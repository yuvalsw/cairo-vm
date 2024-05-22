use num_bigint::BigUint;
use num_integer::Integer;
use std::io::{Read, Seek};

use serde::de::DeserializeOwned;
use zip::read::ZipFile;

use super::cairo_runner::ExecutionResources;
use crate::serde::deserialize_utils::deserialize_biguint_from_number;
use crate::stdlib::prelude::{String, Vec};
use crate::types::builtin_name::BuiltinName;
use crate::types::errors::cairo_pie_error::{CairoPieError, DeserializeMemoryError};
use crate::vm::errors::cairo_pie_errors::CairoPieValidationError;
use crate::{
    stdlib::{collections::HashMap, prelude::*},
    types::relocatable::{MaybeRelocatable, Relocatable},
    Felt252,
};
use num_traits::{One, Zero};
use serde::{Deserialize, Deserializer, Serialize};
#[cfg(feature = "std")]
use {
    std::{fs::File, io::Write, path::Path},
    zip::ZipWriter,
};

pub const CAIRO_PIE_VERSION: &str = "1.1";

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct SegmentInfo {
    pub index: isize,
    pub size: usize,
}

impl From<(isize, usize)> for SegmentInfo {
    fn from(value: (isize, usize)) -> Self {
        SegmentInfo {
            index: value.0,
            size: value.1,
        }
    }
}

// A simplified version of Memory, without any additional data besides its elements
// Contains all addr-value pairs, ordered by index and offset
// Allows practical serialization + conversion between CairoPieMemory & Memory
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPieMemory(
    #[serde(serialize_with = "serde_impl::serialize_memory")]
    pub  Vec<((usize, usize), MaybeRelocatable)>,
);

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct PublicMemoryPage {
    pub start: usize,
    pub size: usize,
}

// HashMap value based on starknet/core/os/output.cairo usage
pub type Attributes = HashMap<String, Vec<usize>>;
pub type Pages = HashMap<usize, PublicMemoryPage>;

impl From<&std::vec::Vec<usize>> for PublicMemoryPage {
    fn from(vec: &std::vec::Vec<usize>) -> Self {
        Self {
            start: vec[0],
            size: vec[1],
        }
    }
}

fn pages_from_vec<'de, D>(deserializer: D) -> Result<Pages, D::Error>
where
    D: Deserializer<'de>,
{
    Ok(HashMap::<String, Vec<usize>>::deserialize(deserializer)?
        .iter()
        .map(|(k, v)| (k.parse::<usize>().unwrap(), PublicMemoryPage::from(v)))
        .collect())
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct OutputBuiltinAdditionalData {
    #[serde(skip)]
    pub base: usize,
    #[serde(deserialize_with = "pages_from_vec")]
    pub pages: Pages,
    pub attributes: Attributes,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
#[serde(untagged)]
pub enum BuiltinAdditionalData {
    // Contains verified addresses as contiguous index, value pairs
    #[serde(with = "serde_impl::hash_additional_data")]
    Hash(Vec<Relocatable>),
    Output(OutputBuiltinAdditionalData),
    // Signatures are composed of (r, s) tuples
    #[serde(with = "serde_impl::signature_additional_data")]
    Signature(HashMap<Relocatable, (Felt252, Felt252)>),
    None,
    RangeCheck(Option<u32>),
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPieAdditionalData(
    #[serde(with = "crate::types::builtin_name::serde_generic_map_impl")]
    pub  HashMap<BuiltinName, BuiltinAdditionalData>,
);

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPie {
    pub metadata: CairoPieMetadata,
    pub memory: CairoPieMemory,
    pub execution_resources: ExecutionResources,
    pub additional_data: CairoPieAdditionalData,
    pub version: CairoPieVersion,
}

fn parse_zip_file<T: DeserializeOwned>(mut zip_file: ZipFile) -> Result<T, CairoPieError> {
    let mut buf = vec![];
    zip_file.read_to_end(&mut buf)?;
    serde_json::from_slice(&buf).map_err(|e| e.into())
}

const N_SEGMENT_BITS: usize = 16;
const N_OFFSET_BITS: usize = 47;
const SEGMENT_MASK: u64 = ((1 << N_SEGMENT_BITS) - 1) << N_OFFSET_BITS;
const OFFSET_MASK: u64 = (1 << N_OFFSET_BITS) - 1;

fn maybe_relocatable_from_le_bytes(bytes: &[u8]) -> MaybeRelocatable {
    // Little-endian -> the relocatable bit is in the last element
    let is_relocatable = (bytes[bytes.len() - 1] & 0x80) != 0;

    if !is_relocatable {
        let felt = Felt252::from_bytes_le_slice(bytes);
        return MaybeRelocatable::Int(felt);
    }

    // Relocatable values are guaranteed to fit in a u64
    let value = {
        let mut value = 0;
        for (index, byte) in bytes[..8].iter().enumerate() {
            value += u64::from(*byte) << (index * 8);
        }
        value
    };

    let segment = (value & SEGMENT_MASK) >> N_OFFSET_BITS;
    let offset = value & OFFSET_MASK;
    MaybeRelocatable::RelocatableValue(Relocatable::from((segment as isize, offset as usize)))
}

fn read_memory_file<R: Read>(
    mut reader: R,
    addr_size: usize,
    felt_size: usize,
) -> Result<CairoPieMemory, DeserializeMemoryError> {
    let memory_cell_size = addr_size + felt_size;
    let mut memory = CairoPieMemory::new();
    let mut pos: usize = 0;

    loop {
        let mut element = vec![0; memory_cell_size];
        match reader.read(&mut element) {
            Ok(n) => {
                if n == 0 {
                    break;
                }
                if n != memory_cell_size {
                    return Err(DeserializeMemoryError::UnexpectedEof);
                }
            }
            Err(e) => return Err(e.into()),
        }
        let (address_bytes, value_bytes) = element.split_at(addr_size);
        let address = maybe_relocatable_from_le_bytes(address_bytes);
        let value = maybe_relocatable_from_le_bytes(value_bytes);

        match address {
            MaybeRelocatable::RelocatableValue(relocatable) => {
                memory.0.push((
                    (relocatable.segment_index as usize, relocatable.offset),
                    value,
                ));
            }
            MaybeRelocatable::Int(_value) => {
                return Err(DeserializeMemoryError::AddressIsNotRelocatable(pos));
            }
        }
        pos += memory_cell_size;
    }

    Ok(memory)
}

impl CairoPie {
    #[cfg(feature = "std")]
    pub fn from_zip_archive<R: Read + Seek>(
        mut zip: zip::ZipArchive<R>,
    ) -> Result<CairoPie, CairoPieError> {
        let metadata: CairoPieMetadata = parse_zip_file(zip.by_name("metadata.json")?)?;
        let execution_resources: ExecutionResources =
            parse_zip_file(zip.by_name("execution_resources.json")?)?;
        let additional_data =
            CairoPieAdditionalData(parse_zip_file(zip.by_name("additional_data.json")?)?);
        let version: CairoPieVersion = parse_zip_file(zip.by_name("version.json")?)?;

        let addr_size: usize = 8;
        let felt_bytes = {
            let (mut n_bytes, remainder) = metadata.program.prime.bits().div_rem(&8u64);
            if remainder != 0 {
                n_bytes += 1;
            }
            n_bytes as usize
        };
        let memory = read_memory_file(zip.by_name("memory.bin")?, addr_size, felt_bytes)?;

        Ok(CairoPie {
            metadata,
            memory,
            execution_resources,
            additional_data,
            version,
        })
    }

    #[cfg(feature = "std")]
    pub fn from_file(path: &Path) -> Result<CairoPie, CairoPieError> {
        let file = std::fs::File::open(path)?;
        let zip = zip::ZipArchive::new(file)?;

        CairoPie::from_zip_archive(zip)
    }
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPieMetadata {
    pub program: StrippedProgram,
    pub program_segment: SegmentInfo,
    pub execution_segment: SegmentInfo,
    pub ret_fp_segment: SegmentInfo,
    pub ret_pc_segment: SegmentInfo,
    #[serde(serialize_with = "serde_impl::serialize_builtin_segments")]
    pub builtin_segments: HashMap<BuiltinName, SegmentInfo>,
    pub extra_segments: Vec<SegmentInfo>,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct StrippedProgram {
    #[serde(serialize_with = "serde_impl::serialize_program_data")]
    #[serde(deserialize_with = "serde_impl::deserialize_array_of_felts")]
    pub data: Vec<MaybeRelocatable>,
    pub builtins: Vec<BuiltinName>,
    pub main: usize,
    #[serde(deserialize_with = "deserialize_biguint_from_number")]
    #[serde(serialize_with = "serde_impl::serialize_prime")]
    pub prime: BigUint,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPieVersion {
    pub cairo_pie: String,
}

impl CairoPieMetadata {
    pub(crate) fn run_validity_checks(&self) -> Result<(), CairoPieValidationError> {
        if self.program.main > self.program.data.len() {
            return Err(CairoPieValidationError::InvalidMainAddress);
        }
        if self.program.data.len() != self.program_segment.size {
            return Err(CairoPieValidationError::ProgramLenVsSegmentSizeMismatch);
        }
        if self.builtin_segments.len() != self.program.builtins.len()
            || !self
                .program
                .builtins
                .iter()
                .all(|b| self.builtin_segments.contains_key(b))
        {
            return Err(CairoPieValidationError::BuiltinListVsSegmentsMismatch);
        }
        if !self.ret_fp_segment.size.is_zero() {
            return Err(CairoPieValidationError::InvalidRetFpSegmentSize);
        }
        if !self.ret_pc_segment.size.is_zero() {
            return Err(CairoPieValidationError::InvalidRetPcSegmentSize);
        }
        self.validate_segment_order()
    }

    fn validate_segment_order(&self) -> Result<(), CairoPieValidationError> {
        if !self.program_segment.index.is_zero() {
            return Err(CairoPieValidationError::InvalidProgramSegmentIndex);
        }
        if !self.execution_segment.index.is_one() {
            return Err(CairoPieValidationError::InvalidExecutionSegmentIndex);
        }
        for (i, builtin_name) in self.program.builtins.iter().enumerate() {
            // We can safely index as run_validity_checks already ensures that the keys match
            if self.builtin_segments[builtin_name].index != 2 + i as isize {
                return Err(CairoPieValidationError::InvalidBuiltinSegmentIndex(
                    *builtin_name,
                ));
            }
        }
        let n_builtins = self.program.builtins.len() as isize;
        if self.ret_fp_segment.index != n_builtins + 2 {
            return Err(CairoPieValidationError::InvalidRetFpSegmentIndex);
        }
        if self.ret_pc_segment.index != n_builtins + 3 {
            return Err(CairoPieValidationError::InvalidRetPcSegmentIndex);
        }
        for (i, segment) in self.extra_segments.iter().enumerate() {
            if segment.index != 4 + n_builtins + i as isize {
                return Err(CairoPieValidationError::InvalidExtraSegmentIndex);
            }
        }
        Ok(())
    }
}

impl CairoPie {
    /// Check that self is a valid Cairo PIE
    pub fn run_validity_checks(&self) -> Result<(), CairoPieValidationError> {
        self.metadata.run_validity_checks()?;
        self.run_memory_validity_checks()?;
        if self.execution_resources.builtin_instance_counter.len()
            != self.metadata.program.builtins.len()
            || !self.metadata.program.builtins.iter().all(|b| {
                self.execution_resources
                    .builtin_instance_counter
                    .contains_key(b)
            })
        {
            return Err(CairoPieValidationError::BuiltinListVsSegmentsMismatch);
        }
        Ok(())
    }

    fn run_memory_validity_checks(&self) -> Result<(), CairoPieValidationError> {
        let mut segment_sizes = vec![
            &self.metadata.program_segment,
            &self.metadata.execution_segment,
            &self.metadata.ret_fp_segment,
            &self.metadata.ret_pc_segment,
        ];
        segment_sizes.extend(self.metadata.builtin_segments.values());
        segment_sizes.extend(self.metadata.extra_segments.iter());
        let segment_sizes: HashMap<isize, usize> =
            HashMap::from_iter(segment_sizes.iter().map(|si| (si.index, si.size)));

        let validate_addr = |addr: Relocatable| -> Result<(), CairoPieValidationError> {
            if !segment_sizes
                .get(&addr.segment_index)
                .is_some_and(|size| addr.offset <= *size)
            {
                return Err(CairoPieValidationError::InvalidAddress);
            }
            Ok(())
        };

        for ((si, so), value) in self.memory.0.iter() {
            validate_addr((*si as isize, *so).into())?;
            if let MaybeRelocatable::RelocatableValue(val) = value {
                validate_addr(*val)?;
            }
        }
        Ok(())
    }

    /// Checks that the pie received is identical to self, skipping the fields execution_resources.n_steps, and additional_data[pedersen]
    /// Stricter runs check more Pedersen addresses leading to different address lists
    pub fn check_pie_compatibility(&self, pie: &CairoPie) -> Result<(), CairoPieValidationError> {
        if self.metadata != pie.metadata {
            return Err(CairoPieValidationError::DiffMetadata);
        }
        let mut self_mem = self.memory.0.clone();
        let mut pie_mem = pie.memory.0.clone();
        self_mem.sort();
        pie_mem.sort();
        if self_mem != pie_mem {
            for (x, y) in std::iter::zip(self_mem.iter(), pie_mem.iter()) {
                if x != y {
                    println!("Diff found: {:?}, {:?}", x, y);
                }
            }
            return Err(CairoPieValidationError::DiffMemory);
        }
        if self.execution_resources.n_steps != pie.execution_resources.n_steps
            || self.execution_resources.builtin_instance_counter
                != pie.execution_resources.builtin_instance_counter
        {
            return Err(CairoPieValidationError::DiffExecutionResources);
        }
        if self.additional_data.0.len() != pie.additional_data.0.len() {
            return Err(CairoPieValidationError::DiffAdditionalData);
        }
        for (name, data) in self.additional_data.0.iter() {
            if BuiltinName::output == *name {
                continue;
            }
            if !pie.additional_data.0.get(name).is_some_and(|d| d == data) {
                println!("Our Data: {:?}", data);
                println!("Pie Data: {:?}", pie.additional_data.0.get(name).unwrap());
                return Err(CairoPieValidationError::DiffAdditionalDataForBuiltin(*name));
            }
        }
        Ok(())
    }

    #[cfg(feature = "std")]
    pub fn write_zip_file(&self, file_path: &Path) -> Result<(), std::io::Error> {
        let file = File::create(file_path)?;
        let mut zip_writer = ZipWriter::new(file);
        let options =
            zip::write::FileOptions::default().compression_method(zip::CompressionMethod::Deflated);
        zip_writer.start_file("version.json", options)?;
        serde_json::to_writer(&mut zip_writer, &self.version)?;
        zip_writer.start_file("metadata.json", options)?;
        serde_json::to_writer(&mut zip_writer, &self.metadata)?;
        zip_writer.start_file("memory.bin", options)?;
        zip_writer.write_all(&self.memory.to_bytes())?;
        zip_writer.start_file("additional_data.json", options)?;
        serde_json::to_writer(&mut zip_writer, &self.additional_data)?;
        zip_writer.start_file("execution_resources.json", options)?;
        serde_json::to_writer(&mut zip_writer, &self.execution_resources)?;
        zip_writer.finish()?;
        Ok(())
    }

    #[cfg(feature = "std")]
    pub fn read_zip_file(file_path: &Path) -> Result<CairoPie, std::io::Error> {
        use zip::ZipArchive;

        let file = File::open(file_path)?;
        let mut zip_reader = ZipArchive::new(file)?;

        let reader = std::io::BufReader::new(zip_reader.by_name("version.json")?);
        let version: CairoPieVersion = serde_json::from_reader(reader)?;

        let reader = std::io::BufReader::new(zip_reader.by_name("metadata.json")?);
        let metadata: CairoPieMetadata = serde_json::from_reader(reader)?;

        let mut memory = vec![];
        zip_reader.by_name("memory.bin")?.read_to_end(&mut memory)?;
        let memory = CairoPieMemory::from_bytes(&memory)
            .ok_or_else(|| std::io::Error::from(std::io::ErrorKind::InvalidData))?;

        let reader = std::io::BufReader::new(zip_reader.by_name("execution_resources.json")?);
        let execution_resources: ExecutionResources = serde_json::from_reader(reader)?;

        let reader = std::io::BufReader::new(zip_reader.by_name("additional_data.json")?);
        let additional_data: CairoPieAdditionalData = serde_json::from_reader(reader)?;

        Ok(CairoPie {
            metadata,
            memory,
            execution_resources,
            additional_data,
            version,
        })
    }
}

pub(super) mod serde_impl {
    use crate::stdlib::collections::HashMap;
    use crate::types::builtin_name::BuiltinName;
    use num_integer::Integer;
    use num_traits::Num;

    use super::{CairoPieMemory, SegmentInfo};
    #[cfg(any(target_arch = "wasm32", no_std, not(feature = "std")))]
    use crate::alloc::string::ToString;
    use crate::stdlib::prelude::{String, Vec};
    use crate::{
        types::relocatable::{MaybeRelocatable, Relocatable},
        Felt252,
    };
    use num_bigint::BigUint;
    use serde::de::SeqAccess;
    use serde::{de, ser::SerializeSeq, Deserializer, Serialize, Serializer};
    use serde_json::Number;
    use std::fmt;

    use crate::serde::deserialize_utils::felt_from_number;

    use crate::utils::CAIRO_PRIME;

    pub const ADDR_BYTE_LEN: usize = 8;
    pub const FIELD_BYTE_LEN: usize = 32;
    pub const ADDR_BASE: u64 = 0x8000000000000000;
    // 2 ** (8 * ADDR_BYTE_LEN - 1)
    pub const OFFSET_BASE: u64 = 0x800000000000;
    // 2 ** OFFSET_BIT_LEN
    use serde::{de::Error, ser::SerializeMap, Deserialize};

    pub const CELL_BYTE_LEN: usize = ADDR_BYTE_LEN + FIELD_BYTE_LEN;
    pub const RELOCATE_BASE: &str =
        "8000000000000000000000000000000000000000000000000000000000000000"; // 2 ** (8 * FIELD_BYTE_LEN - 1)

    pub(crate) struct Felt252Wrapper<'a>(&'a Felt252);

    impl<'a> Serialize for Felt252Wrapper<'a> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            // Note: This uses an API intended only for testing.
            serde_json::Number::from_string_unchecked(self.0.to_string()).serialize(serializer)
        }
    }

    pub mod version {}

    pub mod program_data {}

    pub mod prime {
        use super::*;

        use lazy_static::lazy_static;
        lazy_static! {
            static ref CAIRO_PRIME_NUMBER: Number =
                Number::from_string_unchecked(CAIRO_PRIME.to_string());
        }
    }

    pub fn serialize_program_data<S>(
        values: &[MaybeRelocatable],
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq_serializer = serializer.serialize_seq(Some(values.len()))?;

        for value in values {
            match value {
                MaybeRelocatable::RelocatableValue(_) => todo!(),
                MaybeRelocatable::Int(x) => {
                    seq_serializer.serialize_element(&Felt252Wrapper(x))?;
                }
            };
        }

        seq_serializer.end()
    }

    pub fn serialize_memory<S>(
        values: &[((usize, usize), MaybeRelocatable)],
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Missing segment and memory holes can be ignored
        // as they can be inferred by the address on the prover side
        let mem_cap = values.len() * ADDR_BYTE_LEN + values.len() * FIELD_BYTE_LEN;
        let mut res = Vec::with_capacity(mem_cap);

        for ((segment, offset), value) in values.iter() {
            let mem_addr = ADDR_BASE + *segment as u64 * OFFSET_BASE + *offset as u64;
            res.extend_from_slice(mem_addr.to_le_bytes().as_ref());
            match value {
                // Serializes RelocatableValue(little endian):
                // 1bit |   SEGMENT_BITS |   OFFSET_BITS
                // 1    |     segment    |   offset
                MaybeRelocatable::RelocatableValue(rel_val) => {
                    let reloc_base = BigUint::from_str_radix(RELOCATE_BASE, 16)
                        .map_err(|_| serde::ser::Error::custom("invalid relocation base str"))?;
                    let reloc_value = reloc_base
                        + BigUint::from(rel_val.segment_index as usize)
                            * BigUint::from(OFFSET_BASE)
                        + BigUint::from(rel_val.offset);
                    res.extend_from_slice(reloc_value.to_bytes_le().as_ref());
                }
                // Serializes Int(little endian):
                // 1bit | Num
                // 0    | num
                MaybeRelocatable::Int(data_val) => {
                    res.extend_from_slice(data_val.to_bytes_le().as_ref());
                }
            };
        }

        let string = res
            .iter()
            .fold(String::new(), |string, b| string + &format!("{:02x}", b));

        serializer.serialize_str(&string)
    }

    impl CairoPieMemory {
        pub fn new() -> Self {
            Self(vec![])
        }

        pub fn len(&self) -> usize {
            self.0.len()
        }

        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        pub fn to_bytes(&self) -> Vec<u8> {
            // Missing segment and memory holes can be ignored
            // as they can be inferred by the address on the prover side
            let values = &self.0;
            let mem_cap = values.len() * ADDR_BYTE_LEN + values.len() * FIELD_BYTE_LEN;
            let mut res = Vec::with_capacity(mem_cap);

            for ((segment, offset), value) in values.iter() {
                let mem_addr = ADDR_BASE + *segment as u64 * OFFSET_BASE + *offset as u64;
                res.extend_from_slice(mem_addr.to_le_bytes().as_ref());
                match value {
                    // Serializes RelocatableValue(little endian):
                    // 1bit |   SEGMENT_BITS |   OFFSET_BITS
                    // 1    |     segment    |   offset
                    MaybeRelocatable::RelocatableValue(rel_val) => {
                        let reloc_base = BigUint::from_str_radix(RELOCATE_BASE, 16).unwrap();
                        let reloc_value = reloc_base
                            + BigUint::from(rel_val.segment_index as usize)
                                * BigUint::from(OFFSET_BASE)
                            + BigUint::from(rel_val.offset);
                        res.extend_from_slice(reloc_value.to_bytes_le().as_ref());
                    }
                    // Serializes Int(little endian):
                    // 1bit | Num
                    // 0    | num
                    MaybeRelocatable::Int(data_val) => {
                        res.extend_from_slice(data_val.to_bytes_le().as_ref());
                    }
                };
            }
            res
        }

        pub fn from_bytes(bytes: &[u8]) -> Option<CairoPieMemory> {
            if !bytes.len().is_multiple_of(&CELL_BYTE_LEN) {
                return None;
            }

            let relocatable_from_bytes = |bytes: [u8; 8]| -> (usize, usize) {
                const N_SEGMENT_BITS: usize = 16;
                const N_OFFSET_BITS: usize = 47;
                const SEGMENT_MASK: u64 = ((1 << N_SEGMENT_BITS) - 1) << N_OFFSET_BITS;
                const OFFSET_MASK: u64 = (1 << N_OFFSET_BITS) - 1;

                let addr = u64::from_le_bytes(bytes);
                let segment = (addr & SEGMENT_MASK) >> N_OFFSET_BITS;
                let offset = addr & OFFSET_MASK;
                (segment as usize, offset as usize)
            };

            let mut res = vec![];
            for cell_bytes in bytes.chunks(CELL_BYTE_LEN) {
                let addr = relocatable_from_bytes(cell_bytes[0..ADDR_BYTE_LEN].try_into().ok()?);
                let field_bytes = &cell_bytes[ADDR_BYTE_LEN..CELL_BYTE_LEN];
                // Check the last bit to determine if it is a Relocatable or Felt value
                let value = if (field_bytes[field_bytes.len() - 1] & 0x80) != 0 {
                    let (segment, offset) =
                        relocatable_from_bytes(field_bytes[0..ADDR_BYTE_LEN].try_into().ok()?);
                    MaybeRelocatable::from((segment as isize, offset))
                } else {
                    MaybeRelocatable::from(Felt252::from_bytes_le_slice(field_bytes))
                };
                res.push((addr, value));
            }

            Some(CairoPieMemory(res))
        }
    }

    pub fn serialize_prime<S>(_value: &BigUint, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[cfg(any(target_arch = "wasm32", no_std, not(feature = "std")))]
        use crate::alloc::string::ToString;

        // Note: This uses an API intended only for testing.
        Number::from_string_unchecked(CAIRO_PRIME.to_string()).serialize(serializer)
    }

    pub(crate) struct MaybeRelocatableNumberVisitor;

    impl<'de> de::Visitor<'de> for MaybeRelocatableNumberVisitor {
        type Value = Vec<MaybeRelocatable>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("Could not deserialize array of hexadecimal")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut data: Vec<MaybeRelocatable> = vec![];

            while let Some(n) = seq.next_element::<Number>()? {
                let felt = felt_from_number(n.clone()).ok_or(de::Error::custom(format!(
                    "Failed to parse number as felt: {n}"
                )))?;
                data.push(MaybeRelocatable::Int(felt));
            }
            Ok(data)
        }
    }

    pub fn deserialize_array_of_felts<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<Vec<MaybeRelocatable>, D::Error> {
        d.deserialize_seq(MaybeRelocatableNumberVisitor)
    }

    pub mod signature_additional_data {
        use super::*;

        pub fn serialize<S>(
            values: &HashMap<Relocatable, (Felt252, Felt252)>,
            serializer: S,
        ) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut seq_serializer = serializer.serialize_seq(Some(values.len()))?;

            for (key, (x, y)) in values {
                seq_serializer.serialize_element(&[
                    [
                        Felt252Wrapper(&Felt252::from(key.segment_index)),
                        Felt252Wrapper(&Felt252::from(key.offset)),
                    ],
                    [Felt252Wrapper(x), Felt252Wrapper(y)],
                ])?;
            }
            seq_serializer.end()
        }

        pub fn deserialize<'de, D>(
            d: D,
        ) -> Result<HashMap<Relocatable, (Felt252, Felt252)>, D::Error>
        where
            D: Deserializer<'de>,
        {
            let number_map = Vec::<((Number, Number), (Number, Number))>::deserialize(d)?;
            let mut res = HashMap::with_capacity(number_map.len());
            for ((index, offset), (r, s)) in number_map.into_iter() {
                let addr = Relocatable::from((
                    index
                        .as_u64()
                        .ok_or_else(|| D::Error::custom("Invalid address"))?
                        as isize,
                    offset
                        .as_u64()
                        .ok_or_else(|| D::Error::custom("Invalid address"))?
                        as usize,
                ));
                let r = Felt252::from_dec_str(r.as_str())
                    .map_err(|_| D::Error::custom("Invalid Felt252 value"))?;
                let s = Felt252::from_dec_str(s.as_str())
                    .map_err(|_| D::Error::custom("Invalid Felt252 value"))?;
                res.insert(addr, (r, s));
            }
            Ok(res)
        }
    }

    pub mod hash_additional_data {
        use super::*;

        pub fn serialize<S>(values: &[Relocatable], serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut seq_serializer: <S as Serializer>::SerializeSeq =
                serializer.serialize_seq(Some(values.len()))?;

            for value in values {
                seq_serializer.serialize_element(&[value.segment_index, value.offset as isize])?;
            }

            seq_serializer.end()
        }

        pub fn deserialize<'de, D>(d: D) -> Result<Vec<Relocatable>, D::Error>
        where
            D: Deserializer<'de>,
        {
            let tuples = Vec::<(usize, usize)>::deserialize(d)?;
            Ok(tuples
                .into_iter()
                .map(|(x, y)| Relocatable::from((x as isize, y)))
                .collect())
        }
    }

    pub fn serialize_builtin_segments<S>(
        values: &HashMap<BuiltinName, SegmentInfo>,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map_serializer = serializer.serialize_map(Some(values.len()))?;
        const BUILTIN_ORDERED_LIST: &[BuiltinName] = &[
            BuiltinName::output,
            BuiltinName::pedersen,
            BuiltinName::range_check,
            BuiltinName::ecdsa,
            BuiltinName::bitwise,
            BuiltinName::ec_op,
            BuiltinName::keccak,
            BuiltinName::poseidon,
        ];

        for name in BUILTIN_ORDERED_LIST {
            if let Some(info) = values.get(name) {
                map_serializer.serialize_entry(name, info)?
            }
        }
        map_serializer.end()
    }
}

#[cfg(test)]
mod test {
    #[cfg(feature = "std")]
    use rstest::rstest;

    use super::*;
    use crate::utils::CAIRO_PRIME;
    use rstest::rstest;
    use std::fs::File;

    #[test]
    fn serialize_cairo_pie_memory() {
        let addrs = [
            ((1, 0), "0000000000800080"),
            ((1, 1), "0100000000800080"),
            ((1, 4), "0400000000800080"),
            ((1, 8), "0800000000800080"),
            ((2, 0), "0000000000000180"),
            ((5, 8), "0800000000800280"),
        ];

        let memory = CairoPieMemory(vec![
            (addrs[0].0, MaybeRelocatable::Int(1234.into())),
            (addrs[1].0, MaybeRelocatable::Int(11.into())),
            (addrs[2].0, MaybeRelocatable::Int(12.into())),
            (
                addrs[3].0,
                MaybeRelocatable::RelocatableValue((1, 2).into()),
            ),
            (
                addrs[4].0,
                MaybeRelocatable::RelocatableValue((3, 4).into()),
            ),
            (
                addrs[5].0,
                MaybeRelocatable::RelocatableValue((5, 6).into()),
            ),
        ]);

        let mem = serde_json::to_value(memory).unwrap();
        let mem_str = mem.as_str().unwrap();
        let shift_len = (serde_impl::ADDR_BYTE_LEN + serde_impl::FIELD_BYTE_LEN) * 2;
        let shift_field = serde_impl::FIELD_BYTE_LEN * 2;
        let shift_addr = serde_impl::ADDR_BYTE_LEN * 2;

        // Serializes Address 8 Byte(little endian):
        for (i, expected_addr) in addrs.into_iter().enumerate() {
            let shift = shift_len * i;
            assert_eq!(
                &mem_str[shift..shift + shift_addr],
                expected_addr.1,
                "addr mismatch({i}): {mem_str:?}",
            );
        }

        // Serializes Int(little endian):
        // 1bit | Num
        // 0    | num
        assert_eq!(
            &mem_str[shift_addr..shift_addr + shift_field],
            "d204000000000000000000000000000000000000000000000000000000000000",
            "value mismatch: {mem_str:?}",
        );
        // Serializes RelocatableValue(little endian):
        // 1bit |   SEGMENT_BITS |   OFFSET_BITS
        // 1    |     segment    |   offset
        let shift_first_relocatable = shift_len * 3 + shift_addr;
        assert_eq!(
            &mem_str[shift_first_relocatable..shift_first_relocatable + shift_field],
            "0200000000800000000000000000000000000000000000000000000000000080",
            "value mismatch: {mem_str:?}",
        );
    }

    #[rstest]
    #[case(0x8000_0000_0000_0000u64, 0, 0)]
    #[case(0x8010_0000_0000_1000u64, 32, 0x1000)]
    fn test_memory_deserialize_relocatable(
        #[case] value: u64,
        #[case] expected_segment: isize,
        #[case] expected_offset: usize,
    ) {
        let bytes: [u8; 8] = value.to_le_bytes();
        let maybe_relocatable = maybe_relocatable_from_le_bytes(&bytes);

        assert_eq!(
            maybe_relocatable,
            MaybeRelocatable::RelocatableValue(Relocatable {
                segment_index: expected_segment,
                offset: expected_offset,
            })
        );
    }

    #[rstest]
    #[case([0, 0, 0, 0, 0, 0, 0], 0)]
    #[case([0, 1, 2, 3, 4, 5, 6], 0x6050403020100)]
    fn test_memory_deserialize_integer(#[case] bytes: [u8; 7], #[case] expected_value: u64) {
        let maybe_relocatable = maybe_relocatable_from_le_bytes(&bytes);

        assert_eq!(
            maybe_relocatable,
            MaybeRelocatable::Int(Felt252::from(expected_value))
        );
    }

    #[test]
    fn test_read_memory_file() {
        let path = Path::new("../cairo_programs/manually_compiled/fibonacci_cairo_pie/memory.bin");
        let file = File::open(path).unwrap();

        let memory = read_memory_file(file, 8, 32).expect("Could not read memory file");
        assert_eq!(memory.len(), 88);
    }

    #[test]
    fn test_cairo_pie_from_file() {
        let path =
            Path::new("../cairo_programs/manually_compiled/fibonacci_cairo_pie/fibonacci_pie.zip");

        let cairo_pie = CairoPie::from_file(path).expect("Could not read CairoPie zip file");
        assert_eq!(cairo_pie.metadata.program.prime, CAIRO_PRIME.clone());
        assert_eq!(
            cairo_pie.metadata.program.builtins,
            vec![BuiltinName::output]
        );
        assert_eq!(
            cairo_pie.metadata.program_segment,
            SegmentInfo::from((0, 25))
        );
        assert_eq!(
            cairo_pie.metadata.execution_segment,
            SegmentInfo::from((1, 61))
        );
        assert_eq!(cairo_pie.metadata.ret_fp_segment, SegmentInfo::from((3, 0)));
        assert_eq!(cairo_pie.metadata.ret_pc_segment, SegmentInfo::from((4, 0)));
        assert_eq!(
            cairo_pie.metadata.builtin_segments,
            HashMap::from([("output".to_string(), SegmentInfo::from((2, 2)))])
        );
        assert_eq!(cairo_pie.metadata.extra_segments, vec![]);

        assert_eq!(cairo_pie.execution_resources.n_steps, 72);
        assert_eq!(cairo_pie.execution_resources.n_memory_holes, 0);
        assert_eq!(
            cairo_pie.execution_resources.builtin_instance_counter,
            HashMap::from([("output_builtin".to_string(), 2)])
        );

        assert_eq!(cairo_pie.memory.len(), 88);
        // Check a few values
        assert_eq!(
            cairo_pie.memory.0[0],
            (
                (0usize, 0usize),
                MaybeRelocatable::Int(Felt252::from(290341444919459839u64))
            )
        );
        assert_eq!(
            cairo_pie.memory.0[cairo_pie.memory.len() - 1],
            (
                (1usize, 60usize),
                MaybeRelocatable::RelocatableValue(Relocatable::from((2, 2)))
            )
        );

        assert_eq!(
            cairo_pie.additional_data,
            HashMap::from([(
                "output_builtin".to_string(),
                BuiltinAdditionalData::Output(OutputBuiltinAdditionalData {
                    base: 0,
                    pages: Default::default(),
                    attributes: Default::default(),
                })
            )])
        );

        assert_eq!(cairo_pie.version.cairo_pie, CAIRO_PIE_VERSION);
    }

    #[cfg(feature = "std")]
    #[case(include_bytes!("../../../../cairo_programs/fibonacci.json"), "fibonacci")]
    #[case(include_bytes!("../../../../cairo_programs/integration.json"), "integration")]
    #[case(include_bytes!("../../../../cairo_programs/common_signature.json"), "signature")]
    #[case(include_bytes!("../../../../cairo_programs/relocate_segments.json"), "relocate")]
    #[case(include_bytes!("../../../../cairo_programs/ec_op.json"), "ec_op")]
    #[case(include_bytes!("../../../../cairo_programs/bitwise_output.json"), "bitwise")]
    fn read_write_pie_zip(#[case] program_content: &[u8], #[case] identifier: &str) {
        use crate::{
            cairo_run::CairoRunConfig,
            hint_processor::builtin_hint_processor::builtin_hint_processor_definition::BuiltinHintProcessor,
            types::layout_name::LayoutName,
        };
        // Run a program to obtain the CairoPie
        let cairo_pie = {
            let cairo_run_config = CairoRunConfig {
                layout: LayoutName::starknet_with_keccak,
                ..Default::default()
            };
            let (runner, vm) = crate::cairo_run::cairo_run(
                program_content,
                &cairo_run_config,
                &mut BuiltinHintProcessor::new_empty(),
            )
            .unwrap();
            runner.get_cairo_pie(&vm).unwrap()
        };
        // Serialize the CairoPie into a zip file
        let filename = format!("temp_file_{}", identifier); // Identifier used to avoid name clashes
        let file_path = Path::new(&filename);
        cairo_pie.write_zip_file(file_path).unwrap();
        // Deserialize the zip file
        let deserialized_pie = CairoPie::read_zip_file(file_path).unwrap();
        // Check that both pies are equal
        assert_eq!(cairo_pie, deserialized_pie);
        // Remove zip file created by the test
        std::fs::remove_file(file_path).unwrap();
    }
}
