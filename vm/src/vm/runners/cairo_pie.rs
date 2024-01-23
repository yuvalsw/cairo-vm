use num_bigint::BigUint;
#[cfg(feature = "std")]
use {
    crate::types::errors::cairo_pie_error::{CairoPieError, DeserializeMemoryError},
    num_integer::Integer,
    serde::de::DeserializeOwned,
    std::fs::File,
    std::io::Write,
    std::io::{Read, Seek},
    std::path::Path,
    zip::read::ZipFile,
    zip::ZipWriter,
};

use super::cairo_runner::ExecutionResources;
use crate::stdlib::prelude::{String, Vec};
use crate::{
    serde::deserialize_program::BuiltinName,
    stdlib::{collections::HashMap, prelude::*},
    types::relocatable::{MaybeRelocatable, Relocatable},
    Felt252,
};
use serde::{Deserialize, Serialize};

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

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct OutputBuiltinAdditionalData {
    pub pages: Pages,
    pub attributes: Attributes,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
#[serde(untagged)]
pub enum BuiltinAdditionalData {
    // Contains verified addresses as contiguous index, value pairs
    #[serde(serialize_with = "serde_impl::serialize_hash_additional_data")]
    Hash(Vec<Relocatable>),
    Output(OutputBuiltinAdditionalData),
    // Signatures are composed of (r, s) tuples
    #[serde(serialize_with = "serde_impl::serialize_signature_additional_data")]
    Signature(HashMap<Relocatable, (Felt252, Felt252)>),
    None,
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPie {
    pub metadata: CairoPieMetadata,
    pub memory: CairoPieMemory,
    pub execution_resources: ExecutionResources,
    pub additional_data: HashMap<String, BuiltinAdditionalData>,
    pub version: CairoPieVersion,
}

#[cfg(feature = "std")]
impl CairoPie {
    const N_SEGMENT_BITS: usize = 16;
    const N_OFFSET_BITS: usize = 47;
    const SEGMENT_MASK: u64 = ((1 << Self::N_SEGMENT_BITS) - 1) << Self::N_OFFSET_BITS;
    const OFFSET_MASK: u64 = (1 << Self::N_OFFSET_BITS) - 1;

    fn parse_zip_file<T: DeserializeOwned>(mut zip_file: ZipFile) -> Result<T, CairoPieError> {
        let mut buf = vec![];
        zip_file.read_to_end(&mut buf)?;
        serde_json::from_slice(&buf).map_err(|e| e.into())
    }

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

        let segment = (value & Self::SEGMENT_MASK) >> Self::N_OFFSET_BITS;
        let offset = value & Self::OFFSET_MASK;
        MaybeRelocatable::RelocatableValue(Relocatable::from((segment as isize, offset as usize)))
    }

    fn read_memory_file<R: Read>(
        mut reader: R,
        addr_size: usize,
        felt_size: usize,
    ) -> Result<CairoPieMemory, DeserializeMemoryError> {
        let memory_cell_size = addr_size + felt_size;
        let mut memory = vec![];
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
            let address = Self::maybe_relocatable_from_le_bytes(address_bytes);
            let value = Self::maybe_relocatable_from_le_bytes(value_bytes);

            match address {
                MaybeRelocatable::RelocatableValue(relocatable) => {
                    memory.push((
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

        Ok(CairoPieMemory(memory))
    }

    /// Builds a CairoPie object from the Python VM ZIP archive format.
    ///
    /// This function expects the ZIP archive to contain the following files:
    /// * metadata.json
    /// * execution_resources.json
    /// * additional_data.json
    /// * version.json
    /// * memory.bin
    ///
    /// This is used to load PIEs to re-execute with the Starknet bootloader.
    #[cfg(feature = "std")]

    pub fn from_zip_archive<R: Read + Seek>(
        mut zip: zip::ZipArchive<R>,
    ) -> Result<Self, CairoPieError> {
        let metadata: CairoPieMetadata = Self::parse_zip_file(zip.by_name("metadata.json")?)?;
        let execution_resources: ExecutionResources =
            Self::parse_zip_file(zip.by_name("execution_resources.json")?)?;
        let additional_data: HashMap<String, BuiltinAdditionalData> =
            Self::parse_zip_file(zip.by_name("additional_data.json")?)?;
        let version: CairoPieVersion = Self::parse_zip_file(zip.by_name("version.json")?)?;

        let addr_size: usize = 8;
        let felt_bytes = {
            let (mut n_bytes, remainder) = metadata.program.prime.bits().div_rem(&8u64);
            if remainder != 0 {
                n_bytes += 1;
            }
            n_bytes as usize
        };
        let memory = Self::read_memory_file(zip.by_name("memory.bin")?, addr_size, felt_bytes)?;

        Ok(Self {
            metadata,
            memory,
            execution_resources,
            additional_data,
            version,
        })
    }

    /// Builds a CairoPie object from an array of bytes.
    #[cfg(feature = "std")]
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CairoPieError> {
        let reader = std::io::Cursor::new(bytes);
        let zip_archive = zip::ZipArchive::new(reader)?;

        Self::from_zip_archive(zip_archive)
    }

    /// Builds a CairoPie object from a ZIP archive.
    #[cfg(feature = "std")]
    pub fn from_file(path: &Path) -> Result<Self, CairoPieError> {
        let file = std::fs::File::open(path)?;
        let zip = zip::ZipArchive::new(file)?;

        Self::from_zip_archive(zip)
    }
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Deserialize))]
pub struct CairoPieMetadata {
    pub program: StrippedProgram,
    pub program_segment: SegmentInfo,
    pub execution_segment: SegmentInfo,
    pub ret_fp_segment: SegmentInfo,
    pub ret_pc_segment: SegmentInfo,
    pub builtin_segments: HashMap<String, SegmentInfo>,
    pub extra_segments: Vec<SegmentInfo>,
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Deserialize))]
pub struct StrippedProgram {
    #[serde(serialize_with = "serde_impl::serialize_program_data")]
    #[cfg_attr(
        feature = "std",
        serde(deserialize_with = "serde_impl::de::deserialize_array_of_felts")
    )]
    pub data: Vec<MaybeRelocatable>,
    pub builtins: Vec<BuiltinName>,
    pub main: usize,
    #[serde(serialize_with = "serde_impl::serialize_prime")]
    #[cfg_attr(
        feature = "std",
        serde(
            deserialize_with = "crate::serde::deserialize_program::deserialize_biguint_from_number"
        )
    )]
    pub prime: BigUint,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CairoPieVersion {
    pub cairo_pie: String,
}

impl CairoPie {
    #[cfg(feature = "std")]
    pub fn write_zip_file(&self, file_path: &Path) -> Result<(), std::io::Error> {
        let file = File::create(file_path)?;
        let mut zip_writer = ZipWriter::new(file);
        let options =
            zip::write::FileOptions::default().compression_method(zip::CompressionMethod::Stored);
        zip_writer.start_file("version.json", options)?;
        zip_writer.write_all(serde_json::to_string(&self.version)?.as_bytes())?;
        zip_writer.start_file("metadata.json", options)?;
        zip_writer.write_all(serde_json::to_string(&self.metadata)?.as_bytes())?;
        zip_writer.start_file("memory.bin", options)?;
        zip_writer.write_all(&self.memory.to_bytes())?;
        zip_writer.start_file("additional_data.json", options)?;
        zip_writer.write_all(serde_json::to_string(&self.additional_data)?.as_bytes())?;
        zip_writer.start_file("execution_resources.json", options)?;
        zip_writer.write_all(serde_json::to_string(&self.execution_resources)?.as_bytes())?;
        zip_writer.finish()?;
        Ok(())
    }
}

mod serde_impl {
    use crate::stdlib::collections::HashMap;
    use num_traits::Num;

    use super::CairoPieMemory;
    use crate::stdlib::prelude::{String, Vec};
    use crate::{
        types::relocatable::{MaybeRelocatable, Relocatable},
        utils::CAIRO_PRIME,
        Felt252,
    };
    use num_bigint::BigUint;
    use serde::{ser::SerializeSeq, Serialize, Serializer};
    use serde_json::Number;

    pub const ADDR_BYTE_LEN: usize = 8;
    pub const FIELD_BYTE_LEN: usize = 32;
    pub const ADDR_BASE: u64 = 0x8000000000000000; // 2 ** (8 * ADDR_BYTE_LEN - 1)
    pub const OFFSET_BASE: u64 = 0x800000000000; // 2 ** OFFSET_BIT_LEN
    pub const RELOCATE_BASE: &str =
        "8000000000000000000000000000000000000000000000000000000000000000"; // 2 ** (8 * FIELD_BYTE_LEN - 1)

    struct Felt252Wrapper<'a>(&'a Felt252);

    impl<'a> Serialize for Felt252Wrapper<'a> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            #[cfg(any(target_arch = "wasm32", no_std, not(feature = "std")))]
            use crate::alloc::string::ToString;

            // Note: This uses an API intended only for testing.
            serde_json::Number::from_string_unchecked(self.0.to_string()).serialize(serializer)
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

    #[allow(clippy::format_collect)]
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

        serializer.serialize_str(
            res.iter()
                .map(|b| format!("{:02x}", b))
                .collect::<String>()
                .as_str(),
        )
    }

    impl CairoPieMemory {
        pub fn new() -> Self {
            Self(vec![])
        }

        pub fn len(&self) -> usize {
            self.0.len()
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

    #[cfg(feature = "std")]

    pub mod de {
        use crate::serde::deserialize_program::felt_from_number;
        use crate::vm::runners::cairo_pie::MaybeRelocatable;
        use serde_json::Number;
        pub(crate) struct MaybeRelocatableNumberVisitor;

        impl<'de> serde::de::Visitor<'de> for MaybeRelocatableNumberVisitor {
            type Value = Vec<MaybeRelocatable>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("Could not deserialize array of hexadecimal")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut data: Vec<MaybeRelocatable> = vec![];

                while let Some(n) = seq.next_element::<Number>()? {
                    let felt = felt_from_number(n.clone()).ok_or(serde::de::Error::custom(
                        format!("Failed to parse number as felt: {n}"),
                    ))?;
                    data.push(MaybeRelocatable::Int(felt));
                }
                Ok(data)
            }
        }

        pub fn deserialize_array_of_felts<'de, D: serde::Deserializer<'de>>(
            d: D,
        ) -> Result<Vec<MaybeRelocatable>, D::Error> {
            d.deserialize_seq(MaybeRelocatableNumberVisitor)
        }
    }

    pub fn serialize_signature_additional_data<S>(
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

    pub fn serialize_hash_additional_data<S>(
        values: &[Relocatable],
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq_serializer = serializer.serialize_seq(Some(values.len()))?;

        for value in values {
            seq_serializer.serialize_element(&[value.segment_index, value.offset as isize])?;
        }

        seq_serializer.end()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[cfg(feature = "std")]
    use {crate::utils::CAIRO_PRIME, rstest::rstest, std::fs::File};

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

    #[cfg(feature = "std")]
    #[rstest]
    #[case(0x8000_0000_0000_0000u64, 0, 0)]
    #[case(0x8010_0000_0000_1000u64, 32, 0x1000)]
    fn test_memory_deserialize_relocatable(
        #[case] value: u64,
        #[case] expected_segment: isize,
        #[case] expected_offset: usize,
    ) {
        let bytes: [u8; 8] = value.to_le_bytes();
        let maybe_relocatable = CairoPie::maybe_relocatable_from_le_bytes(&bytes);

        assert_eq!(
            maybe_relocatable,
            MaybeRelocatable::RelocatableValue(Relocatable {
                segment_index: expected_segment,
                offset: expected_offset
            })
        );
    }

    #[cfg(feature = "std")]
    #[rstest]
    #[case([0, 0, 0, 0, 0, 0, 0], 0)]
    #[case([0, 1, 2, 3, 4, 5, 6], 0x6050403020100)]
    fn test_memory_deserialize_integer(#[case] bytes: [u8; 7], #[case] expected_value: u64) {
        let maybe_relocatable = CairoPie::maybe_relocatable_from_le_bytes(&bytes);

        assert_eq!(
            maybe_relocatable,
            MaybeRelocatable::Int(Felt252::from(expected_value))
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_read_memory_file() {
        let path = Path::new("../cairo_programs/manually_compiled/fibonacci_cairo_pie/memory.bin");
        let file = File::open(path).unwrap();

        let memory = CairoPie::read_memory_file(file, 8, 32).expect("Could not read memory file");
        assert_eq!(memory.0.len(), 88);
    }

    #[cfg(feature = "std")]
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
                    pages: Default::default(),
                    attributes: Default::default(),
                })
            )])
        );

        assert_eq!(cairo_pie.version.cairo_pie, CAIRO_PIE_VERSION);
    }
}
