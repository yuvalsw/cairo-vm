use crate::types::layout_name::LayoutName;

use super::instance_definitions::{
    builtins_instance_def::BuiltinsInstanceDef, diluted_pool_instance_def::DilutedPoolInstanceDef,
};

pub(crate) const MEMORY_UNITS_PER_STEP: u32 = 8;

use serde::Serialize;

#[derive(Serialize, Debug)]
pub struct CairoLayout {
    pub(crate) name: LayoutName,
    pub(crate) rc_units: u32,
    pub(crate) builtins: BuiltinsInstanceDef,
    pub(crate) public_memory_fraction: u32,
    pub(crate) diluted_pool_instance_def: Option<DilutedPoolInstanceDef>,
}

impl CairoLayout {
    pub(crate) fn plain_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::plain,
            rc_units: 16,
            builtins: BuiltinsInstanceDef::plain(),
            public_memory_fraction: 4,
            diluted_pool_instance_def: None,
        }
    }

    pub(crate) fn small_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::small,
            rc_units: 16,
            builtins: BuiltinsInstanceDef::small(),
            public_memory_fraction: 4,
            diluted_pool_instance_def: None,
        }
    }

    pub(crate) fn dex_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::dex,
            rc_units: 4,
            builtins: BuiltinsInstanceDef::dex(),
            public_memory_fraction: 4,
            diluted_pool_instance_def: None,
        }
    }

    pub(crate) fn recursive_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::recursive,
            rc_units: 4,
            builtins: BuiltinsInstanceDef::recursive(),
            public_memory_fraction: 8,
            diluted_pool_instance_def: Some(DilutedPoolInstanceDef::default()),
        }
    }

    pub(crate) fn starknet_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::starknet,
            rc_units: 4,
            builtins: BuiltinsInstanceDef::starknet(),
            public_memory_fraction: 8,
            diluted_pool_instance_def: Some(DilutedPoolInstanceDef::new(2, 4, 16)),
        }
    }

    pub(crate) fn starknet_with_keccak_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::starknet_with_keccak,
            rc_units: 4,
            builtins: BuiltinsInstanceDef::starknet_with_keccak(),
            public_memory_fraction: 8,
            diluted_pool_instance_def: Some(DilutedPoolInstanceDef::default()),
        }
    }

    pub(crate) fn recursive_large_output_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::recursive_large_output,
            rc_units: 4,
            builtins: BuiltinsInstanceDef::recursive_large_output(),
            public_memory_fraction: 8,
            diluted_pool_instance_def: Some(DilutedPoolInstanceDef::default()),
        }
    }
    pub(crate) fn recursive_with_poseidon() -> CairoLayout {
        CairoLayout {
            name: LayoutName::recursive_with_poseidon,
            rc_units: 4,
            builtins: BuiltinsInstanceDef::recursive_with_poseidon(),
            public_memory_fraction: 8,
            diluted_pool_instance_def: Some(DilutedPoolInstanceDef::new(8, 4, 16)),
        }
    }

    pub(crate) fn all_cairo_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::all_cairo,
            rc_units: 4,
            builtins: BuiltinsInstanceDef::all_cairo(),
            public_memory_fraction: 8,
            diluted_pool_instance_def: Some(DilutedPoolInstanceDef::default()),
        }
    }

    pub(crate) fn all_solidity_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::all_solidity,
            rc_units: 8,
            builtins: BuiltinsInstanceDef::all_solidity(),
            public_memory_fraction: 8,
            diluted_pool_instance_def: Some(DilutedPoolInstanceDef::default()),
        }
    }

    pub(crate) fn dynamic_instance() -> CairoLayout {
        CairoLayout {
            name: LayoutName::dynamic,
            rc_units: 16,
            builtins: BuiltinsInstanceDef::dynamic(),
            public_memory_fraction: 8,
            diluted_pool_instance_def: Some(DilutedPoolInstanceDef::default()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::*;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_plain_instance() {
        let layout = CairoLayout::plain_instance();
        let builtins = BuiltinsInstanceDef::plain();
        assert_eq!(layout.name, LayoutName::plain);
        assert_eq!(layout.rc_units, 16);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 4);
        assert_eq!(layout.diluted_pool_instance_def, None);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_small_instance() {
        let layout = CairoLayout::small_instance();
        let builtins = BuiltinsInstanceDef::small();
        assert_eq!(layout.name, LayoutName::small);
        assert_eq!(layout.rc_units, 16);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 4);
        assert_eq!(layout.diluted_pool_instance_def, None);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_dex_instance() {
        let layout = CairoLayout::dex_instance();
        let builtins = BuiltinsInstanceDef::dex();
        assert_eq!(layout.name, LayoutName::dex);
        assert_eq!(layout.rc_units, 4);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 4);
        assert_eq!(layout.diluted_pool_instance_def, None);
    }

    #[test]
    fn get_recursive_instance() {
        let layout = CairoLayout::recursive_instance();
        let builtins = BuiltinsInstanceDef::recursive();
        assert_eq!(layout.name, LayoutName::recursive);
        assert_eq!(layout.rc_units, 4);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 8);
        assert_eq!(
            layout.diluted_pool_instance_def,
            Some(DilutedPoolInstanceDef::default())
        );
    }

    #[test]
    fn get_starknet_instance() {
        let layout = CairoLayout::starknet_instance();
        let builtins = BuiltinsInstanceDef::starknet();
        assert_eq!(layout.name, LayoutName::starknet);
        assert_eq!(layout.rc_units, 4);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 8);
        assert_eq!(
            layout.diluted_pool_instance_def,
            Some(DilutedPoolInstanceDef::new(2, 4, 16))
        );
    }

    #[test]
    fn get_starknet_with_keccak_instance() {
        let layout = CairoLayout::starknet_with_keccak_instance();
        let builtins = BuiltinsInstanceDef::starknet_with_keccak();
        assert_eq!(layout.name, LayoutName::starknet_with_keccak);
        assert_eq!(layout.rc_units, 4);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 8);
        assert_eq!(
            layout.diluted_pool_instance_def,
            Some(DilutedPoolInstanceDef::default())
        );
    }

    #[test]
    fn get_recursive_large_output_instance() {
        let layout = CairoLayout::recursive_large_output_instance();
        let builtins = BuiltinsInstanceDef::recursive_large_output();
        assert_eq!(layout.name, LayoutName::recursive_large_output);
        assert_eq!(layout.rc_units, 4);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 8);
        assert_eq!(
            layout.diluted_pool_instance_def,
            Some(DilutedPoolInstanceDef::default())
        );
    }

    #[test]
    fn get_all_cairo_instance() {
        let layout = CairoLayout::all_cairo_instance();
        let builtins = BuiltinsInstanceDef::all_cairo();
        assert_eq!(layout.name, LayoutName::all_cairo);
        assert_eq!(layout.rc_units, 4);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 8);
        assert_eq!(
            layout.diluted_pool_instance_def,
            Some(DilutedPoolInstanceDef::default())
        );
    }

    #[test]
    fn get_all_solidity_instance() {
        let layout = CairoLayout::all_solidity_instance();
        let builtins = BuiltinsInstanceDef::all_solidity();
        assert_eq!(layout.name, LayoutName::all_solidity);
        assert_eq!(layout.rc_units, 8);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 8);
        assert_eq!(
            layout.diluted_pool_instance_def,
            Some(DilutedPoolInstanceDef::default())
        );
    }

    #[test]
    fn get_dynamic_instance() {
        let layout = CairoLayout::dynamic_instance();
        let builtins = BuiltinsInstanceDef::dynamic();
        assert_eq!(layout.name, LayoutName::dynamic);
        assert_eq!(layout.rc_units, 16);
        assert_eq!(layout.builtins, builtins);
        assert_eq!(layout.public_memory_fraction, 8);
        assert_eq!(
            layout.diluted_pool_instance_def,
            Some(DilutedPoolInstanceDef::default())
        );
    }
}
