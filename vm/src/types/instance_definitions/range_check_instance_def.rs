use serde::Serialize;
pub(crate) const CELLS_PER_RANGE_CHECK: u32 = 1;

#[derive(Serialize, Debug, PartialEq)]
pub(crate) struct RangeCheckInstanceDef {
    pub(crate) ratio: Option<u32>,
}

impl Default for RangeCheckInstanceDef {
    fn default() -> Self {
        RangeCheckInstanceDef { ratio: Some(8) }
    }
}

impl RangeCheckInstanceDef {
    pub(crate) fn new(ratio: Option<u32>) -> Self {
        RangeCheckInstanceDef { ratio }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::*;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_new() {
        let builtin_instance = RangeCheckInstanceDef { ratio: Some(10) };
        assert_eq!(RangeCheckInstanceDef::new(Some(10)), builtin_instance);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_default() {
        let builtin_instance = RangeCheckInstanceDef { ratio: Some(8) };
        assert_eq!(RangeCheckInstanceDef::default(), builtin_instance);
    }
}
