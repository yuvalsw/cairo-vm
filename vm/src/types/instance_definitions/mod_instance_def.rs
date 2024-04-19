use serde::Serialize;

pub(crate) const N_WORDS: usize = 4;

pub(crate) const CELLS_PER_MOD: u32 = 7;

#[derive(Serialize, Debug, PartialEq, Clone)]
pub(crate) struct ModInstanceDef {
    pub(crate) ratio: Option<u32>,
    pub(crate) word_bit_len: u32,
    pub(crate) batch_size: usize,
}

impl ModInstanceDef {
    pub(crate) fn new(ratio: Option<u32>, batch_size: usize, word_bit_len: u32) -> Self {
        ModInstanceDef {
            ratio,
            word_bit_len,
            batch_size,
        }
    }
}
