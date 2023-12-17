use thiserror_no_std::Error;
use zip::result::ZipError;

#[derive(Debug, Error)]
pub enum DeserializeMemoryError {
    #[error("Unexpected EOF while parsing the memory file")]
    UnexpectedEof,

    #[error("Address at position {0} is not a relocatable value")]
    AddressIsNotRelocatable(usize),

    #[error(transparent)]
    Io(#[from] std::io::Error),
}

#[derive(Debug, Error)]
pub enum CairoPieError {
    #[cfg(feature = "std")]
    #[error(transparent)]
    IO(#[from] std::io::Error),

    #[error(transparent)]
    Parse(#[from] serde_json::Error),

    #[error(transparent)]
    Zip(#[from] ZipError),

    #[error(transparent)]
    DeserializeMemory(#[from] DeserializeMemoryError),
}
