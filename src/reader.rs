use std::io::Read;

use crate::enc::Encoding;
use crate::{Error, ErrorKind};

/// The `Reader<R, E>` struct allows reading ORDPATH encoded values directly from any source implementing [`Read`].
pub struct Reader<R: Read, E: Encoding> {
    src: R,
    enc: E,
    acc: u64,
    acc_len: u8,
}

impl<R: Read, E: Encoding> Reader<R, E> {
    /// To be done.
    pub fn new(src: R, enc: E) -> Self {
        Self {
            src,
            enc,
            acc: 0,
            acc_len: 0,
        }
    }

    /// To be done.
    pub fn read(&mut self) -> Result<Option<i64>, Error> {
        let prefix = (self.acc >> 56) as u8;
        let stage = self.enc.stage_by_prefix(prefix);

        if let Some(stage) = stage {
            if stage.len() <= self.acc_len {
                let value = (self.acc << stage.prefix_len()) >> (64 - stage.value_len());

                self.acc <<= stage.len();
                self.acc_len -= stage.len();

                return Ok(Some(value as i64 + stage.value_low()));
            }
        }

        let mut buf = [0u8; 8];
        let consumed = self.src.read(&mut buf)?;

        if consumed > 0 {
            let acc_next = u64::from_be_bytes(buf);
            let acc = self.acc | acc_next >> self.acc_len;
            let len = self.acc_len + consumed as u8 * 8;
            let prefix = (acc >> 56) as u8;

            if let Some(stage) = self.enc.stage_by_prefix(prefix) {
                if stage.len() <= len {
                    let value = (acc << stage.prefix_len()) >> (64 - stage.value_len());

                    self.acc = acc_next << (stage.len() - self.acc_len);
                    self.acc_len = len - stage.len();

                    return Ok(Some(value as i64 + stage.value_low()));
                }
            }

            return Err(Error::new(ErrorKind::InvalidInput));
        }

        Ok(None)
    }
}
