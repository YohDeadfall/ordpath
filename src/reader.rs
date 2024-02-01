use std::io::Read;

use crate::enc::Encoding;
use crate::{Error, ErrorKind};

/// The `Reader<R, E>` struct allows reading ORDPATH encoded values directly from any source implementing [`Read`].
pub struct Reader<R: Read, E: Encoding> {
    src: R,
    enc: E,
    acc: u64,
    len: u8,
}

impl<R: Read, E: Encoding> Reader<R, E> {
    /// Creates a new `Reader<R, E>`.
    pub fn new(src: R, enc: E) -> Self {
        Self {
            src,
            enc,
            acc: 1 << 63,
            len: 0,
        }
    }

    /// Read the next value.
    pub fn read(&mut self) -> Result<Option<i64>, Error> {
        let prefix = (self.acc >> 56) as u8;
        let stage = self.enc.stage_by_prefix(prefix);

        if let Some(stage) = stage {
            if stage.len() <= self.len {
                let value = (self.acc << stage.prefix_len()) >> (64 - stage.value_len());

                self.acc <<= stage.len();
                self.len -= stage.len();

                return Ok(Some(value as i64 + stage.value_low()));
            }
        }

        let mut buf = [0u8; 8];
        let consumed = self.src.read(&mut buf)?;

        if consumed > 0 {
            let acc_next = u64::from_be_bytes(buf);
            let acc = if self.len > 0 {
                acc_next >> self.len | self.acc
            } else {
                acc_next
            };

            let len = self.len + consumed as u8 * 8;
            let prefix = (acc >> 56) as u8;

            if let Some(stage) = self.enc.stage_by_prefix(prefix) {
                if stage.len() <= len {
                    self.acc = acc_next << (stage.len() - self.len);
                    self.len = {
                        let left = len - stage.len();
                        if len < 64 {
                            left.min(63u8.saturating_sub(self.acc.trailing_zeros() as u8))
                        } else {
                            left
                        }
                    };

                    let value = (acc << stage.prefix_len()) >> (64 - stage.value_len());

                    return Ok(Some(value as i64 + stage.value_low()));
                }
            }
        }

        if self.len == 0 && self.acc == 1 << 63 {
            Ok(None)
        } else {
            Err(Error::new(ErrorKind::InvalidInput))
        }
    }
}
