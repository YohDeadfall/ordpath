use std::io::Read;

use crate::enc::{Encoding, Stage};
use crate::{Error, ErrorKind};

/// The `Reader<R, E>` struct allows reading ORDPATH encoded values directly from any source implementing [`Read`].
pub struct Reader<R: Read + ?Sized, E: Encoding> {
    one: bool,
    acc: u64,
    len: u8,
    enc: E,
    src: R,
}

impl<R: Read, E: Encoding> Reader<R, E> {
    /// Creates a new `Reader<R, E>` for the gives source.
    pub fn new(src: R, enc: E, one_term: bool) -> Self {
        Self {
            one: one_term,
            acc: (one_term as u64) << 63,
            len: 0,
            enc,
            src,
        }
    }

    /// Reads the next value and provides the corresponding stage.
    pub fn read(&mut self) -> Result<Option<(i64, &Stage)>, Error> {
        let prefix = (self.acc >> 56) as u8;
        let stage = self.enc.stage_by_prefix(prefix);

        if let Some(stage) = stage {
            if stage.len() <= self.len {
                let value = (self.acc << stage.prefix_len()) >> (64 - stage.value_len());

                self.acc <<= stage.len();
                self.len -= stage.len();

                let value = value as i64 + stage.value_low();
                return Ok(Some((value, stage)));
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
                        if self.one && len < 64 {
                            left.min(63u8.saturating_sub(self.acc.trailing_zeros() as u8))
                        } else {
                            left
                        }
                    };

                    let value = ((acc << stage.prefix_len()) >> (64 - stage.value_len())) as i64
                        + stage.value_low();
                    return Ok(Some((value, stage)));
                }
            }
        }

        if self.acc == (self.one as u64) << 63 {
            Ok(None)
        } else {
            Err(Error::new(ErrorKind::InvalidInput))
        }
    }
}
