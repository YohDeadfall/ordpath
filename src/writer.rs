use std::io::Write;

use crate::enc::Encoding;
use crate::{Error, ErrorKind};

/// The `Reader<R, E>` struct allows reading ORDPATH encoded values directly from any source implementing [`Read`].
pub struct Writer<W: Write, E: Encoding> {
    dst: W,
    enc: E,
    acc: u64,
    len: u8,
}

impl<W: Write, E: Encoding> Writer<W, E> {
    /// Creates a new `Writer<R, E>`.
    pub fn new(dst: W, enc: E) -> Self {
        Self {
            dst,
            enc,
            acc: 0,
            len: 0,
        }
    }

    /// Write a value into this writer.
    pub fn write(&mut self, value: i64) -> Result<(), Error> {
        let stage = self
            .enc
            .stage_by_value(value)
            .ok_or_else(|| Error::new(ErrorKind::InvalidInput))?;
        let prefix = stage.prefix() as u64;
        let value = (value - stage.value_low()) as u64;

        let buf = match stage.len() < 64 {
            true => (prefix << (stage.value_len()) | value) << (64 - stage.len()),
            false => prefix << (64 - stage.prefix_len()) | (value >> (stage.len() - 64)),
        };

        let len = self.len & 127;
        self.acc |= buf >> len;

        let len = len + stage.len();
        self.len = 128
            | if len < 64 {
                len
            } else {
                let left = len - 64;

                self.len = 0;
                self.dst.write_all(&self.acc.to_be_bytes())?;
                self.acc = if stage.len() <= 64 {
                    buf << (stage.len() - left)
                } else {
                    value << (stage.len() - left)
                };

                left
            };

        Ok(())
    }
}

impl<W: Write, E: Encoding> Drop for Writer<W, E> {
    fn drop(&mut self) {
        if self.len > 0 {
            let len = self.len as usize & 127;
            let acc = self.acc | (1 << (63 - len));

            let len = (len + 1).div_ceil(8);
            let acc = &acc.to_be_bytes()[..len];

            _ = self.dst.write_all(acc);
        }
    }
}
