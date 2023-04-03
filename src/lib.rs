use std::cmp::Ordering;

pub struct Stage {
    prefix_len: u8,
    prefix: u8,
    value_len: u8,
    value_low: i64,
}

impl Stage {
    const fn new(prefix_len: u8, prefix: u8, value_len: u8, value_low: i64) -> Stage {
        assert!(prefix_len < 8);
        assert!(value_len < 64);

        Stage {
            prefix_len,
            prefix,
            value_len,
            value_low,
        }
    }

    const fn prefix(&self) -> u8 {
        self.prefix
    }

    const fn prefix_len(&self) -> u8 {
        self.prefix_len
    }

    const fn value_low(&self) -> i64 {
        self.value_low
    }

    const fn value_high(&self) -> i64 {
        self.value_low + ((1 << self.value_len) - 1)
    }

    const fn value_len(&self) -> u8 {
        self.value_len
    }
}

trait Encoding {
    fn stage_by_prefix(&self, prefix: u8) -> Option<&Stage>;
    fn stage_by_value(&self, value: i64) -> Option<&Stage>;
}

macro_rules! replace_expr {
    ($e:expr; $s:expr) => {
        $s
    };
}

macro_rules! count {
    ($($e:expr,)*) => {<[()]>::len(&[$(replace_expr!($e; ())),*])};
}

#[macro_export]
macro_rules! encoding {
    ($v:vis $t:ident :[$(($prefix:expr, $prefix_len:expr, $value_len:expr)),+]) => {
        #[derive(Copy, Clone, Default, Debug)]
        $v struct $t;

        impl $t {
            const STAGES: [Stage; count!($($prefix,)*)] = {
                let mut stages = [
                    $(Stage::new($prefix_len, $prefix, $value_len, 0)),+
                ];

                let origin = stages.len() / 2;

                let mut index = origin;
                while index > 0  {
                    index -= 1;
                    stages[index] = Stage::new(
                        stages[index].prefix_len(),
                        stages[index].prefix(),
                        stages[index].value_len(),
                        stages[index + 1].value_low() - stages[index].value_high() - 1);
                }

                let mut index = origin;
                while index + 1 < stages.len() {
                    index += 1;
                    stages[index] = Stage::new(
                        stages[index].prefix_len(),
                        stages[index].prefix(),
                        stages[index].value_len(),
                        stages[index - 1].value_high() + 1);
                }

                stages
            };

            const STAGE_LOOKUP: [u8; u8::MAX as usize] = {
                let mut lookup = [u8::MAX; u8::MAX as usize];
                let mut index = 0;
                while index < Self::STAGES.len() {
                    let stage = &Self::STAGES[index];
                    let prefix_offset = u8::BITS as u8 - stage.prefix_len();
                    let prefix = stage.prefix << prefix_offset;
                    let mut data = 0;
                    while data < 1 << prefix_offset {
                        lookup[(prefix | data) as usize] = index as u8;
                        data +=1;
                    }

                    index +=1;
                }

                lookup
            };
        }

        impl Encoding for $t {
            fn stage_by_prefix(&self, prefix: u8) -> Option<&Stage> {
                match Self::STAGE_LOOKUP[prefix as usize] {
                    u8::MAX => None,
                    index => Some(&Self::STAGES[index as usize])
                }
            }

            fn stage_by_value(&self, value: i64) -> Option<&Stage> {
                Self::STAGES.binary_search_by(|stage|{
                    let result = stage.value_low().cmp(&value);
                    if result.is_gt() {
                        return result;
                    }

                    let result = stage.value_high().cmp(&value);
                    if result.is_lt() {
                        return result;
                    }

                    Ordering::Equal
                })
                .map(|index| &Self::STAGES[index]).ok()
            }
        }
    };
}

encoding!(pub Default: [
    (0b0000001, 7, 48),
    (0b0000010, 7, 32),
    (0b0000011, 7, 16),
    (0b000010 , 6, 12),
    (0b000011 , 6, 8 ),
    (0b00010  , 5, 6 ),
    (0b00011  , 5, 4 ),
    (0b001    , 3, 3 ),
    (0b01     , 2, 3 ),
    (0b100    , 3, 4 ),
    (0b101    , 3, 6 ),
    (0b1100   , 4, 8 ),
    (0b1101   , 4, 12),
    (0b11100  , 5, 16),
    (0b11101  , 5, 32),
    (0b11110  , 5, 48)]
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_encoding() {
        assert_eq!(
            Default::STAGES.map(|s| (s.prefix(), s.value_low(), s.value_high())),
            [
                (0b0000001, -281479271747928, -4295037273),
                (0b0000010, -4295037272, -69977),
                (0b0000011, -69976, -4441),
                (0b000010, -4440, -345),
                (0b000011, -344, -89),
                (0b00010, -88, -25),
                (0b00011, -24, -9),
                (0b001, -8, -1),
                (0b01, 0, 7),
                (0b100, 8, 23),
                (0b101, 24, 87),
                (0b1100, 88, 343),
                (0b1101, 344, 4439),
                (0b11100, 4440, 69975),
                (0b11101, 69976, 4295037271),
                (0b11110, 4295037272, 281479271747927)
            ]
        );
    }
}
