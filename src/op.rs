use regex::Regex;

use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::str::FromStr;

use self::error::{InvalidDivError, InvalidInsError, InvalidRpcError};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Op {
    inner: OpKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum OpKind {
    Add(i32),
    Mul(i32),
    Div(i32),
    Del,
    Ins { digits: u8, n: u32 },
    Rpc { from_digits: u8, from_n: u32, to_digits: u8, to_n: u32 },
}

impl Op {
    pub fn add(n: i32) -> Self {
        Op {
            inner: OpKind::Add(n),
        }
    }

    pub fn mul(n: i32) -> Self {
        Op {
            inner: OpKind::Mul(n),
        }
    }

    pub fn div(n: i32) -> Result<Self, InvalidDivError> {
        if n == 0 {
            Err(InvalidDivError)
        } else {
            Ok(Op {
                inner: OpKind::Div(n),
            })
        }
    }

    pub fn del() -> Self {
        Op { inner: OpKind::Del }
    }

    pub fn ins(digits: u8, n: u32) -> Result<Self, InvalidInsError> {
        if n >= 10u32.pow(u32::from(digits)) {
            Err(InvalidInsError)
        } else {
            Ok(Op {
                inner: OpKind::Ins { digits, n },
            })
        }
    }

    pub fn rpc(from_digits: u8, from_n: u32, to_digits: u8, to_n: u32) -> Result<Self, InvalidRpcError> {
        if from_n >= 10u32.pow(u32::from(from_digits)) || to_n >= 10u32.pow(u32::from(to_digits)) {
            Err(InvalidRpcError)
        } else {
            Ok(Op {
                inner: OpKind::Rpc { from_digits, from_n, to_digits, to_n },
            })
        }
    }

    pub fn apply(&self, n: i32) -> Option<i32> {
        use self::OpKind;
        match self.inner {
            OpKind::Add(m) => Some(m + n),
            OpKind::Mul(m) => Some(m * n),
            OpKind::Div(m) => if n % m == 0 {
                Some(n / m)
            } else {
                None
            },
            OpKind::Del => Some((n.abs() / 10) * n.signum()),
            OpKind::Ins { digits, n: m } => Some(
                n * 10i32.pow(u32::from(digits)) + i32::try_from(m).ok()? * if n < 0 {
                    -1
                } else {
                    1
                }
            ),
            OpKind::Rpc { from_digits, from_n, to_digits, to_n } => {
                let mut haystack = n.abs();
                let mut haystack_pow_of_ten = 1;
                loop {
                    let next_pow_of_ten = haystack_pow_of_ten * 10;
                    if next_pow_of_ten <= haystack {
                        haystack_pow_of_ten = next_pow_of_ten;
                    } else {
                        break;
                    }
                }

                let from_pow_of_ten = 10i32.pow(u32::from(from_digits));
                let to_pow_of_ten = 10i32.pow(u32::from(to_digits));
                let from_n = i32::try_from(from_n).ok()?;
                let to_n = i32::try_from(to_n).ok()?;

                let mut result = 0;
                let mut intermediate = 0;
                let mut intermediate_pow_of_ten = 0;

                while haystack_pow_of_ten != 0 {
                    if intermediate_pow_of_ten != from_pow_of_ten {
                        intermediate_pow_of_ten = if intermediate_pow_of_ten == 0 {
                            1
                        } else {
                            intermediate_pow_of_ten * 10
                        };
                        intermediate = intermediate * 10 + haystack / haystack_pow_of_ten;
                    } else if intermediate == from_n {
                        result = result * to_pow_of_ten * 10 + to_n;
                        intermediate_pow_of_ten = 1;
                        intermediate = haystack / haystack_pow_of_ten;
                    } else {
                        intermediate = (intermediate % intermediate_pow_of_ten) * 10 + haystack / haystack_pow_of_ten;
                    }
                    haystack %= haystack_pow_of_ten;
                    haystack_pow_of_ten /= 10;
                }

                if intermediate_pow_of_ten == from_pow_of_ten && intermediate == from_n {
                    result = result * to_pow_of_ten * 10 + to_n;
                } else {
                    result = result * intermediate_pow_of_ten * 10 + intermediate;
                }

                Some(result)
            }
        }.filter(|&n| -100000 < n && n < 1000000)
    }
}

impl FromStr for Op {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use self::Op;

        lazy_static! {
            static ref RPC_PATTERN: Regex = Regex::new(r"(\d+)=>(\d+)").unwrap();
        }

        if s == "<<" {
            Ok(Op::del())
        } else if s.starts_with('-') {
            s.parse().map(Op::add).map_err(|_| ())
        } else if s.starts_with('+') {
            s[1..].parse().map(Op::add).map_err(|_| ())
        } else if s.starts_with('*') {
            s[1..].parse().map(Op::mul).map_err(|_| ())
        } else if s.starts_with('/') {
            s[1..]
                .parse()
                .map_err(|_| ())
                .and_then(|n| Op::div(n).map_err(|_| ()))
        } else if let Ok(n) = s.parse::<u32>() {
            Op::ins(s.len().try_into().map_err(|_| ())?, n).map_err(|_| ())
        } else if let Some(captures) = RPC_PATTERN.captures(s) {
            if captures.get(0).ok_or(())?.as_str().len() == s.len() {
                let from = captures.get(1).ok_or(())?.as_str();
                let to = captures.get(2).ok_or(())?.as_str();
                Ok(Op {
                    inner: OpKind::Rpc {
                        from_digits: u8::try_from(from.len()).map_err(|_| ())?,
                        from_n: from.parse().map_err(|_| ())?,
                        to_digits: u8::try_from(to.len()).map_err(|_| ())?,
                        to_n: to.parse().map_err(|_| ())?,
                    },
                })
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::OpKind;

        match self.inner {
            OpKind::Add(n) => {
                if n >= 0 {
                    write!(f, "+{}", n)
                } else {
                    write!(f, "{}", n)
                }
            }
            OpKind::Mul(n) => write!(f, "*{}", n),
            OpKind::Div(n) => write!(f, "/{}", n),
            OpKind::Del => write!(f, "<<"),
            OpKind::Ins { digits, n } => {
                let mut pow_of_ten = if digits != 0 {
                    10u32.pow(u32::from(digits - 1))
                } else {
                    0
                };
                while pow_of_ten > n {
                    write!(f, "0")?;
                    pow_of_ten /= 10;
                }
                if n != 0 {
                    write!(f, "{}", n)
                } else {
                    Ok(())
                }
            },
            OpKind::Rpc { from_digits, from_n, to_digits, to_n } => {
                let mut pow_of_ten = if from_digits != 0 {
                    10u32.pow(u32::from(from_digits - 1))
                } else {
                    0
                };
                while pow_of_ten > from_n {
                    write!(f, "0")?;
                    pow_of_ten /= 10;
                }
                if from_n != 0 {
                    write!(f, "{}=>", from_n)?
                }
                pow_of_ten = if to_digits != 0 {
                    10u32.pow(u32::from(to_digits - 1))
                } else {
                    0
                };
                while pow_of_ten > to_n {
                    write!(f, "0")?;
                    pow_of_ten /= 10;
                }
                if to_n != 0 {
                    write!(f, "{}", to_n)
                } else {
                    Ok(())
                }
            }
        }
    }
}

pub mod error {
    /// Returned on failed call to Op::div.
    /// Currently only returned on Op::div(0).
    pub struct InvalidDivError;

    /// Returned on failed call to Op::ins.
    /// Currently, the initializer fails when the base 10 representation of n is shorter than the given digits; e. g. Op::ins(1, 10).
    pub struct InvalidInsError;

    pub struct InvalidRpcError;
}

#[cfg(test)]
mod tests {
    use super::{Op, OpKind};

    #[test]
    fn parse_add() {
        let test_cases = [
            ("+1", 1),
            ("+12", 12),
            ("+123", 123),
            ("+1234", 1234),
            ("+12345", 12345),
            ("+123456", 123456),
            ("+1234567", 1234567),
        ];

        for &(input, expected) in &test_cases {
            let result = input.parse::<Op>();
            match result {
                Ok(Op { inner: OpKind::Add(n) }) if n == expected => (),
                something_else => panic!("Parsed {:?}, Expected Ok(Op {{ inner: Add({}) }}); Got {:?} instead", input, expected, something_else),
            }
        }
    }

    #[test]
    fn parse_sub() {
        let test_cases = [
            ("-1", -1),
            ("-12", -12),
            ("-123", -123),
            ("-1234", -1234),
            ("-12345", -12345),
            ("-123456", -123456),
        ];

        for &(input, expected) in &test_cases {
            let result = input.parse::<Op>();
            match result {
                Ok(Op { inner: OpKind::Add(n) }) if n == expected => (),
                something_else => panic!("Parsed {:?}, Expected Ok(Op {{ inner: Add({}) }}); Got {:?} instead", input, expected, something_else),
            }
        }
    }

    #[test]
    fn parse_mul() {
        let test_cases = [
            ("*1", 1),
            ("*12", 12),
            ("*123", 123),
            ("*1234", 1234),
            ("*12345", 12345),
            ("*123456", 123456),
            ("*1234567", 1234567),
            ("*-1", -1),
            ("*-12", -12),
            ("*-123", -123),
            ("*-1234", -1234),
            ("*-12345", -12345),
            ("*-123456", -123456),
        ];

        for &(input, expected) in &test_cases {
            let result = input.parse::<Op>();
            match result {
                Ok(Op { inner: OpKind::Mul(n) }) if n == expected => (),
                something_else => panic!("Parsed {:?}, Expected Ok(Op {{ inner: Mul({}) }}); Got {:?} instead", input, expected, something_else),
            }
        }
    }

    #[test]
    fn parse_div() {
        let test_cases = [
            ("/1", 1),
            ("/12", 12),
            ("/123", 123),
            ("/1234", 1234),
            ("/12345", 12345),
            ("/123456", 123456),
            ("/1234567", 1234567),
            ("/-1", -1),
            ("/-12", -12),
            ("/-123", -123),
            ("/-1234", -1234),
            ("/-12345", -12345),
            ("/-123456", -123456),
        ];

        for &(input, expected) in &test_cases {
            let result = input.parse::<Op>();
            match result {
                Ok(Op { inner: OpKind::Div(n) }) if n == expected => (),
                something_else => panic!("Parsed {:?}, Expected Ok(Op {{ inner: Div({}) }}); Got {:?} instead", input, expected, something_else),
            }
        }
    }

    #[test]
    fn parse_del() {
        assert_eq!("<<".parse::<Op>(), Ok(Op { inner: OpKind::Del }));
    }

    #[test]
    fn parse_ins() {
        let test_cases = [
            ("0", (1, 0)),
            ("00", (2, 0)),
            ("000", (3, 0)),
            ("0000", (4, 0)),
            ("00000", (5, 0)),
            ("1", (1, 1)),
            ("01", (2, 1)),
            ("001", (3, 1)),
            ("12", (2, 12)),
            ("123", (3, 123)),
            ("012", (3, 12)),
            ("0012", (4, 12)),
            ("1234567", (7, 1234567)),
        ];

        for &(input, (expected_digits, expected_n)) in &test_cases {
            let result = input.parse::<Op>();
            match result {
                Ok(Op { inner: OpKind::Ins {digits, n} }) if digits == expected_digits && n == expected_n => (),
                something_else => panic!("Parsed {:?}, Expected Ok(Op {{ inner: Ins {{ digits: {}, n: {} }} }}); Got {:?} instead", input, expected_digits, expected_n, something_else),
            }
        }
    }

    #[test]
    fn parse_rpc() {
        let test_cases = [
            ("0=>1", ((1, 0), (1, 1))),
            ("00=>1", ((2, 0), (1, 1))),
            ("12=>34", ((2, 12), (2, 34))),
            ("02=>04", ((2, 2), (2, 4))),
            ("123=>0", ((3, 123), (1, 0))),
            ("123=>00", ((3, 123), (2, 0))),
            ("003=>0007", ((3, 3), (4, 7))),
        ];

        for &(input, ((expected_from_digits, expected_from_n), (expected_to_digits, expected_to_n))) in &test_cases {
            let result = input.parse::<Op>();
            match result {
                Ok(Op {inner: OpKind::Rpc { from_digits, from_n, to_digits, to_n }})
                    if from_digits == expected_from_digits &&
                       from_n == expected_from_n &&
                       to_digits == expected_to_digits &&
                       to_n == expected_to_n => (),
                something_else => panic!("Parsed {:?}, Expected Ok(Op {{ inner: Rpc {{ from_digits: {}, from_n: {}, to_digits: {}, to_n: {} }} }}); Got {:?} instead", input, expected_from_digits, expected_from_n, expected_to_digits, expected_to_n, something_else),
            }
        }
    }

    #[test]
    fn parse_err() {
        let test_cases = [
            "a", "1a", "1+1", "1=>-1", "-1=>1", "1=>2a", "<<1", "+1+1", "1=>", "=>1"
        ];

        for input in &test_cases {
            let result = input.parse::<Op>();
            match result {
                Err(()) => (),
                something_else => panic!("Parsed {:?}, Expected Err(()); Got {:?} instead", input, something_else),
            } 
        }
    }
}
