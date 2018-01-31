use regex::Regex;

use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::str::FromStr;

use self::error::{InvalidDivError, InvalidInsError};

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
    Rpc(String, String),
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

    pub fn rpc(from: String, to: String) -> Self {
        // A dummy impl; will be refactored
        Op {
            inner: OpKind::Rpc(from, to),
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
            OpKind::Rpc(ref from, ref to) => Some(n.to_string().replace(from, to).parse().unwrap()),
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
            Ok(Op::rpc(
                captures.get(1).unwrap().as_str().to_string(),
                captures.get(2).unwrap().as_str().to_string(),
            ))
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
            OpKind::Rpc(ref from, ref to) => write!(f, "{}=>{}", from, to),
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
}

#[cfg(test)]
mod tests {
    use super::Op;

    #[test]
    fn parse_add() {
        let test_cases = [
            ("+1", Ok(Op::Add(1))),
            ("+12", Ok(Op::Add(12))),
            ("+123", Ok(Op::Add(123))),
            ("+1234", Ok(Op::Add(1234))),
            ("+12345", Ok(Op::Add(12345))),
            ("+123456", Ok(Op::Add(123456))),
            ("+1234567", Ok(Op::Add(1234567))),
        ];

        for &(ref input, ref output) in &test_cases {
            assert_eq!(input.parse::<Op>(), *output);
        }
    }

    #[test]
    fn parse_sub() {
        let test_cases = [
            ("-1", Ok(Op::Add(-1))),
            ("-12", Ok(Op::Add(-12))),
            ("-123", Ok(Op::Add(-123))),
            ("-1234", Ok(Op::Add(-1234))),
            ("-12345", Ok(Op::Add(-12345))),
            ("-123456", Ok(Op::Add(-123456))),
        ];

        for &(ref input, ref output) in &test_cases {
            assert_eq!(input.parse::<Op>(), *output);
        }
    }

    #[test]
    fn parse_mul() {
        let test_cases = [
            ("*1", Ok(Op::Mul(1))),
            ("*12", Ok(Op::Mul(12))),
            ("*123", Ok(Op::Mul(123))),
            ("*1234", Ok(Op::Mul(1234))),
            ("*12345", Ok(Op::Mul(12345))),
            ("*123456", Ok(Op::Mul(123456))),
            ("*1234567", Ok(Op::Mul(1234567))),
            ("*-1", Ok(Op::Mul(-1))),
            ("*-12", Ok(Op::Mul(-12))),
            ("*-123", Ok(Op::Mul(-123))),
            ("*-1234", Ok(Op::Mul(-1234))),
            ("*-12345", Ok(Op::Mul(-12345))),
            ("*-123456", Ok(Op::Mul(-123456))),
        ];

        for &(ref input, ref output) in &test_cases {
            assert_eq!(input.parse::<Op>(), *output);
        }
    }

    #[test]
    fn parse_div() {
        let test_cases = [
            ("/1", Ok(Op::Div(1))),
            ("/12", Ok(Op::Div(12))),
            ("/123", Ok(Op::Div(123))),
            ("/1234", Ok(Op::Div(1234))),
            ("/12345", Ok(Op::Div(12345))),
            ("/123456", Ok(Op::Div(123456))),
            ("/1234567", Ok(Op::Div(1234567))),
            ("/-1", Ok(Op::Div(-1))),
            ("/-12", Ok(Op::Div(-12))),
            ("/-123", Ok(Op::Div(-123))),
            ("/-1234", Ok(Op::Div(-1234))),
            ("/-12345", Ok(Op::Div(-12345))),
            ("/-123456", Ok(Op::Div(-123456))),
        ];

        for &(ref input, ref output) in &test_cases {
            assert_eq!(input.parse::<Op>(), *output);
        }
    }

    #[test]
    fn parse_del() {
        assert_eq!("<<".parse::<Op>(), Ok(Op::Del));
    }

    #[test]
    fn parse_ins() {
        let test_cases = [
            ("1", Ok(Op::Ins("1".to_string()))),
            ("12", Ok(Op::Ins("12".to_string()))),
            ("123", Ok(Op::Ins("123".to_string()))),
            ("1234", Ok(Op::Ins("1234".to_string()))),
            ("12345", Ok(Op::Ins("12345".to_string()))),
            ("123456", Ok(Op::Ins("123456".to_string()))),
            ("1234567", Ok(Op::Ins("1234567".to_string()))),
        ];

        for &(ref input, ref output) in &test_cases {
            assert_eq!(input.parse::<Op>(), *output);
        }
    }

    #[test]
    fn parse_rpc() {
        let test_cases = [
            ("1=>2", Ok(Op::Rpc("1".into(), "2".into()))),
            ("12=>3", Ok(Op::Rpc("12".into(), "3".into()))),
            ("123=>45", Ok(Op::Rpc("123".into(), "45".into()))),
            ("1234=>567", Ok(Op::Rpc("1234".into(), "567".into()))),
        ];

        for &(ref input, ref output) in &test_cases {
            assert_eq!(input.parse::<Op>(), *output);
        }
    }

    #[test]
    fn parse_err() {
        let test_cases = [
            "a", "1a", "1+1", "1=>-1", "-1=>1", "<<1", "+1+1", "1=>", "=>1"
        ];

        for test_case in &test_cases {
            assert_eq!(test_case.parse::<Op>(), Err(()))
        }
    }
}
