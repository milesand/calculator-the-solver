use regex::Regex;

use std::fmt;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Add(i32),
    Mul(i32),
    Div(i32),
    Del,
    Ins(String),
    Rpc(String, String),
}

impl Op {
    pub fn apply(&self, n: i32) -> Option<i32> {
        use self::Op::{Del, Add, Rpc, Div, Ins, Mul};
        match *self {
                Add(m) => Some(m + n),
                Mul(m) => Some(m * n),
                Div(m) => if n % m == 0 { Some(n / m) } else { None },
                Del => Some((n.abs() / 10) * n.signum()),
                Ins(ref s) => {
                    let mut n = n.to_string();
                    n.push_str(s);
                    Some(s.parse().unwrap())
                }
                Rpc(ref from, ref to) => {
                    Some(n.to_string()
                             .replace(from, to)
                             .parse()
                             .unwrap())
                }
            }
            .filter(|n| -100000 < *n && *n < 1000000)
    }
}

impl FromStr for Op {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use self::Op::{Del, Add, Rpc, Div, Ins, Mul};
        lazy_static! {
            static ref RPC_PATTERN: Regex = Regex::new(r"(\d+)=>(\d+)").unwrap();
        }
        if s == "<<" {
            Ok(Del)
        } else if s.starts_with('-') {
            s.parse().map(Add).map_err(|_| ())
        } else if s.starts_with('+') {
            s[1..].parse().map(Add).map_err(|_| ())
        } else if s.starts_with('*') {
            s[1..].parse().map(Mul).map_err(|_| ())
        } else if s.starts_with('/') {
            s[1..].parse().map(Div).map_err(|_| ())
        } else if s.bytes().all(|b| b'0' <= b && b <= b'9') {
            Ok(Ins(s.to_string()))
        } else if let Some(captures) = RPC_PATTERN.captures(s) {
            Ok(Rpc(captures.get(1)
                       .unwrap()
                       .as_str()
                       .to_string(),
                   captures.get(2)
                       .unwrap()
                       .as_str()
                       .to_string()))
        } else {
            Err(())
        }
    }
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::Op::{Del, Add, Rpc, Div, Ins, Mul};
        match *self {
            Add(n) => {
                if n >= 0 {
                    write!(f, "+{}", n)
                } else {
                    write!(f, "{}", n)
                }
            }
            Mul(n) => write!(f, "*{}", n),
            Div(n) => write!(f, "/{}", n),
            Del => write!(f, "<<"),
            Ins(ref s) => write!(f, "{}", s),
            Rpc(ref from, ref to) => write!(f, "{}=>{}", from, to),
        }
    }
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
            "a",
            "1a",
            "1+1",
            "1=>-1",
            "-1=>1",
            "<<1",
            "+1+1",
            "1=>",
            "=>1",
        ];
        
        for test_case in &test_cases {
            assert_eq!(test_case.parse::<Op>(), Err(()))
        }
    }
}
