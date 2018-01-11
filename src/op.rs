use regex::Regex;

use std::fmt;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Add(i32),
    Mul(i32),
    Div(i32),
    Del,
    Ins(i32),
    Rpc(String, String),
}

impl Op {
    pub fn apply(&self, n: i32) -> Option<i32> {
        use self::Op::*;
        match *self {
                Add(m) => Some(m + n),
                Mul(m) => Some(m * n),
                Div(m) => if n % m == 0 { Some(n / m) } else { None },
                Del => Some((n.abs() / 10) * n.signum()),
                Ins(m) => {
                    let mut pow_of_ten = 10;
                    while pow_of_ten <= m {
                        pow_of_ten *= 10;
                    }
                    Some((n.abs() * pow_of_ten + m) * if n < 0 { -1 } else { 1 })
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
        use self::Op::*;
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
        } else if let Ok(n) = s.parse() {
            Ok(Ins(n))
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
        use self::Op::*;
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
            Ins(n) => write!(f, "{}", n),
            Rpc(ref from, ref to) => write!(f, "{}=>{}", from, to),
        }
    }
}
