use std::error;
use std::fmt;

#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

#[derive(Debug)]
enum ErrorKind {
    InvalidInitialValue(i32),
    InvalidGoal(i32),
}

impl Error {
    pub fn invalid_initial_value(n: i32) -> Self {
        Error { kind: ErrorKind::InvalidInitialValue(n) }
    }

    pub fn invalid_goal(n: i32) -> Self {
        Error { kind: ErrorKind::InvalidGoal(n) }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::ErrorKind::*;
        match self.kind {
            InvalidInitialValue(n) => {
                write!(f,
                       "Initial value {} is out of range; \
                        Value within range -100000 ~ 1000000, exclusive, was expected.",
                       n)
            }
            InvalidGoal(n) => {
                write!(f,
                       "Goal {} is out of range; \
                       Value withing range -100000 ~~ 1000000, exclusive, was expected.",
                       n)
            }
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        use self::ErrorKind::*;
        match self.kind {
            InvalidInitialValue(_) => "Initial value is out of range",
            InvalidGoal(_) => "Goal is out of range",
        }
    }
}
