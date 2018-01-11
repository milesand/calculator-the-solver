#![feature(option_filter)]

#[macro_use]
extern crate lazy_static;
extern crate regex;

mod op;
pub use op::Op;

mod error;
pub use error::Error;

pub fn run(initial: i32, goal: i32, moves: usize, ops: &[Op]) -> Result<Option<Vec<&Op>>, Error> {
    if initial <= -100000 || 1000000 <= initial {
        return Err(Error::invalid_initial_value(initial));
    }
    if goal <= -100000 || 1000000 <= goal {
        return Err(Error::invalid_goal(goal));
    }

    let mut path = vec![];

    if solve(initial, goal, moves, ops, &mut path) {
        Ok(Some(path))
    } else {
        Ok(None)
    }
}

fn solve<'a: 'b, 'b>(n: i32,
                     goal: i32,
                     moves: usize,
                     ops: &'a [Op],
                     path: &'b mut Vec<&'a Op>)
                     -> bool {
    if n == goal {
        return true;
    }
    if path.len() == moves {
        return false;
    }
    for op in ops.iter() {
        let next = op.apply(n);
        match next {
            None => continue,
            Some(next) => {
                path.push(op);
                if solve(next, goal, moves, ops, path) {
                    return true;
                }
                path.pop();
            }
        }
    }
    return false;
}
