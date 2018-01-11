extern crate lib;

use std::io;
use std::io::prelude::*;

use lib::Op;

fn get_input<I: BufRead, O: Write>(i: &mut I, o: &mut O, msg: &[u8]) -> Result<String, io::Error> {
    o.write(msg)?;
    o.flush()?;

    let mut buf = String::new();
    i.read_line(&mut buf)?;
    Ok(buf)
}

fn get_initial_n<I: BufRead, O: Write>(i: &mut I, o: &mut O) -> Result<i32, io::Error> {
    loop {
        let input = get_input(i, o, b"Input n: ")?;
        if let Ok(n) = input.trim().parse() {
            if -100000 < n && n < 1000000 {
                return Ok(n);
            }
        }
    }
}

fn get_moves<I: BufRead, O: Write>(i: &mut I, o: &mut O) -> Result<usize, io::Error> {
    loop {
        let input = get_input(i, o, b"Input moves: ")?;
        if let Ok(n) = input.trim().parse() {
            return Ok(n);
        }
    }
}

fn get_goal<I: BufRead, O: Write>(i: &mut I, o: &mut O) -> Result<i32, io::Error> {
    loop {
        let input = get_input(i, o, b"Input goal: ")?;
        if let Ok(n) = input.trim().parse() {
            if -100000 < n && n < 1000000 {
                return Ok(n);
            }
        }
    }
}

fn get_ops<I: BufRead, O: Write>(i: &mut I, o: &mut O) -> Result<Vec<Op>, io::Error> {
    loop {
        let input = get_input(i, o, b"Input ops: ")?;
        if let Ok(ops) = input.trim()
               .split_whitespace()
               .map(|s| s.parse())
               .collect() {
            return Ok(ops);
        }
    }
}


fn main() {
    let stdin = io::stdin();
    let mut stdin = stdin.lock();

    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    let initial = get_initial_n(&mut stdin, &mut stdout).expect("IO Error");
    let goal = get_goal(&mut stdin, &mut stdout).expect("IO Error");
    let moves = get_moves(&mut stdin, &mut stdout).expect("IO Error");
    let ops = get_ops(&mut stdin, &mut stdout).expect("IO Error");

    match lib::run(initial, goal, moves, &ops) {
        Ok(Some(path)) => {
            write!(stdout, "Path found:").expect("IO Error");
            for op in path.iter() {
                write!(stdout, " {}", op).expect("IO Error");
            }
            write!(stdout, "\n").expect("IO Error");
        }
        Ok(None) => {
            write!(stdout, "Path not found\n").expect("IO Error");
        }
        Err(e) => {
            write!(stdout, "Internal Error: {}", e).expect("IO Error");
        }
    }
}
