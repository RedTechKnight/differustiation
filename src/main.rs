#[cfg(test)]
mod test;

use expression::{Expression, Literal, Operator, Term};
use parser::parse_expression;
#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

mod expression;
mod parser;
use std::fs;
use std::io;
use std::io::prelude::*;
fn main() {
    let mut input = "x^5";
    let expr = parse_expression(input).unwrap();
    let one = Expression::integer_expression(1);
    let zero = Expression::integer_expression(0);
    let answer = expr.simplify().derive('x').simplify();
    println!("{}", answer);
    match texify(answer) {
        Ok(_) => println!("Great!"),
        _ => println!("Oh no!"),
    }
}

fn texify(expr: Expression) -> io::Result<()> {
    let mut output = fs::File::create("debug/debug.tex")?;
    output.write_all(b"\\documentclass{article}\n")?;
    output.write_all(b"\\begin{document}\n \\(")?;
    output.write_all(expr.into_tex().as_bytes())?;
    output.write_all(b"\\) \\end{document}")
}
