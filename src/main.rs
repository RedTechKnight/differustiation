#[cfg(test)]
mod test;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

mod expression;
mod parser;
use parser::parse_expression;
use std::env;

fn main() {
    let input = env::args().skip(1).take(1).collect::<String>();
    let expr = parse_expression(&input).unwrap();
    let answer = expr.simplify().derive('x').simplify();
    println!("{}", answer);
}
