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
    let mut args = env::args().skip(1).collect::<Vec<String>>();
    if args.len() > 1 {
        let var = args.remove(0).chars().nth(0);
        if let Some(var) = var {
            let expr = parse_expression(&args[0]);
            match expr {
                Some(expr) => println!("{}", expr.simplify().derive(var).simplify()),
                None => println!("Expression could not be parsed."),
            }
        } else {
            println!("Variable of differentiation should be at least one character.")
        }
    } else {
	println!("This program expects 2 arguments, the first a single character for the variable of differentiation, the second the expression you wish to differentiation. \ni.e. cargo run x \"x^x\"\nOnly first character of the first argument is taken.")
    }
}
