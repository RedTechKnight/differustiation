#[cfg(test)]
mod test;

mod expression;
mod parser;
use clap::{App, Arg};
use parser::parse_expression;
fn main() {
    let matches = setup_arg_parser().get_matches();
    let wrt = matches.value_of("var").unwrap().chars().next().unwrap();
    let expr_str = matches.value_of("expression").unwrap();
    let expr = parse_expression(expr_str);
    match expr {
        Ok(expr) => println!("{}", expr.simplify().derive(wrt).present()),
        Err(err) => println!("{:?}", err),
    }
}

fn single_char(val: String) -> Result<(), String> {
    if val.len() > 1 {
        Err("Variable of differentiation must be a single character".to_string())
    } else {
        Ok(())
    }
}

fn setup_arg_parser<'a>() -> App<'a, 'a> {
    App::new("differustiation")
        .version("0.1.0")
        .author("RedTechKnight <bloodtechknight@protonmail.com>")
        .about("Attempts to differentiate mathematical expressions")
        .arg(
            Arg::with_name("var")
                .required(true)
                .help("The variable of differentiation.")
                .validator(single_char),
        )
        .arg(
            Arg::with_name("expression")
                .required(true)
                .help("The expression to differentiate."),
        )
}
