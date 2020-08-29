use crate::expression::{Expression, Literal, Operator};
use std::collections::HashMap;
use std::iter::Peekable;
pub fn parse_expression(input: &str) -> Option<Expression> {
    let tokens = tokenise(&mut input.chars().peekable());
    parse_add(&mut tokens.into_iter().peekable())
}
enum Token {
    Plus,
    Minus,
    Div,
    Mul,
    Exp,
    LParen,
    RParen,
    Num(Literal),
    Var(char),
    Fun(String),
}

fn tokenise<I: Iterator<Item = char>>(input: &mut Peekable<I>) -> Vec<Token> {
    let mut output = Vec::new();
    let mut token_map = vec![
        ('+', Token::Plus),
        ('-', Token::Minus),
        ('/', Token::Div),
        ('*', Token::Mul),
        ('^', Token::Exp),
        ('(', Token::LParen),
        (')', Token::RParen),
    ]
    .into_iter()
    .collect::<HashMap<char, Token>>();
    while let Some(chr) = input.next() {
        match chr {
            chr if ['+', '-', '/', '*', '^', '(', ')'].contains(&chr) => {
                output.push(token_map[&chr])
            }
            chr if chr.is_digit(10) => {
                let mut num = String::new();
                let mut period = false;
                num.push(chr);
                while let Some(chr) = input.peek() {
                    if chr.is_digit(10) {
                        num.push(input.next().unwrap())
                    } else if !period && chr.eq(&'.') {
                        num.push(input.next().unwrap());
                        period = true;
                    } else {
                        break;
                    }
                }
                if let Ok(num) = num.parse::<i128>() {
                    output.push(Token::Num(Literal::Integer(num)))
                } else if let Ok(num) = num.parse::<f64>() {
		    output.push(Token::Num(Literal::Real(num)))
		}
            }
            chr if chr.is_alphabetic() => {
                let mut word = String::new();
                word.push(chr);
                while let Some(chr) = input.peek() {
                    if chr.is_alphabetic() {
                        word.push(input.next().unwrap())
                    } else {
                        break;
                    }
                }
                if word.len() == 1 {
		    output.push(Token::Var(word.remove(0)))
		} else {
		    output.push(Token::Fun(word))
		}
            }
            chr if [' '].contains(&chr) => (),
            _ => (),
        }
    }
    output
}

fn parse_primary<I: Iterator<Item = String>>(input: &mut Peekable<I>) -> Option<Expression> {
    Some(match input.next() {
        Some(token) if token == "(" => {
            let inner_expr = parse_add(input)?;
            match input.next() {
                Some(tok) if tok == ")" => Expression::Unary(Operator::Paren, Box::new(inner_expr)),
                _ => panic!("No closing parenthesis to match opening."),
            }
        }
        Some(tok) if tok.chars().all(char::is_alphabetic) && tok.len() > 1 => match input.next() {
            Some(next) if next == "(" => {
                let inner_expr = parse_add(input)?;
                match input.next() {
                    Some(next) if next == ")" => {
                        Expression::Unary(Operator::Custom(tok), Box::new(inner_expr))
                    }
                    _ => panic!("No closing parenthessi to match opening paren."),
                }
            }
            _ => panic!("Expected opening parenthesis for mathematical functions!"),
        },
        Some(mut tok) => match tok.parse::<i128>() {
            Ok(succ) => Expression::integer_expression(succ),
            _ => match tok.parse::<f64>() {
                Ok(succ) => Expression::real_expression(succ),
                _ => Expression::variable_expression(tok.remove(0)),
            },
        },
        _ => panic!("EOF reached."),
    })
}

fn parse_unary<I: Iterator<Item = String>>(input: &mut Peekable<I>) -> Option<Expression> {
    match input.peek() {
        Some(tok) if tok == "-" => {
            input.next();
            let operand = parse_unary(input)?;
            Some(Expression::Unary(Operator::Neg, Box::new(operand)))
        }
        Some(_) => parse_primary(input),
        None => None,
    }
}

fn parse_exp<I: Iterator<Item = String>>(input: &mut Peekable<I>) -> Option<Expression> {
    let lhs = parse_unary(input)?;
    match input.peek() {
        Some(tok) if tok == "^" => {
            input.next();
            let rhs = parse_exp(input)?;
            Some(Expression::Binary(
                Operator::Exp,
                Box::new(lhs),
                Box::new(rhs),
            ))
        }
        _ => Some(lhs),
    }
}

fn left_assoc_mul<I: Iterator<Item = String>>(
    lhs: Expression,
    input: &mut Peekable<I>,
) -> Option<Expression> {
    match input.peek() {
        Some(tok) if tok == "*" => {
            input.next();
            let rhs = parse_exp(input)?;

            left_assoc_mul(
                Expression::Binary(Operator::Mul, Box::new(lhs), Box::new(rhs)),
                input,
            )
        }
        Some(tok) if tok == "/" => {
            input.next();
            let rhs = parse_exp(input)?;
            left_assoc_mul(
                Expression::Binary(Operator::Div, Box::new(lhs), Box::new(rhs)),
                input,
            )
        }
        _ => Some(lhs),
    }
}

fn parse_mul<I: Iterator<Item = String>>(input: &mut Peekable<I>) -> Option<Expression> {
    let lhs = parse_exp(input)?;
    left_assoc_mul(lhs, input)
}

fn left_assoc_add<I: Iterator<Item = String>>(
    lhs: Expression,
    input: &mut Peekable<I>,
) -> Option<Expression> {
    match input.peek() {
        Some(tok) if tok == "+" => {
            input.next();
            let rhs = parse_mul(input)?;
            left_assoc_add(
                Expression::Binary(Operator::Add, Box::new(lhs), Box::new(rhs)),
                input,
            )
        }
        Some(tok) if tok == "-" => {
            input.next();
            let rhs = parse_mul(input)?;
            left_assoc_add(
                Expression::Binary(Operator::Sub, Box::new(lhs), Box::new(rhs)),
                input,
            )
        }
        _ => Some(lhs),
    }
}
fn parse_add<I: Iterator<Item = String>>(input: &mut Peekable<I>) -> Option<Expression> {
    let lhs = parse_mul(input)?;
    left_assoc_add(lhs, input)
}
