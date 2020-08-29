use crate::expression::{Expression, Literal, Operator, Term};
use std::collections::HashMap;
use std::iter::Peekable;
pub fn parse_expression(input: &str) -> Result<Expression,String> {
    let tokens = tokenise(&mut input.chars().peekable());
    parse_add(&mut tokens.into_iter().peekable())
}
#[derive(Debug)]
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

fn parse_primary<I: Iterator<Item = Token>>(input: &mut Peekable<I>) -> Result<Expression, String> {
    match input.next() {
        Some(Token::LParen) => {
            let inner_expr = parse_add(input)?;
            match input.next() {
                Some(Token::RParen) => Ok(Expression::Unary(Operator::Paren, Box::new(inner_expr))),
                Some(other) => Err(format!("Expected ')', found {:?}", other)),
            }
        }
        Some(Token::Num(lit)) => Ok(Expression::Lit(Term::Numeric(lit))),
        Some(Token::Var(v)) => Ok(Expression::Lit(Term::Variable(v))),
        Some(Token::Fun(f)) => match input.next() {
            Some(Token::LParen) => {
                let operand = parse_add(input)?;
                match input.next() {
                    Some(Token::RParen) => {
                        Ok(Expression::Unary(Operator::Custom(f), Box::new(operand)))
                    }
                    Some(other) => Err(format!(
                        "Expected ')' at end of function expression, found {:?}",
                        other
                    )),
                }
            }
            Some(other) => Err(format!(
                "Expected '(' after function name, found {:?}",
                other
            )),
        },
        other => Err(format!("Unexpected token: {:?}",other)),
    }
}

fn parse_unary<I: Iterator<Item = Token>>(input: &mut Peekable<I>) -> Result<Expression,String> {
    match input.peek() {
        Some(Token::Minus) => {
            input.next();
            let operand = parse_unary(input)?;
            Ok(Expression::Unary(Operator::Neg, Box::new(operand)))
        }
        Some(_) => parse_primary(input),
        None => Err(format!("Expected unary expression, reached end of input.")),
    }
}

fn parse_exp<I: Iterator<Item = Token>>(input: &mut Peekable<I>) -> Result<Expression,String> {
    let lhs = parse_unary(input)?;
    match input.peek() {
        Some(Token::Exp) => {
            input.next();
            let rhs = parse_exp(input)?;
            Ok(Expression::Binary(
                Operator::Exp,
                Box::new(lhs),
                Box::new(rhs),
            ))
        }
        _ => Ok(lhs),
    }
}

fn left_assoc_mul<I: Iterator<Item = Token>>(
    lhs: Expression,
    input: &mut Peekable<I>,
) -> Result<Expression,String> {
    match input.peek() {
        Some(Token::Mul) => {
            input.next();
            let rhs = parse_exp(input)?;

            left_assoc_mul(
                Expression::Binary(Operator::Mul, Box::new(lhs), Box::new(rhs)),
                input,
            )
        }
        Some(Token::Div) => {
            input.next();
            let rhs = parse_exp(input)?;
            left_assoc_mul(
                Expression::Binary(Operator::Div, Box::new(lhs), Box::new(rhs)),
                input,
            )
        }
        _ => Ok(lhs),
    }
}

fn parse_mul<I: Iterator<Item = Token>>(input: &mut Peekable<I>) -> Result<Expression,String> {
    let lhs = parse_exp(input)?;
    left_assoc_mul(lhs, input)
}

fn left_assoc_add<I: Iterator<Item = Token>>(
    lhs: Expression,
    input: &mut Peekable<I>,
) -> Result<Expression,String> {
    match input.peek() {
        Some(Token::Plus) => {
            input.next();
            let rhs = parse_mul(input)?;
            left_assoc_add(
                Expression::Binary(Operator::Add, Box::new(lhs), Box::new(rhs)),
                input,
            )
        }
        Some(Token::Minus) => {
            input.next();
            let rhs = parse_mul(input)?;
            left_assoc_add(
                Expression::Binary(Operator::Sub, Box::new(lhs), Box::new(rhs)),
                input,
            )
        }
        _ => Ok(lhs),
    }
}
fn parse_add<I: Iterator<Item = Token>>(input: &mut Peekable<I>) -> Result<Expression,String> {
    let lhs = parse_mul(input)?;
    left_assoc_add(lhs, input)
}
