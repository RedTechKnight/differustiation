use crate::expression::{Expression, Literal, Operator, Term};
use std::collections::HashMap;
use std::iter::Peekable;
pub fn parse_expression(input: &str) -> Result<Expression, String> {
    let tokens = tokenise(&mut input.chars().peekable());
    parse_binary(&mut tokens.into_iter().peekable(), 0)
}
#[derive(Debug, Clone, PartialEq)]
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
    let token_map = vec![
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
                output.push(token_map[&chr].clone())
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
            let inner_expr = parse_binary(input, 0)?;
            match input.next() {
                Some(Token::RParen) => Ok(Expression::Unary(Operator::Paren, Box::new(inner_expr))),
                Some(other) => Err(format!("Expected ')', found {:?}", other)),
                None => Err(format!("Expecteed ')', reached end of input")),
            }
        }
        Some(Token::Num(lit)) => Ok(Expression::Lit(Term::Numeric(lit))),
        Some(Token::Var(v)) => Ok(Expression::Lit(Term::Variable(v))),
        Some(Token::Fun(f)) => match input.next() {
            Some(Token::LParen) => {
                let operand = parse_binary(input, 0)?;
                match input.next() {
                    Some(Token::RParen) => {
                        Ok(Expression::Unary(Operator::Custom(f), Box::new(operand)))
                    }
                    Some(other) => Err(format!(
                        "Expected ')' at end of function expression, found {:?}",
                        other
                    )),
                    None => Err(format!(
                        "Expected ')' at end of function expression, reached end of input."
                    )),
                }
            }
            Some(other) => Err(format!(
                "Expected '(' after function name, found {:?}",
                other
            )),
            None => Err(format!(
                "Expected '(' after function name, reached end of input"
            )),
        },
        other => Err(format!("Unexpected token: {:?}", other)),
    }
}

fn parse_unary<I: Iterator<Item = Token>>(input: &mut Peekable<I>) -> Result<Expression, String> {
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

fn parse_binary_right_assoc<I: Iterator<Item = Token>>(
    input: &mut Peekable<I>,
) -> Result<Expression, String> {
    let lhs = parse_unary(input)?;
    match input.peek() {
        Some(Token::Exp) => {
            input.next();
            let rhs = parse_binary_right_assoc(input)?;
            Ok(Expression::Binary(
                Operator::Exp,
                Box::new(lhs),
                Box::new(rhs),
            ))
        }
        _ => Ok(lhs),
    }
}

fn left_assoc<I: Iterator<Item = Token>>(
    lhs: Expression,
    input: &mut Peekable<I>,
    precedence: i32,
) -> Result<Expression, String> {
    let operators = vec![
        (0, vec![Token::Plus, Token::Minus]),
        (1, vec![Token::Mul, Token::Div]),
    ]
    .into_iter()
    .collect::<HashMap<i32, Vec<Token>>>();
    let op = |tok: Token| match tok {
        Token::Plus => Operator::Add,
        Token::Minus => Operator::Sub,
        Token::Mul => Operator::Mul,
        _ => Operator::Div,
    };
    match input.peek().cloned() {
        Some(tok) if operators[&precedence].contains(&tok) => {
            input.next();
            let rhs = if precedence == 0 {
                parse_binary(input, precedence + 1)?
            } else {
                parse_binary_right_assoc(input)?
            };
            left_assoc(
                Expression::Binary(op(tok), Box::new(lhs), Box::new(rhs)),
                input,
                precedence,
            )
        }
        _ => Ok(lhs),
    }
}

fn parse_binary<I: Iterator<Item = Token>>(
    input: &mut Peekable<I>,
    precedence: i32,
) -> Result<Expression, String> {
    let lhs = if precedence == 0 {
        parse_binary(input, precedence + 1)?
    } else {
        parse_binary_right_assoc(input)?
    };
    left_assoc(lhs, input, precedence)
}
