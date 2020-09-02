use crate::expression::{Expression, Literal, Operator, Term};
use anyhow::anyhow;
use nom::branch::alt;
use nom::character::complete::{alpha1, char, digit1, one_of, space0};
use nom::combinator::{map, verify,flat_map};
use nom::error::ErrorKind;
use nom::error::{ParseError};
use nom::multi::many1;
use nom::sequence::{delimited, pair, preceded, separated_pair, tuple};
use nom::IResult;
use std::collections::HashMap;

pub fn parse_expression(input: &str) -> Result<Expression, anyhow::Error> {
    match parse_binary(0)(&tokenise(input).unwrap().1) {
        Ok((_, res)) => Ok(res),
        Err(e) => Err(anyhow!("{}", e)),
    }
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

fn ws<'a, F: 'a, O, E: ParseError<&'a str>>(inner: F) -> impl Fn(&'a str) -> IResult<&'a str, O, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O, E>,
{
    delimited(space0, inner, space0)
}

fn tokenise(input: &str) -> IResult<&str, Vec<Token>> {
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

    let operator = ws(map(one_of("+-*/()^"), move |x: char| token_map[&x].clone()));
    let float = map(ws(separated_pair(digit1, char('.'), digit1)), |x| {
        Token::Num(Literal::Real(format!("{}.{}", x.0, x.1).parse().unwrap()))
    });
    let int = map(ws(digit1), |x| {
        Token::Num(Literal::Integer(x.parse().unwrap()))
    });
    let number = alt((float, int));
    let var_fun = ws(map(alpha1, |x: &str| {
        if x.len() == 1 {
            Token::Var(x.chars().next().unwrap())
        } else {
            Token::Fun(x.to_string())
        }
    }));
    many1(alt((operator, number, var_fun)))(input)
}

fn next<'a, T: 'a + Clone + std::fmt::Debug>(input: &[T]) -> IResult<&[T], T> {
    if input.is_empty() {
        Err(nom::Err::Error((input, ErrorKind::Eof)))
    } else {
        Ok((&input[1..], input[0].clone()))
    }
}

fn paren(input: &[Token]) -> IResult<&[Token], Expression> {
    delimited(
        verify(next, |x| matches!(x, Token::LParen)),
        parse_binary(0),
        verify(next, |x| matches!(x, Token::RParen)),
    )(input)
}

fn parse_primary(input: &[Token]) -> IResult<&[Token], Expression> {
    let num = map(verify(next, |x| matches!(x, Token::Num(_))), |x| match x {
        Token::Num(n) => Expression::Lit(Term::Numeric(n)),
        _ => Expression::integer_expression(0),
    });
    let var = map(verify(next, |x| matches!(x, Token::Var(_))), |x| match x {
        Token::Var(v) => Expression::Lit(Term::Variable(v)),
        _ => Expression::integer_expression(0),
    });
    let fun = map(
        pair(verify(next, |x| matches!(x, Token::Fun(_))), paren),
        |(fun_tok, arg_expr)| match fun_tok {
            Token::Fun(f) => Expression::Unary(Operator::Custom(f), Box::new(arg_expr)),
            _ => Expression::integer_expression(0),
        },
    );
    alt((paren, fun, num, var))(input)
}

fn parse_unary(input: &[Token]) -> IResult<&[Token], Expression> {
    let negation = preceded(verify(next, |x| matches!(x, Token::Minus)), parse_unary);
    alt((negation, parse_primary))(input)
}

fn parse_binary_right_assoc(input: &[Token]) -> IResult<&[Token], Expression> {
    let expr = map(
        separated_pair(
            parse_unary,
            verify(next, |x| matches!(x, Token::Exp)),
            parse_binary_right_assoc,
        ),
        |(lhs, rhs)| Expression::Binary(Operator::Exp, Box::new(lhs), Box::new(rhs)),
    );
    alt((expr, parse_unary))(input)
}

fn next_op(prec: i32) -> impl Fn(&[Token]) -> IResult<&[Token], Expression> {
    move |input: &[Token]| {
        if prec == 0 {
            parse_binary(prec + 1)(input)
        } else {
            parse_binary_right_assoc(input)
        }
    }
}

fn assoc((lhs,prec) : (Expression,i32)) -> impl Fn(&[Token]) -> IResult<&[Token],Expression> {
    move |input: &[Token]| {
	let get_op = |token: Token| match token {
        Token::Plus => Operator::Add,
        Token::Minus => Operator::Sub,
        Token::Mul => Operator::Mul,
        Token::Div => Operator::Div,
        _ => panic!(),
    };
    let bin_op = |prec: i32| match prec {
        0 => vec![Token::Plus, Token::Minus],
        1 => vec![Token::Mul, Token::Div],
        _ => vec![],
    };
	let expr = 
	map(
            tuple((
                |input| Ok((input,lhs.clone())),
                verify(next, |x| matches!(x, x if bin_op(prec).contains(&x))),
                next_op(prec),
            )),
            |(lhs, op, rhs)| Expression::Binary(get_op(op), Box::new(lhs), Box::new(rhs)),
        );
	let recurse = flat_map(map(expr,|res| (res,prec)),assoc);
	let x = alt((recurse,|input| Ok((input,lhs.clone()))))(input);
	x
    }
}

fn bin_expr(prec: i32) -> impl Fn(&[Token]) -> IResult<&[Token], Expression> {
    let get_op = |token: Token| match token {
        Token::Plus => Operator::Add,
        Token::Minus => Operator::Sub,
        Token::Mul => Operator::Mul,
        Token::Div => Operator::Div,
        _ => panic!(),
    };
    let bin_op = |prec: i32| match prec {
        0 => vec![Token::Plus, Token::Minus],
        1 => vec![Token::Mul, Token::Div],
        _ => vec![],
    };
    move |input: &[Token]| {
        map(
            tuple((
                next_op(prec),
                verify(next, |x| matches!(x, x if bin_op(prec).contains(&x))),
                next_op(prec),
            )),
            |(lhs, op, rhs)| Expression::Binary(get_op(op), Box::new(lhs), Box::new(rhs)),
        )(input)
    }
}

fn parse_binary(prec: i32) -> impl Fn(&[Token]) -> IResult<&[Token], Expression> {
    move |input: &[Token]| alt((flat_map(map(bin_expr(prec),|res| (res,prec)),assoc),next_op(prec)))(input)
}
