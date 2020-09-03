use crate::expression::{Expression, Literal, Operator, Term};
use anyhow::anyhow;
use nom::branch::alt;
use nom::character::complete::{alpha1, char, digit1, one_of, space0};
use nom::combinator::{all_consuming, flat_map, map, verify};
use nom::error::ErrorKind;
use nom::error::ParseError;
use nom::multi::many1;
use nom::sequence::{delimited, pair, preceded, separated_pair, tuple};
use nom::IResult;

pub fn parse_expression(input: &str) -> anyhow::Result<Expression> {
    match tokenise(input) {
        Ok((_, tokens)) => match all_consuming(parse_binary(0))(&tokens) {
            Ok((_, expr)) => Ok(expr),
            Err(err) => Err(anyhow!("Error during parsing expression: {}", err)),
        },
        Err(err) => Err(anyhow!("Error tokenising input: {}", err)),
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

fn get_token(c: char) -> Token {
    match c {
        '+' => Token::Plus,
        '-' => Token::Minus,
        '/' => Token::Div,
        '*' => Token::Mul,
        '^' => Token::Exp,
        '(' => Token::LParen,
        ')' => Token::RParen,
        _ => Token::Plus,
    }
}

fn tokenise(input: &str) -> IResult<&str, Vec<Token>> {
    let operator = ws(map(one_of("+-*/()^"), get_token));
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

fn next<'a, T: 'a + Clone>(input: &[T]) -> IResult<&[T], T> {
    if input.is_empty() {
        Err(nom::Err::Error((input, ErrorKind::Eof)))
    } else {
        Ok((&input[1..], input[0].clone()))
    }
}

fn pure<'a, T: 'a + Clone, U>(x: &'a T) -> impl Fn(&[U]) -> IResult<&[U], T> + 'a {
    move |input: &[U]| Ok((input, x.clone()))
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
        |(tok, arg)| match tok {
            Token::Fun(f) => Expression::Unary(Operator::Custom(f), Box::new(arg)),
            _ => Expression::integer_expression(0),
        },
    );
    alt((paren, fun, num, var))(input)
}

fn parse_unary(input: &[Token]) -> IResult<&[Token], Expression> {
    let negation = map(
        preceded(verify(next, |x| matches!(x, Token::Minus)), parse_unary),
        |expr| Expression::Unary(Operator::Neg, Box::new(expr)),
    );
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

fn higher_expr(prec: i32) -> impl Fn(&[Token]) -> IResult<&[Token], Expression> {
    move |input: &[Token]| {
        if prec == 0 {
            parse_binary(prec + 1)(input)
        } else {
            parse_binary_right_assoc(input)
        }
    }
}

fn get_op(token: &Token) -> Operator {
    match token {
        Token::Plus => Operator::Add,
        Token::Minus => Operator::Sub,
        Token::Mul => Operator::Mul,
        Token::Div => Operator::Div,
        Token::Exp => Operator::Exp,
        _ => Operator::Add,
    }
}

fn expected_op(prec: i32, token: &Token) -> bool {
    if prec == 0 {
        matches!(token, Token::Plus | Token::Minus)
    } else {
        matches!(token, Token::Mul | Token::Div)
    }
}

fn left_assoc(
    (lhs, prec): (Expression, i32),
) -> impl Fn(&[Token]) -> IResult<&[Token], Expression> {
    move |input: &[Token]| {
        let expr = map(
            tuple((
                pure(&lhs),
                verify(next, |x| expected_op(prec, &x)),
                higher_expr(prec),
            )),
            |(lhs, op, rhs)| Expression::Binary(get_op(&op), Box::new(lhs), Box::new(rhs)),
        );
        let recurse = flat_map(map(expr, |res| (res, prec)), left_assoc);
        alt((recurse, pure(&lhs)))(input)
    }
}

fn binary_expr(prec: i32) -> impl Fn(&[Token]) -> IResult<&[Token], Expression> {
    move |input: &[Token]| {
        map(
            tuple((
                higher_expr(prec),
                verify(next, |x| expected_op(prec, x)),
                higher_expr(prec),
            )),
            |(lhs, op, rhs)| Expression::Binary(get_op(&op), Box::new(lhs), Box::new(rhs)),
        )(input)
    }
}

fn parse_binary(prec: i32) -> impl Fn(&[Token]) -> IResult<&[Token], Expression> {
    move |input: &[Token]| {
        alt((
            flat_map(map(binary_expr(prec), |res| (res, prec)), left_assoc),
            higher_expr(prec),
        ))(input)
    }
}
