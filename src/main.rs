use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::io;
use std::io::prelude::*;
#[cfg(test)]
mod test;
#[cfg(test)]
    extern crate quickcheck;
    #[cfg(test)]
    #[macro_use(quickcheck)]
    extern crate quickcheck_macros;
fn main() {

    let input = "a - b * c - das(10 + 6) / 86 ^ (-221) ^ (.1123123 + 2 * 3)".chars();
    let mut tokens = tokenise(&mut input.peekable()).into_iter().peekable();
    let expr = parse_add(&mut tokens).unwrap();
    texify(expr);
}

fn texify(expr: Expression) -> io::Result<()> {
    let mut output = fs::File::create("debug/debug.tex")?;
    output.write_all(b"\\documentclass{article}\n")?;
    output.write_all(b"\\begin{document}\n \\(")?;
    output.write_all(expr.as_tex().as_bytes())?;
    output.write_all(b"\\) \\end{document}")
}

fn texify_test(expr: Expression) -> io::Result<()> {
    let mut options = fs::OpenOptions::new();
    options.create(true);
    options.append(true);
    let mut output = options.open("debug/test.tex")?;
    output.write_all(b"\\[")?;
    output.write_all(expr.as_tex().as_bytes())?;
    output.write_all(b"\\]\n")
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
enum Literal {
    Integer(i128),
    Real(f64),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Literal::Integer(i) => i.to_string(),
                Literal::Real(fl) => fl.to_string(),
            }
        )
    }
}

impl Literal {
    fn new_real_literal(a: f64) -> Literal {
        Literal::Real(a)
    }

    fn new_integer_literal(a: i128) -> Literal {
        Literal::Integer(a)
    }

    fn as_integer(self) -> Literal {
        if let Literal::Real(a) = self {
            return Literal::Integer(a as i128);
        }
        self
    }

    fn get_integer(self) -> Option<i128> {
        match self {
            Literal::Integer(a) => Some(a),
            _ => None,
        }
    }

    fn _as_real(self) -> Literal {
        if let Literal::Integer(a) = self {
            return Literal::Real(a as f64);
        }
        self
    }
}
#[derive(Debug, Clone, Copy, PartialOrd, PartialEq)]
enum Term {
    Numeric(Literal),
    Variable(char),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Numeric(n) => write!(f, "{}", n),
            Term::Variable(c) => write!(f, "{}", c),
        }
    }
}

impl Term {
    fn from_string(mut input: String) -> Term {
        match input {
            mut input if input.chars().all(char::is_alphabetic) => Term::Variable(input.remove(0)),
            input if input.chars().all(char::is_numeric) => {
                Term::Numeric(Literal::Integer(input.parse().unwrap()))
            }
            _ => Term::real_term(0.0),
        }
    }
    fn real_term(a: f64) -> Term {
        Term::Numeric(Literal::new_real_literal(a))
    }

    fn integer_term(a: i128) -> Term {
        Term::Numeric(Literal::new_integer_literal(a))
    }

    fn variable_term(a: char) -> Term {
        Term::Variable(a)
    }

    fn as_tex(self) -> String {
        match self {
            Term::Numeric(Literal::Integer(i)) => i.to_string(),
            Term::Numeric(Literal::Real(r)) => r.to_string(),
            Term::Variable(c) => c.to_string(),
        }
    }
}
#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Ord)]
enum Operator {
    Paren,
    Neg,
    Add,
    Mul,
    Sub,
    Div,
    Exp,
    Custom(String),
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operator::Paren => write!(f, ""),
            Operator::Neg => write!(f, "-"),
            Operator::Add => write!(f, "+"),
            Operator::Mul => write!(f, "*"),
            Operator::Sub => write!(f, "-"),
            Operator::Div => write!(f, "/"),
            Operator::Exp => write!(f, "^"),
            Operator::Custom(string) => write!(f, "{}", string),
        }
    }
}

#[derive(Debug, Clone, PartialOrd, PartialEq)]
enum Expression {
    Lit(Term),
    Unary(Operator, Box<Expression>),
    Binary(Operator, Box<Expression>, Box<Expression>),
    Variadic(Operator, Vec<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Lit(t) => write!(f, "{}", t),
            Expression::Unary(op, a) => write!(f, "({} {})", op, *a),
            Expression::Binary(op, a, b) => write!(f, "({} {} {})", op, *a, *b),
            Expression::Variadic(op, exprs) => write!(
                f,
                "({} {})",
                op,
                exprs
                    .into_iter()
                    .map(|x| x.to_string() + " ")
                    .collect::<String>()
            ),
        }
    }
}

impl Expression {
    fn term_expression(t: Term) -> Expression {
        Expression::Lit(t)
    }
    fn variable_expression(a: char) -> Expression {
        Expression::Lit(Term::variable_term(a))
    }

    fn real_expression(a: f64) -> Expression {
        Expression::Lit(Term::real_term(a))
    }

    fn integer_expression(a: i128) -> Expression {
        Expression::Lit(Term::integer_term(a))
    }

    fn unary_expression(f: Operator, a: Expression) -> Expression {
        Expression::Unary(f, Box::new(a))
    }

    fn binary_expression(f: Operator, a: Expression, b: Expression) -> Expression {
        Expression::Binary(f, Box::new(a), Box::new(b))
    }

    fn variadic_expression(f: Operator, exprs: Vec<Expression>) -> Expression {
        Expression::Variadic(f, exprs)
    }

    fn get_binary_expression(self) -> Option<(Operator, Expression, Expression)> {
        if let Expression::Binary(f, a, b) = self {
            return Some((f, *a, *b));
        }
        None
    }
    fn recurse<F: Fn(Expression) -> Expression>(self, rec: F) -> Expression {
        match self {
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, rec(*a)),
            Expression::Binary(f, a, b) => Expression::binary_expression(f, rec(*a), rec(*b)),
            Expression::Variadic(f, exprs) => {
                Expression::variadic_expression(f, exprs.into_iter().map(rec).collect())
            }
        }
    }

    fn factor_out_neg(self) -> Expression {
        match self {
            Expression::Unary(Operator::Neg, a) => {
                return Expression::binary_expression(
                    Operator::Mul,
                    Expression::integer_expression(-1),
                    a.factor_out_neg(),
                );
            }
            other => other.recurse(Expression::factor_out_neg),
        }
    }

    fn factor_out_sub(self) -> Expression {
        match self {
            Expression::Binary(Operator::Sub, a, b) => {
                return Expression::binary_expression(
                    Operator::Add,
                    a.factor_out_sub(),
                    Expression::binary_expression(
                        Operator::Mul,
                        Expression::integer_expression(-1),
                        b.factor_out_sub(),
                    ),
                )
            }
            other => other.recurse(Expression::factor_out_sub),
        }
    }

    fn flatten_add(self) -> Expression {
        match self {
            Expression::Binary(Operator::Add, a, b) => match (a.flatten_add(), b.flatten_add()) {
                (
                    Expression::Variadic(Operator::Add, a),
                    Expression::Variadic(Operator::Add, b),
                ) => Expression::variadic_expression(
                    Operator::Add,
                    a.into_iter().chain(b.into_iter()).collect(),
                ),
                (Expression::Variadic(Operator::Add, a), b) => Expression::variadic_expression(
                    Operator::Add,
                    a.into_iter().chain(vec![b].into_iter()).collect(),
                ),
                (a, Expression::Variadic(Operator::Add, b)) => Expression::variadic_expression(
                    Operator::Add,
                    b.into_iter().chain(vec![a].into_iter()).collect(),
                ),
                (a, b) => Expression::Variadic(Operator::Add, vec![a, b]),
            },
            other => other.recurse(Expression::flatten_add),
        }
    }

    fn flatten_mul(self) -> Expression {
        match self {
            Expression::Binary(Operator::Mul, a, b) => match (a.flatten_mul(), b.flatten_mul()) {
                (
                    Expression::Variadic(Operator::Mul, a),
                    Expression::Variadic(Operator::Mul, b),
                ) => Expression::variadic_expression(
                    Operator::Mul,
                    a.into_iter().chain(b.into_iter()).collect(),
                ),
                (Expression::Variadic(Operator::Mul, a), b) => Expression::variadic_expression(
                    Operator::Mul,
                    a.into_iter().chain(vec![b].into_iter()).collect(),
                ),
                (a, Expression::Variadic(Operator::Mul, b)) => Expression::variadic_expression(
                    Operator::Mul,
                    b.into_iter().chain(vec![a].into_iter()).collect(),
                ),
                (a, b) => Expression::Variadic(Operator::Mul, vec![a, b]),
            },
            other => other.recurse(Expression::flatten_mul),
        }
    }

    fn simplify_rational_1(self) -> Expression {
        match self {
            Expression::Binary(Operator::Div, num, denom) => {
                match (num.simplify_rational_1(), denom.simplify_rational_1()) {
                    (Expression::Binary(Operator::Div, a_num, a_denom), denom) => {
                        Expression::binary_expression(
                            Operator::Div,
                            *a_num,
                            Expression::binary_expression(Operator::Mul, *a_denom, denom),
                        )
                    }
                    (a, b) => Expression::binary_expression(Operator::Div, a, b),
                }
            }
            other => other.recurse(Expression::simplify_rational_1),
        }
    }

    fn simplify_rational_2(self) -> Expression {
        match self {
            Expression::Binary(Operator::Div, num, denom) => {
                match (num.simplify_rational_2(), denom.simplify_rational_2()) {
                    (num, Expression::Binary(Operator::Div, b_num, b_denom)) => {
                        Expression::binary_expression(
                            Operator::Div,
                            Expression::binary_expression(Operator::Mul, num, *b_denom),
                            *b_num,
                        )
                    }
                    (a, b) => Expression::binary_expression(Operator::Div, a, b),
                }
            }
            other => other.recurse(Expression::simplify_rational_2),
        }
    }

    fn simplify_rational_3(self) -> Expression {
        match self {
            Expression::Binary(Operator::Mul, num, denom) => {
                match (num.simplify_rational_3(), denom.simplify_rational_3()) {
                    (num, Expression::Binary(Operator::Div, b_num, b_denom)) => {
                        Expression::binary_expression(
                            Operator::Div,
                            Expression::binary_expression(Operator::Mul, num, *b_num),
                            *b_denom,
                        )
                    }
                    (a, b) => Expression::binary_expression(Operator::Mul, a, b),
                }
            }
            Expression::Variadic(Operator::Mul, mut exprs) => {
                let first_div_node = exprs.iter().enumerate().find(|(_, v)| {
                    if let Expression::Binary(Operator::Div, _, _) = v {
                        return true;
                    }
                    return false;
                });
                match first_div_node {
                    Some(first_div_node) => {
                        let node = first_div_node.0;
                        let (_, num, denom) = exprs.remove(node).get_binary_expression().unwrap();
                        exprs.push(num);
                        Expression::binary_expression(
                            Operator::Div,
                            Expression::variadic_expression(Operator::Mul, exprs),
                            denom,
                        )
                    }
                    _ => Expression::variadic_expression(Operator::Mul, exprs),
                }
            }
            other => other.recurse(Expression::simplify_rational_3),
        }
    }

    fn explicit_exponents(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Mul, mut exprs) => {
                exprs = exprs
                    .into_iter()
                    .map(Expression::explicit_exponents)
                    .collect();
                for expr in exprs.iter_mut() {
                    match expr {
                        Expression::Binary(Operator::Exp, _, _) => (),
                        expr => {
                            let base = std::mem::replace(expr, Expression::integer_expression(1));
                            *expr = Expression::binary_expression(
                                Operator::Exp,
                                base,
                                Expression::integer_expression(1),
                            );
                        }
                    }
                }
                Expression::variadic_expression(Operator::Mul, exprs)
            }
            other => other.recurse(Expression::explicit_exponents),
        }
    }

    fn explicit_coefficients(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Add, mut exprs) => {
                exprs = exprs
                    .into_iter()
                    .map(Expression::explicit_coefficients)
                    .collect();
                for expr in exprs.iter_mut() {
                    match expr {
                        Expression::Binary(Operator::Mul, _, _) => (),
                        expr => {
                            let base = std::mem::replace(expr, Expression::integer_expression(1));
                            *expr = Expression::binary_expression(
                                Operator::Mul,
                                Expression::integer_expression(1),
                                base,
                            );
                        }
                    }
                }
                Expression::variadic_expression(Operator::Add, exprs)
            }
            other => other.recurse(Expression::explicit_coefficients),
        }
    }

    fn collect_like_muls(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Mul, mut exprs) => {
                let mut bases = Vec::new();
                for expr in &exprs {
                    match expr {
                        Expression::Binary(Operator::Exp, base, _) => {
                            if !bases.contains(base) {
                                bases.push((*base).clone())
                            }
                        }
                        _ => (),
                    }
                }
                let mut terms: Vec<(Expression, Vec<Expression>)> = bases
                    .iter()
                    .cloned()
                    .map(|x| *x)
                    .zip(std::iter::repeat(Vec::new()))
                    .collect();

                for term in &mut terms {
                    for expr in &mut exprs {
                        match expr {
                            Expression::Binary(Operator::Exp, base, exp) => {
                                if **base == term.0 {
                                    term.1.push(*exp.clone())
                                }
                            }
                            _ => (),
                        }
                    }
                }
                exprs = terms
                    .into_iter()
                    .map(|(base, exp)| {
                        Expression::binary_expression(
                            Operator::Exp,
                            base,
                            Expression::variadic_expression(Operator::Add, exp),
                        )
                    })
                    .collect();
                Expression::variadic_expression(Operator::Mul, exprs)
            }
            other => other.recurse(Expression::collect_like_muls),
        }
    }

    fn simplify_constants(self) -> Expression {
        match self {
            Expression::Binary(Operator::Exp, base, exp)
                if (*base == Expression::integer_expression(0)
                    || *base == Expression::real_expression(0.0))
                    && (*exp == Expression::real_expression(0.0)
                        || *exp == Expression::integer_expression(0)) =>
            {
                Expression::Binary(Operator::Exp, base, exp)
            }
            Expression::Binary(Operator::Exp, base, _)
                if *base == Expression::integer_expression(0)
                    || *base == Expression::real_expression(0.0) =>
            {
                Expression::integer_expression(0)
            }
            Expression::Binary(Operator::Exp, base, _)
                if *base == Expression::integer_expression(1)
                    || *base == Expression::real_expression(1.0) =>
            {
                Expression::integer_expression(1)
            }
            Expression::Binary(Operator::Exp, _, exp)
                if *exp == Expression::integer_expression(0)
                    || *exp == Expression::real_expression(0.0) =>
            {
                Expression::integer_expression(1)
            }
            Expression::Binary(Operator::Exp, base, exp)
                if *exp == Expression::integer_expression(1)
                    || *exp == Expression::real_expression(1.0) =>
            {
                *base
            }
            Expression::Variadic(Operator::Mul, exprs)
                if exprs.contains(&Expression::integer_expression(0))
                    || exprs.contains(&Expression::real_expression(0.0)) =>
            {
                Expression::integer_expression(0)
            }
            Expression::Variadic(_, mut exprs) if exprs.len() == 1 => exprs.remove(0),
            Expression::Variadic(Operator::Mul, exprs) => Expression::variadic_expression(
                Operator::Mul,
                exprs
                    .into_iter()
                    .map(Expression::simplify_constants)
                    .filter(|x| {
                        !(*x == Expression::integer_expression(1))
                            && !(*x == Expression::real_expression(1.0))
                    })
                    .collect(),
            ),
            Expression::Variadic(Operator::Add, exprs) => Expression::variadic_expression(
                Operator::Add,
                exprs
                    .into_iter()
                    .map(Expression::simplify_constants)
                    .filter(|x| {
                        !(*x == Expression::integer_expression(0))
                            && !(*x == Expression::real_expression(0.0))
                    })
                    .collect(),
            ),

            other => other.recurse(Expression::simplify_constants),
        }
    }

    fn comparer(&self, b: &Expression) -> std::cmp::Ordering {
        match (self, b) {
            (Expression::Lit(Term::Numeric(a)), Expression::Lit(Term::Numeric(b))) => a
                .as_integer()
                .get_integer()
                .unwrap()
                .cmp(&b.as_integer().get_integer().unwrap()),
            (Expression::Lit(Term::Numeric(_)), _) => std::cmp::Ordering::Less,
            (Expression::Lit(Term::Variable(a)), Expression::Lit(Term::Variable(b))) => a.cmp(b),
            (Expression::Lit(Term::Variable(_)), _) => std::cmp::Ordering::Less,
            (Expression::Unary(op_a, a), Expression::Unary(op_b, b)) => {
                op_a.cmp(op_b).then(Expression::comparer(a, b))
            }
            (Expression::Unary(_, _), _) => std::cmp::Ordering::Less,
            (Expression::Binary(op_a, a_1, a_2), Expression::Binary(op_b, b_1, b_2)) => op_a
                .cmp(op_b)
                .then(Expression::comparer(a_1, b_1))
                .then(Expression::comparer(a_2, b_2)),
            (Expression::Binary(_, _, _), _) => std::cmp::Ordering::Less,
            (Expression::Variadic(a, _), Expression::Variadic(b, _)) => a.cmp(b),
            _ => std::cmp::Ordering::Less,
        }
    }

    fn order(self) -> Expression {
        match self {
            Expression::Variadic(op, mut exprs) => {
                exprs = exprs.into_iter().map(|x| x.order()).collect();
                exprs.sort_by(Expression::comparer);
                Expression::variadic_expression(op, exprs)
            }
            other => other.recurse(Expression::order),
        }
    }

    fn equal(&self, other: &Expression) -> bool {
        match (self, other) {
            (Expression::Lit(a), Expression::Lit(b)) => a == b,
            (Expression::Unary(op_a, a_1), Expression::Unary(op_b, b_1)) => {
                op_a == op_b && a_1.equal(b_1)
            }
            (Expression::Binary(op_a, a_1, a_2), Expression::Binary(op_b, b_1, b_2)) => {
                op_a == op_b && a_1.equal(b_1) && a_2.equal(b_2)
            }
            (Expression::Variadic(op_a, exprs_a), Expression::Variadic(op_b, exprs_b)) => {
                op_a == op_b
                    && exprs_a.len() == exprs_b.len()
                    && exprs_a.iter().zip(exprs_b.iter()).all(|(a, b)| a.equal(b))
            }
            _ => false,
        }
    }

    fn simplify(self) -> Expression {
        let last_self = self.clone();
        let simplified = self
            .factor_out_neg()
            .factor_out_sub()
            .flatten_add()
            .flatten_mul()
            .simplify_rational_1()
            .simplify_rational_2()
            .simplify_rational_3()
            .explicit_exponents()
            .collect_like_muls()
            .simplify_constants();
        if simplified.equal(&last_self) {
            return simplified;
        }
        simplified.simplify()
    }

    fn derive(self, wrt: char) -> Expression {
        match self {
            Expression::Lit(_) => Expression::integer_expression(0),
            Expression::Unary(Operator::Paren, a) => *a,
            Expression::Unary(Operator::Neg, a) => {
                Expression::unary_expression(Operator::Neg, a.derive(wrt))
            }
            Expression::Binary(Operator::Div, a, b) => {
                let a_deriv = a.clone().derive(wrt);
                let b_deriv = b.clone().derive(wrt);
                let b_squared = Expression::binary_expression(
                    Operator::Exp,
                    *b.clone(),
                    Expression::integer_expression(2),
                );
                Expression::binary_expression(
                    Operator::Div,
                    Expression::binary_expression(
                        Operator::Add,
                        Expression::binary_expression(Operator::Mul, *b, a_deriv),
                        Expression::binary_expression(
                            Operator::Mul,
                            Expression::integer_expression(-1),
                            Expression::binary_expression(Operator::Mul, *a, b_deriv),
                        ),
                    ),
                    b_squared,
                )
            }
            Expression::Binary(Operator::Exp, base, exp) => Expression::binary_expression(
                Operator::Mul,
                Expression::binary_expression(Operator::Exp, *base.clone(), *exp.clone()),
                Expression::binary_expression(
                    Operator::Mul,
                    *exp,
                    Expression::unary_expression(Operator::Custom(String::from("ln")), *base)
                        .derive(wrt),
                ),
            ),
            Expression::Variadic(Operator::Add, exprs) => Expression::variadic_expression(
                Operator::Add,
                exprs.into_iter().map(|x| x.derive(wrt)).collect(),
            ),
            Expression::Variadic(Operator::Mul, mut exprs) if exprs.len() == 1 => {
                exprs.remove(0).derive(wrt)
            }
            Expression::Variadic(Operator::Mul, mut exprs) => {
                let f = exprs.remove(0);
                let exprs_deriv = exprs.clone();
                exprs.insert(0, f.clone().derive(wrt));
                Expression::binary_expression(
                    Operator::Add,
                    Expression::variadic_expression(Operator::Mul, exprs),
                    Expression::binary_expression(
                        Operator::Mul,
                        f,
                        Expression::Variadic(Operator::Mul, exprs_deriv).derive(wrt),
                    ),
                )
            }

            other => other,
        }
    }

    fn as_tex(self) -> String {
        match self {
            Expression::Lit(literal) => literal.as_tex(),
            Expression::Unary(operator, operand) => match operator {
                Operator::Paren => format!("({})", operand.as_tex()),
                Operator::Neg => format!("-{}", operand.as_tex()),
                Operator::Custom(fun_name) => format!("{}({})", fun_name, operand.as_tex()),
                _ => panic!("Impossible state reached"),
            },
            Expression::Binary(operator, left, right) => match operator {
                Operator::Add => format!("{} + {}", left.as_tex(), right.as_tex()),
                Operator::Sub => format!("{} - {}", left.as_tex(), right.as_tex()),
                Operator::Div => format!("{} \\div {}", left.as_tex(), right.as_tex()),
                Operator::Mul => format!("{} \\times {}", left.as_tex(), right.as_tex()),
                Operator::Exp => format!("({}^{{{}}})", left.as_tex(), right.as_tex()),
                _ => panic!("Impossible state reached"),
            },
            Expression::Variadic(operation, args) => {
                let mut list = args
                    .into_iter()
                    .map(|x| x.as_tex())
                    .collect::<Vec<String>>();
                let mut output = Vec::new();
                if list.len() > 0 {
                    output.push(list.remove(0));
                }

                while list.len() > 0 {
                    output.push(
                        match operation {
                            Operator::Add => " + ",
                            Operator::Mul => " \\times ",
                            _ => "invalid",
                        }
                        .to_string(),
                    );
                    output.push(list.remove(0));
                }
                output.into_iter().collect()
            }
        }
    }
}
use std::iter::Peekable;
fn tokenise<I: Iterator<Item = char>>(input: &mut Peekable<I>) -> Vec<String> {
    let mut output = Vec::new();
    while let Some(chr) = input.next() {
        match chr {
            chr if ['+', '-', '/', '*', '^', '(', ')'].contains(&chr) => {
                output.push(chr.to_string())
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
                output.push(num)
            }
            chr if chr.is_alphabetic() => {
                let mut word = String::new();
                word.push(chr);
                while let Some(chr) = input.peek() {
                    if chr.is_alphabetic() || chr.is_digit(10) {
                        word.push(input.next().unwrap())
                    } else {
			break;
		    }
                }
                output.push(word)
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
	    _ => panic!("Expected opening parenthesis for mathematical functions!")
        },
        Some(mut tok) => tok
            .parse::<i128>()
            .map(|x| Expression::integer_expression(x))
            .or::<std::string::ParseError>(
                tok.parse::<f64>()
                    .map(|x| Expression::real_expression(x))
                    .or(Ok(Expression::variable_expression(tok.remove(0)))),
            )
            .unwrap(),
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
