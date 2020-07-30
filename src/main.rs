use std::cmp::Ordering;
use std::fmt;
use std::fs;
use std::io;
use std::io::prelude::*;
use std::ops::{Add, Mul};
#[cfg(test)]
mod test;
#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
fn main() {
    let input = "tan(x^2)".chars();
    let mut tokens = tokenise(&mut input.peekable()).into_iter().peekable();
    let expr = parse_add(&mut tokens).unwrap();
    let one = Expression::integer_expression(1);
    let zero = Expression::integer_expression(0);
    dbg!(one.equal(&zero));
    dbg!(
        Expression::Variadic(Operator::Mul, vec![one.clone(), one.clone(), one])
            .simplify_constants()
    );
    println!(
        "{} and then {}",
        expr,
        expr.clone()
            .strip_paren()
            .flatten_comm(&Operator::Mul)
            .simplify_rational_3()
            .simplify_rational_1()
            .simplify_rational_2()
    );
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
    fn apply<F: Fn(i128, i128) -> i128, G: Fn(f64, f64) -> f64>(
        a: Literal,
        b: Literal,
        f: F,
        g: G,
    ) -> Literal {
        match (a, b) {
            (Literal::Integer(a), Literal::Integer(b)) => Literal::Integer(f(a, b)),
            (Literal::Real(a), Literal::Integer(b)) => Literal::Real(g(a, b as f64)),
            (Literal::Integer(a), Literal::Real(b)) => Literal::Real(g(a as f64, b)),
            (Literal::Real(a), Literal::Real(b)) => Literal::Real(g(a, b)),
        }
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
    fn into_tex(self) -> String {
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
            Operator::Paren => write!(f, "p"),
            Operator::Neg => write!(f, "n"),
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
                    .iter()
                    .map(|x| x.to_string() + " ")
                    .collect::<String>()
            ),
        }
    }
}

impl Expression {
    fn variable_expression(a: char) -> Expression {
        Expression::Lit(Term::Variable(a))
    }

    fn real_expression(a: f64) -> Expression {
        Expression::Lit(Term::Numeric(Literal::Real(a)))
    }

    fn integer_expression(a: i128) -> Expression {
        Expression::Lit(Term::Numeric(Literal::Integer(a)))
    }

    fn recurse<F: Fn(Expression) -> Expression>(self, rec: F) -> Expression {
        match self {
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::Unary(f, Box::new(rec(*a))),
            Expression::Binary(f, a, b) => {
                Expression::Binary(f, Box::new(rec(*a)), Box::new(rec(*b)))
            }
            Expression::Variadic(f, exprs) => {
                Expression::Variadic(f, exprs.into_iter().map(rec).collect())
            }
        }
    }

    fn strip_paren(self) -> Expression {
        match self {
            Expression::Unary(Operator::Paren, op) => op.strip_paren(),
            other => other.recurse(Expression::strip_paren),
        }
    }

    fn factor_out_neg(self) -> Expression {
        match self {
            Expression::Unary(Operator::Neg, a) => Expression::Variadic(
                Operator::Mul,
                vec![Expression::integer_expression(-1), a.factor_out_neg()],
            ),
            other => other.recurse(Expression::factor_out_neg),
        }
    }

    fn factor_out_sub(self) -> Expression {
        match self {
            Expression::Binary(Operator::Sub, a, b) => Expression::Variadic(
                Operator::Add,
                vec![
                    a.factor_out_sub(),
                    Expression::Variadic(
                        Operator::Mul,
                        vec![Expression::integer_expression(-1), b.factor_out_sub()],
                    ),
                ],
            ),
            other => other.recurse(Expression::factor_out_sub),
        }
    }

    fn flatten(self) -> Expression {
        self.flatten_comm(&Operator::Add)
            .flatten_comm(&Operator::Mul)
    }

    fn flatten_comm(self, operator: &Operator) -> Expression {
        match self {
            Expression::Binary(op, a, b) if operator == &op => {
                let mut terms = Vec::new();
                let mut append = |x: Expression| match x.flatten_comm(operator) {
                    Expression::Variadic(op, mut exprs) if &op == operator => {
                        terms.append(&mut exprs)
                    }
                    single => terms.push(single),
                };
                append(*a);
                append(*b);
                Expression::Variadic(operator.clone(), terms)
            }
            Expression::Variadic(op, exprs) if &op == operator => {
                let exprs = exprs
                    .into_iter()
                    .map(|x| x.flatten_comm(operator))
                    .collect::<Vec<Expression>>();
                let (mut to_append, mut rest): (Vec<Expression>, Vec<Expression>) = exprs
                    .into_iter()
                    .partition(|x| matches!(x,Expression::Variadic(op,_) if op == operator));
                let mut append = |x: Expression| match x.flatten_comm(operator) {
                    Expression::Variadic(op, mut exprs) if &op == operator => {
                        rest.append(&mut exprs)
                    }
                    single => rest.push(single),
                };
                while !to_append.is_empty() {
                    append(to_append.remove(0))
                }
                Expression::Variadic(operator.clone(), rest)
            }
            other => other.recurse(|x| x.flatten_comm(operator)),
        }
    }

    fn simplify_rational_1(self) -> Expression {
        match self {
            Expression::Binary(Operator::Div, numer, denom) => match numer.simplify_rational_1() {
                Expression::Binary(Operator::Div, numer_numer, numer_denom) => Expression::Binary(
                    Operator::Div,
                    numer_numer,
                    Box::new(Expression::Variadic(
                        Operator::Mul,
                        vec![*numer_denom, denom.simplify_rational_1()],
                    )),
                )
                .simplify_rational_1(),
                numer => Expression::Binary(
                    Operator::Div,
                    Box::new(numer),
                    Box::new(denom.simplify_rational_1()),
                ),
            },
            other => other.recurse(Expression::simplify_rational_1),
        }
    }

    fn simplify_rational_2(self) -> Expression {
        match self {
            Expression::Binary(Operator::Div, numer, denom) => match denom.simplify_rational_2() {
                Expression::Binary(Operator::Div, denom_numer, denom_denom) => Expression::Binary(
                    Operator::Div,
                    Box::new(Expression::Variadic(
                        Operator::Mul,
                        vec![*denom_denom, numer.simplify_rational_2()],
                    )),
                    denom_numer,
                )
                .simplify_rational_2(),
                denom => Expression::Binary(
                    Operator::Div,
                    Box::new(numer.simplify_rational_2()),
                    Box::new(denom),
                ),
            },
            other => other.recurse(Expression::simplify_rational_2),
        }
    }

    fn simplify_rational_3(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Mul, mut exprs) => {
                match exprs
                    .iter_mut()
                    .position(|x| matches!(*x, Expression::Binary(Operator::Div, _, _)))
                {
                    Some(index) => {
                        if let Expression::Binary(Operator::Div, numer, denom) = exprs.remove(index)
                        {
                            exprs.push(*numer);
                            Expression::Binary(
                                Operator::Div,
                                Box::new(Expression::Variadic(
                                    Operator::Mul,
                                    exprs
                                        .into_iter()
                                        .map(Expression::simplify_rational_3)
                                        .collect(),
                                )),
                                Box::new(denom.simplify_rational_3()),
                            )
                            .simplify_rational_3()
                        } else {
                            panic!("Unreachable!")
                        }
                    }
                    None => Expression::Variadic(
                        Operator::Mul,
                        exprs
                            .into_iter()
                            .map(Expression::simplify_rational_3)
                            .collect(),
                    ),
                }
            }
            other => other.recurse(Expression::simplify_rational_3),
        }
    }

    fn explicit_exponents(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Mul, exprs) => {
                let exprs = exprs
                    .into_iter()
                    .map(|expr| match expr {
                        Expression::Binary(Operator::Exp, lhs, rhs) => Expression::Binary(
                            Operator::Exp,
                            Box::new(lhs.explicit_exponents()),
                            Box::new(rhs.explicit_exponents()),
                        ),
                        other => Expression::Binary(
                            Operator::Exp,
                            Box::new(other.explicit_exponents()),
                            Box::new(Expression::integer_expression(1)),
                        ),
                    })
                    .collect();
                Expression::Variadic(Operator::Mul, exprs)
            }
            other => other.recurse(Expression::explicit_exponents),
        }
    }

    fn explicit_coefficients(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Add, exprs) => {
                let exprs = exprs
                    .into_iter()
                    .map(|expr| match expr {
                        Expression::Binary(Operator::Mul, lhs, rhs) => Expression::Binary(
                            Operator::Mul,
                            Box::new(lhs.explicit_coefficients()),
                            Box::new(rhs.explicit_coefficients()),
                        ),
                        other => Expression::Binary(
                            Operator::Mul,
                            Box::new(Expression::integer_expression(1)),
                            Box::new(other.explicit_coefficients()),
                        ),
                    })
                    .collect();
                Expression::Variadic(Operator::Add, exprs)
            }
            other => other.recurse(Expression::explicit_coefficients),
        }
    }

    fn collect_like_muls(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Mul, mut exprs) => {
                let mut bases = Vec::new();
                for expr in &exprs {
                    if let Expression::Binary(Operator::Exp, base, _) = expr {
                        if !bases.contains(base) {
                            bases.push(base.clone())
                        }
                    }
                }
                let mut terms: Vec<(Expression, Vec<Expression>)> = bases
                    .into_iter()
                    .map(|x| *x)
                    .zip(std::iter::repeat(Vec::new()))
                    .collect();

                while !exprs.is_empty() {
                    if let Expression::Binary(Operator::Exp, base, mut pow) = exprs.remove(0) {
                        for term in &mut terms {
                            if term.0.equal(&base) {
                                term.1.push(std::mem::replace(
                                    &mut *pow,
                                    Expression::integer_expression(0),
                                ))
                            }
                        }
                    }
                }

                exprs = terms
                    .into_iter()
                    .map(|(base, exp)| {
                        Expression::Binary(
                            Operator::Exp,
                            Box::new(base.collect_like_muls()),
                            Box::new(Expression::Variadic(
                                Operator::Add,
                                exp.into_iter().map(Expression::collect_like_muls).collect(),
                            )),
                        )
                    })
                    .collect();
                Expression::Variadic(Operator::Mul, exprs)
            }
            other => other.recurse(Expression::collect_like_muls),
        }
    }

    fn simplify_constants(self) -> Expression {
        let zero_i = Expression::integer_expression(0);
        let zero_r = Expression::real_expression(0.0);
        let one_i = Expression::integer_expression(1);
        let one_r = Expression::real_expression(1.0);
        match self {
            Expression::Binary(Operator::Exp, mut base, mut pow) => {
                *base = base.simplify_constants();
                *pow = pow.simplify_constants();
                if pow.equal(&one_i)
                    || base.equal(&one_i)
                    || pow.equal(&one_r)
                    || base.equal(&one_r)
                {
                    *base
                } else if (pow.equal(&zero_i) || pow.equal(&zero_r))
                    && (!base.equal(&zero_i) || !base.equal(&zero_r))
                {
                    one_i
                } else if (base.equal(&zero_i) || base.equal(&zero_r))
                    && (!pow.equal(&zero_i) || !pow.equal(&zero_r))
                {
                    zero_i
                } else {
                    Expression::Binary(Operator::Exp, base, pow)
                }
            }
            Expression::Variadic(Operator::Mul, mut exprs) => {
                exprs = exprs
                    .into_iter()
                    .map(Expression::simplify_constants)
                    .collect();
                exprs.retain(|expr| !(expr.equal(&one_i) || expr.equal(&one_r)));
                if exprs.is_empty() {
                    Expression::integer_expression(1)
                } else if exprs.iter().any(|x| x.equal(&zero_i) || x.equal(&zero_r)) {
                    zero_i
                } else if exprs
                    .iter()
                    .any(|x| matches!(x, Expression::Lit(Term::Numeric(_))))
                {
                    let (consts, mut exprs): (Vec<Expression>, Vec<Expression>) = exprs
                        .into_iter()
                        .partition(|x| matches!(x, Expression::Lit(Term::Numeric(_))));
                    exprs.push(Expression::Lit(Term::Numeric(consts.into_iter().fold(
                        Literal::Integer(1),
                        |acc, expr| match expr {
                            Expression::Lit(Term::Numeric(lit)) => {
                                Literal::apply(acc, lit, i128::mul, f64::mul)
                            }
                            _ => panic!("Non constant!"),
                        },
                    ))));
                    if exprs.len() == 1 {
                        exprs.remove(0)
                    } else {
                        Expression::Variadic(Operator::Mul, exprs)
                    }
                } else if exprs.len() == 1 {
                    exprs.remove(0).simplify_constants()
                } else {
                    Expression::Variadic(Operator::Mul, exprs)
                }
            }
            Expression::Variadic(Operator::Add, mut exprs) => {
                exprs = exprs
                    .into_iter()
                    .map(Expression::simplify_constants)
                    .collect();
                exprs.retain(|expr| !(expr.equal(&zero_i) || expr.equal(&zero_r)));
                if exprs.is_empty() {
                    Expression::integer_expression(0)
                } else if exprs
                    .iter()
                    .any(|x| matches!(x, Expression::Lit(Term::Numeric(_))))
                {
                    let (consts, mut exprs): (Vec<Expression>, Vec<Expression>) = exprs
                        .into_iter()
                        .partition(|x| matches!(x, Expression::Lit(Term::Numeric(_))));
                    exprs.push(Expression::Lit(Term::Numeric(consts.into_iter().fold(
                        Literal::Integer(0),
                        |acc, expr| match expr {
                            Expression::Lit(Term::Numeric(lit)) => {
                                Literal::apply(acc, lit, i128::add, f64::add)
                            }
                            _ => panic!("Non constants!"),
                        },
                    ))));
                    if exprs.len() == 1 {
                        exprs.remove(0)
                    } else {
                        Expression::Variadic(Operator::Add, exprs)
                    }
                } else if exprs.len() == 1 {
                    exprs.remove(0).simplify_constants()
                } else {
                    Expression::Variadic(Operator::Add, exprs)
                }
            }
            other => other.recurse(Expression::simplify_constants),
        }
    }

    fn factor(self) -> Expression {
        match self {
            Expression::Binary(Operator::Div, num, denom) => panic!(),
            other => other.recurse(Expression::factor),
        }
    }

    fn comparer(&self, b: &Expression) -> std::cmp::Ordering {
        match (self, b) {
            (Expression::Lit(a), Expression::Lit(b)) => {
                a.partial_cmp(b).expect("Failed to compare two literals!")
            }
            (Expression::Lit(_), _) => Ordering::Less,
            (_, Expression::Lit(_)) => Ordering::Greater,
            (Expression::Unary(op_a, a), Expression::Unary(op_b, b)) => {
                op_a.cmp(op_b).then(Expression::comparer(a, b))
            }
            (Expression::Unary(_, _), _) => std::cmp::Ordering::Less,
            (_, Expression::Unary(_, _)) => std::cmp::Ordering::Greater,
            (Expression::Binary(op_a, a_1, a_2), Expression::Binary(op_b, b_1, b_2)) => op_a
                .cmp(op_b)
                .then(Expression::comparer(a_1, b_1))
                .then(Expression::comparer(a_2, b_2)),
            (Expression::Binary(_, _, _), _) => std::cmp::Ordering::Less,
            (_, Expression::Binary(_, _, _)) => std::cmp::Ordering::Greater,
            (Expression::Variadic(f, f_exprs), Expression::Variadic(g, g_exprs)) => f.cmp(g).then(
                f_exprs
                    .iter()
                    .zip(g_exprs.iter())
                    .fold(Ordering::Equal, |acc, (a, b)| acc.then(a.comparer(b))),
            ),
        }
    }

    fn order(self) -> Expression {
        match self {
            Expression::Variadic(op, mut exprs) => {
                exprs = exprs.into_iter().map(|x| x.order()).collect();
                exprs.sort_by(Expression::comparer);
                Expression::Variadic(op, exprs)
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
            .strip_paren()
            .factor_out_neg()
            .factor_out_sub()
            .flatten()
            .simplify_rational_1()
            .simplify_rational_2()
            .simplify_rational_3()
            .flatten()
            .explicit_exponents()
            .collect_like_muls()
            .flatten()
            .simplify_constants();
        if simplified.equal(&last_self) {
            simplified.order()
        } else {
            simplified.simplify()
        }
    }

    fn derive(self, wrt: char) -> Expression {
        match self {
            Expression::Lit(Term::Variable(var)) => {
                Expression::integer_expression(if var == wrt { 1 } else { 0 })
            }
            Expression::Lit(_) => Expression::integer_expression(0),
            Expression::Unary(Operator::Paren, a) => a.derive(wrt),
            Expression::Unary(Operator::Neg, a) => Expression::Variadic(
                Operator::Mul,
                vec![Expression::integer_expression(-1), a.derive(wrt)],
            ),
            Expression::Unary(Operator::Custom(f), x) if f == "ln" => Expression::Variadic(
                Operator::Mul,
                vec![
                    x.clone().derive(wrt),
                    Expression::Binary(
                        Operator::Exp,
                        x,
                        Box::new(Expression::integer_expression(-1)),
                    ),
                ],
            ),
            Expression::Unary(Operator::Custom(f), x) if f == "sin" => Expression::Variadic(
                Operator::Mul,
                vec![
                    x.clone().derive(wrt),
                    Expression::Unary(Operator::Custom(String::from("cos")), x),
                ],
            ),
            Expression::Unary(Operator::Custom(f), x) if f == "cos" => Expression::Variadic(
                Operator::Mul,
                vec![
                    x.clone().derive(wrt),
                    Expression::integer_expression(-1),
                    Expression::Unary(Operator::Custom(String::from("sin")), x),
                ],
            ),
            Expression::Unary(Operator::Custom(f), x) if f == "tan" => Expression::Binary(
                Operator::Div,
                Box::new(Expression::Unary(
                    Operator::Custom(String::from("sin")),
                    x.clone(),
                )),
                Box::new(Expression::Unary(
                    Operator::Custom(String::from("cos")),
                    x,
                )),
            )
            .derive(wrt),
            Expression::Binary(Operator::Div, a, b) => {
                let a_deriv = a.clone().derive(wrt);
                let b_deriv = b.clone().derive(wrt);
                let b_squared = Box::new(Expression::Binary(
                    Operator::Exp,
                    b.clone(),
                    Box::new(Expression::integer_expression(2)),
                ));
                let b_a_deriv = Expression::Variadic(Operator::Mul, vec![*b, a_deriv]);
                let a_b_deriv = Expression::Variadic(
                    Operator::Mul,
                    vec![Expression::integer_expression(-1), *a, b_deriv],
                );
                Expression::Binary(
                    Operator::Div,
                    Box::new(Expression::Variadic(
                        Operator::Add,
                        vec![b_a_deriv, a_b_deriv],
                    )),
                    b_squared,
                )
            }
            Expression::Binary(Operator::Exp, base, exp) => Expression::Variadic(
                Operator::Mul,
                vec![
                    Expression::Binary(Operator::Exp, base.clone(), exp.clone()),
                    Expression::Variadic(
                        Operator::Mul,
                        vec![
                            *exp,
                            Expression::Unary(Operator::Custom(String::from("ln")), base),
                        ],
                    )
                    .derive(wrt),
                ],
            ),
            Expression::Variadic(_, mut exprs) if exprs.len() == 1 => exprs.remove(0).derive(wrt),
            Expression::Variadic(Operator::Add, exprs) => Expression::Variadic(
                Operator::Add,
                exprs.into_iter().map(|x| x.derive(wrt)).collect(),
            ),
            Expression::Variadic(Operator::Mul, exprs) => {
                let mut exprs_deriv = exprs
                    .clone()
                    .into_iter()
                    .map(|x| x.derive(wrt))
                    .collect::<Vec<Expression>>();
                let mut nodes = std::iter::repeat(exprs.clone())
                    .take(exprs.len())
                    .collect::<Vec<Vec<Expression>>>();
                for (i, node) in nodes.iter_mut().enumerate() {
                    node.remove(i);
                    node.insert(i, exprs_deriv.remove(0))
                }

                Expression::Variadic(
                    Operator::Add,
                    nodes
                        .into_iter()
                        .map(|exprs| Expression::Variadic(Operator::Mul, exprs))
                        .collect(),
                )
            }

            other => other,
        }
    }

    fn into_tex(self) -> String {
        match self {
            Expression::Lit(literal) => literal.into_tex(),
            Expression::Unary(operator, operand) => match operator {
                Operator::Paren => format!("({})", operand.into_tex()),
                Operator::Neg => format!("-{}", operand.into_tex()),
                Operator::Custom(fun_name) => format!("{}({})", fun_name, operand.into_tex()),
                _ => panic!("Impossible state reached"),
            },
            Expression::Binary(operator, left, right) => match operator {
                Operator::Add => format!("{} + {}", left.into_tex(), right.into_tex()),
                Operator::Sub => format!("{} - {}", left.into_tex(), right.into_tex()),
                Operator::Div => format!("\\frac{{{}}}{{{}}}", left.into_tex(), right.into_tex()),
                Operator::Mul => format!("{} \\times {}", left.into_tex(), right.into_tex()),
                Operator::Exp => format!("({}^{{{}}})", left.into_tex(), right.into_tex()),
                _ => panic!("Impossible state reached"),
            },
            Expression::Variadic(operation, args) => {
                let mut list = args
                    .into_iter()
                    .map(|x| x.into_tex())
                    .collect::<Vec<String>>();
                let mut output = Vec::new();
                if !list.is_empty() {
                    output.push(list.remove(0));
                }

                while !list.is_empty() {
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
