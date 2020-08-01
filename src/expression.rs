use std::cmp::{Ordering, PartialEq, PartialOrd};
use std::fmt;
use std::ops::{Add, Mul};
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub enum Literal {
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
    //It's meant to make to make it easier use binary functions on either.
    pub fn apply<F: Fn(i128, i128) -> i128, G: Fn(f64, f64) -> f64>(
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
pub enum Term {
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
    pub fn into_tex(self) -> String {
        match self {
            Term::Numeric(Literal::Integer(i)) => i.to_string(),
            Term::Numeric(Literal::Real(r)) => r.to_string(),
            Term::Variable(c) => c.to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Ord)]
pub enum Operator {
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

#[derive(Debug, Clone)]
pub enum Expression {
    Lit(Term),
    Unary(Operator, Box<Expression>),
    Binary(Operator, Box<Expression>, Box<Expression>),
    Variadic(Operator, Vec<Expression>),
}

impl PartialEq for Expression {
    fn eq(&self, other: &Expression) -> bool {
        match (self, other) {
            (Expression::Lit(a), Expression::Lit(b)) => a == b,
            (Expression::Unary(op_a, a_1), Expression::Unary(op_b, b_1)) => {
                op_a == op_b && a_1.eq(b_1)
            }
            (Expression::Binary(op_a, a_1, a_2), Expression::Binary(op_b, b_1, b_2)) => {
                op_a == op_b && a_1.eq(b_1) && a_2.eq(b_2)
            }
            (Expression::Variadic(op_a, exprs_a), Expression::Variadic(op_b, exprs_b)) => {
                op_a == op_b
                    && exprs_a.len() == exprs_b.len()
                    && exprs_a.iter().zip(exprs_b.iter()).all(|(a, b)| a.eq(b))
            }
            _ => false,
        }
    }
}

impl PartialOrd for Expression {
    fn partial_cmp(&self, other: &Expression) -> Option<Ordering> {
        match (self, other) {
            (Expression::Lit(a), Expression::Lit(b)) => a.partial_cmp(b),
            (Expression::Lit(_), _) => Some(Ordering::Less),
            (_, Expression::Lit(_)) => Some(Ordering::Greater),
            (Expression::Unary(op_a, a), Expression::Unary(op_b, b)) => Some(
                op_a.cmp(op_b)
                    .then(a.partial_cmp(b).unwrap_or(Ordering::Greater)),
            ),
            (Expression::Unary(_, _), _) => Some(Ordering::Less),
            (_, Expression::Unary(_, _)) => Some(Ordering::Greater),
            (Expression::Binary(op_a, a_1, a_2), Expression::Binary(op_b, b_1, b_2)) => Some(
                op_a.cmp(op_b)
                    .then(a_1.partial_cmp(b_1).unwrap_or(Ordering::Greater))
                    .then(a_2.partial_cmp(b_2).unwrap_or(Ordering::Greater)),
            ),
            (Expression::Binary(_, _, _), _) => Some(Ordering::Less),
            (_, Expression::Binary(_, _, _)) => Some(Ordering::Greater),
            (Expression::Variadic(f, f_exprs), Expression::Variadic(g, g_exprs)) => Some(
                f.cmp(g).then(
                    f_exprs
                        .iter()
                        .zip(g_exprs.iter())
                        .fold(Ordering::Equal, |acc, (a, b)| {
                            acc.then(a.partial_cmp(b).unwrap_or(Ordering::Less))
                        }),
                ),
            ),
        }
    }
}

impl Eq for Expression {}

impl Ord for Expression {
    fn cmp(&self, other: &Expression) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Less)
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Lit(t) => write!(f, "{}", t),
            Expression::Unary(op, a) => match op {
                Operator::Paren => write!(f, "({})", *a),
		Operator::Custom(fun) => write!(f,"{}({})",fun,*a),
                op => write!(f, "{}{}", op, *a),
            },
            Expression::Binary(op, a, b) => write!(f, "({} {} {})", *a, op, *b),
            Expression::Variadic(op, exprs) => {
                write!(f, "(")?;
                for expr in exprs.iter().take(exprs.len() - 1) {
                    write!(f, "{} {}", expr, op)?;
                }
                match exprs.iter().last() {
                    Some(expr) => write!(f, " {}", expr),
                    _ => write!(f, ""),
                }?;
                write!(f, ")")
            }
        }
    }
}

//The methods are mostly different steps of the simplification process
impl Expression {
    pub fn variable_expression(a: char) -> Expression {
        Expression::Lit(Term::Variable(a))
    }

    pub fn real_expression(a: f64) -> Expression {
        Expression::Lit(Term::Numeric(Literal::Real(a)))
    }

    pub fn integer_expression(a: i128) -> Expression {
        Expression::Lit(Term::Numeric(Literal::Integer(a)))
    }
    //Applies function on the remaining cases of an Expression, meant to help cut down on boilerplate.
    pub fn apply_on_others<F: Fn(Expression) -> Expression>(self, f: F) -> Expression {
        match self {
            l @ Expression::Lit(_) => l,
            Expression::Unary(op, a) => Expression::Unary(op, Box::new(f(*a))),
            Expression::Binary(op, a, b) => {
                Expression::Binary(op, Box::new(f(*a)), Box::new(f(*b)))
            }
            Expression::Variadic(op, exprs) => {
                Expression::Variadic(op, exprs.into_iter().map(f).collect())
            }
        }
    }

    pub fn strip_paren(self) -> Expression {
        match self {
            Expression::Unary(Operator::Paren, op) => op.strip_paren(),
            other => other.apply_on_others(Expression::strip_paren),
        }
    }

    pub fn factor_out_neg(self) -> Expression {
        match self {
            Expression::Unary(Operator::Neg, a) => Expression::Variadic(
                Operator::Mul,
                vec![Expression::integer_expression(-1), a.factor_out_neg()],
            ),
            other => other.apply_on_others(Expression::factor_out_neg),
        }
    }

    pub fn factor_out_sub(self) -> Expression {
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
            other => other.apply_on_others(Expression::factor_out_sub),
        }
    }

    pub fn flatten(self) -> Expression {
        self.flatten_comm(&Operator::Add)
            .flatten_comm(&Operator::Mul)
    }

    //Flattens trees of commutative operations (i.e., addition and multiplicaton)
    pub fn flatten_comm(self, operator: &Operator) -> Expression {
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
            other => other.apply_on_others(|x| x.flatten_comm(operator)),
        }
    }

    //Turns (/ (/ a b) c) into (/ a (* b c))
    pub fn simplify_rational_1(self) -> Expression {
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
            other => other.apply_on_others(Expression::simplify_rational_1),
        }
    }
    //Turns (/ a (/ b c)) into (/ (* a c) b)
    pub fn simplify_rational_2(self) -> Expression {
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
            other => other.apply_on_others(Expression::simplify_rational_2),
        }
    }

    //Turns (* a b (/ c d) e f (/ g h) i j...) into (/ (* a b c e f (/g h) i j ...) d) until (/ (* a b c e f g i j) (* d h)) remains
    pub fn simplify_rational_3(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Mul, mut exprs) => {
                exprs = exprs
                    .into_iter()
                    .map(Expression::simplify_rational_3)
                    .collect();
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
                                Box::new(Expression::Variadic(Operator::Mul, exprs)),
                                Box::new(denom.simplify_rational_3()),
                            )
                            .simplify_rational_3()
                        } else {
                            //This shouldn't be possible to reach
                            Expression::Variadic(Operator::Mul, exprs)
                        }
                    }
                    None => Expression::Variadic(Operator::Mul, exprs),
                }
            }
            other => other.apply_on_others(Expression::simplify_rational_3),
        }
    }

    //Makes all expressions under multiplication node exponentials. Makes it easier to group them.
    pub fn explicit_exponents(self) -> Expression {
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
            other => other.apply_on_others(Expression::explicit_exponents),
        }
    }

    //Makes all expressions under an addition node products. Makes it easier to group them (not implemented yet.)
    pub fn explicit_coefficients(self) -> Expression {
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
            other => other.apply_on_others(Expression::explicit_coefficients),
        }
    }

    //Groups exponents with the same base
    pub fn collect_like_muls(self) -> Expression {
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
                            if term.0 == *base {
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
            other => other.apply_on_others(Expression::collect_like_muls),
        }
    }

    pub fn simplify_constants(self) -> Expression {
        let zero_i = Expression::integer_expression(0);
        let zero_r = Expression::real_expression(0.0);
        let one_i = Expression::integer_expression(1);
        let one_r = Expression::real_expression(1.0);
        match self {
            Expression::Binary(Operator::Exp, mut base, mut pow) => {
                *base = base.simplify_constants();
                *pow = pow.simplify_constants();
                if *pow == one_i || *base == one_i || *pow == one_r || *base == one_r {
                    *base
                } else if (*pow == zero_i || *pow == zero_r)
                    && !(*base == zero_i || *base == zero_r)
                {
                    one_i
                } else if (*base == zero_i || *base == zero_r)
                    && !(*pow == zero_i || *pow == zero_r)
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
                exprs.retain(|expr| !(*expr == one_i || *expr == one_r));
                if exprs.is_empty() {
                    Expression::integer_expression(1)
                } else if exprs.iter().any(|x| *x == zero_i || *x == zero_r) {
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
                            _ => acc,
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
                exprs.retain(|expr| !(*expr == zero_i || *expr == zero_r));
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
                            _ => acc,
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
            other => other.apply_on_others(Expression::simplify_constants),
        }
    }

    pub fn order(self) -> Expression {
        match self {
            Expression::Variadic(op, mut exprs) => {
                exprs = exprs.into_iter().map(|x| x.order()).collect();
                exprs.sort();
                Expression::Variadic(op, exprs)
            }
            other => other.apply_on_others(Expression::order),
        }
    }

    pub fn simplify(self) -> Expression {
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
        if simplified == last_self {
            simplified.order()
        } else {
            simplified.simplify()
        }
    }

    //The reason all this other code exists. Recursively produces the derivate of a given expression with respect to its supplied argument
    pub fn derive(self, wrt: char) -> Expression {
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
                Box::new(Expression::Unary(Operator::Custom(String::from("cos")), x)),
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
    //Quick and dirty way to get a string you can throw into a LaTeX renderer, can make visually inspecting results easier.
    pub fn into_tex(self) -> String {
        match self {
            Expression::Lit(literal) => literal.into_tex(),
            Expression::Unary(operator, operand) => match operator {
                Operator::Paren => format!("({})", operand.into_tex()),
                Operator::Neg => format!("-({})", operand.into_tex()),
                Operator::Custom(fun_name) => format!("{}({})", fun_name, operand.into_tex()),
                _ => "".to_string(),
            },
            Expression::Binary(operator, left, right) => match operator {
                Operator::Add => format!("{} + {}", left.into_tex(), right.into_tex()),
                Operator::Sub => format!("{} - {}", left.into_tex(), right.into_tex()),
                Operator::Div => format!("\\frac{{{}}}{{{}}}", left.into_tex(), right.into_tex()),
                Operator::Mul => format!("{} \\times {}", left.into_tex(), right.into_tex()),
                Operator::Exp => format!("({}^{{{}}})", left.into_tex(), right.into_tex()),
                _ => "".to_string(),
            },
            Expression::Variadic(operation, args) => {
                let mut list = args
                    .into_iter()
                    .map(|x| x.into_tex())
                    .collect::<Vec<String>>();
                let mut output = Vec::new();
                if !list.is_empty() {
                    output.push("(".to_string());
                    output.push(list.remove(0));
                }

                while !list.is_empty() {
                    output.push(
                        match operation {
                            Operator::Add => " + ",
                            Operator::Mul => " \\times ",
                            _ => "",
                        }
                        .to_string(),
                    );
                    output.push(list.remove(0));
                }
                output.push(")".to_string());
                output.into_iter().collect()
            }
        }
    }
}
