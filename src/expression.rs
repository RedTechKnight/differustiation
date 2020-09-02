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

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Term {
    Numeric(Literal),
    Variable(char),
}

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Term) -> Option<Ordering> {
        match (self, other) {
            (Term::Numeric(_), Term::Variable(_)) => Some(Ordering::Less),
            (Term::Variable(_), Term::Numeric(_)) => Some(Ordering::Greater),
            (Term::Numeric(a), Term::Numeric(b)) => a.partial_cmp(b),
            (Term::Variable(a), Term::Variable(b)) => a.partial_cmp(b),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Numeric(n) => write!(f, "{}", n),
            Term::Variable(c) => write!(f, "{}", c),
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
                Operator::Custom(fun) => write!(f, "{}({})", fun, *a),
                op => write!(f, "{}{}", op, *a),
            },
            Expression::Binary(op, a, b) => write!(f, "({} {} {})", *a, op, *b),
            Expression::Variadic(op, exprs) => write!(
                f,
                "({})",
                exprs
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(match op {
                        Operator::Add => " + ",
                        _ => "*",
                    })
            ),
        }
    }
}

//The methods are mostly different steps of the simplification process
impl Expression {
    pub fn integer_expression(a: i128) -> Expression {
        Expression::Lit(Term::Numeric(Literal::Integer(a)))
    }

    fn is_zero(&self) -> bool {
        match self {
            Expression::Lit(Term::Numeric(Literal::Integer(0))) => true,
            Expression::Lit(Term::Numeric(Literal::Real(r))) => {
                if let Some(Ordering::Equal) = r.partial_cmp(&0.0) {
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn is_one(&self) -> bool {
        match self {
            Expression::Lit(Term::Numeric(Literal::Integer(1))) => true,
            Expression::Lit(Term::Numeric(Literal::Real(r))) => {
                if let Some(Ordering::Equal) = r.partial_cmp(&1.0) {
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn is_less_than_zero(&self) -> bool {
        match self {
            Expression::Lit(Term::Numeric(Literal::Integer(i))) => i < &0,
            Expression::Lit(Term::Numeric(Literal::Real(r))) => {
                if let Some(Ordering::Less) = r.partial_cmp(&0.0) {
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
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

    pub fn strip(self) -> Expression {
        match self {
            Expression::Unary(Operator::Paren, op) => op.strip(),
            Expression::Variadic(_, mut exprs) if exprs.len() == 1 => exprs.remove(0).strip(),
            other => other.apply_on_others(Expression::strip),
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
                let (mut to_append, mut rest): (Vec<Expression>, Vec<Expression>) = exprs
                    .into_iter()
                    .map(|x| x.flatten_comm(operator))
                    .partition(|x| matches!(x,Expression::Variadic(op,_) if op == operator));
                let mut append = |x: Expression| match x {
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
    pub fn remove_div_in_numer(self) -> Expression {
        match self {
            Expression::Binary(Operator::Div, numer, denom) => match numer.remove_div_in_numer() {
                Expression::Binary(Operator::Div, numer_numer, numer_denom) => Expression::Binary(
                    Operator::Div,
                    numer_numer,
                    Box::new(Expression::Variadic(
                        Operator::Mul,
                        vec![*numer_denom, denom.remove_div_in_numer()],
                    )),
                )
                .remove_div_in_numer(),
                numer => Expression::Binary(
                    Operator::Div,
                    Box::new(numer),
                    Box::new(denom.remove_div_in_numer()),
                ),
            },
            other => other.apply_on_others(Expression::remove_div_in_numer),
        }
    }

    //Turns (/ a (/ b c)) into (/ (* a c) b)
    pub fn remove_div_in_denom(self) -> Expression {
        match self {
            Expression::Binary(Operator::Div, numer, denom) => match denom.remove_div_in_denom() {
                Expression::Binary(Operator::Div, denom_numer, denom_denom) => Expression::Binary(
                    Operator::Div,
                    Box::new(Expression::Variadic(
                        Operator::Mul,
                        vec![*denom_denom, numer.remove_div_in_denom()],
                    )),
                    denom_numer,
                )
                .remove_div_in_denom(),
                denom => Expression::Binary(
                    Operator::Div,
                    Box::new(numer.remove_div_in_denom()),
                    Box::new(denom),
                ),
            },
            other => other.apply_on_others(Expression::remove_div_in_denom),
        }
    }

    //Turns (* a b (/ c d) e f (/ g h) i j...) into (/ (* a b c e f (/g h) i j ...) d) until (/ (* a b c e f g i j) (* d h)) remains
    pub fn remove_div_in_mul_node(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Mul, mut exprs) => {
                exprs = exprs
                    .into_iter()
                    .map(Expression::remove_div_in_mul_node)
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
                                Box::new(denom.remove_div_in_mul_node()),
                            )
                            .remove_div_in_mul_node()
                        } else {
                            //This shouldn't be possible to reach
                            Expression::Variadic(Operator::Mul, exprs)
                        }
                    }
                    None => Expression::Variadic(Operator::Mul, exprs),
                }
            }
            other => other.apply_on_others(Expression::remove_div_in_mul_node),
        }
    }

    //Makes all expressions under multiplication node exponentials. Makes it easier to group them.
    pub fn explicit_exponents(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Mul, exprs) => {
                let exprs = exprs
                    .into_iter()
                    .map(Expression::explicit_exponents)
                    .map(|expr| match expr {
                        expr @ Expression::Binary(Operator::Exp, _, _) => expr,

                        other => Expression::Binary(
                            Operator::Exp,
                            Box::new(other),
                            Box::new(Expression::integer_expression(1)),
                        ),
                    })
                    .collect();
                Expression::Variadic(Operator::Mul, exprs)
            }
            other => other.apply_on_others(Expression::explicit_exponents),
        }
    }

    //Makes all expressions under an addition node products. Makes it easier to group them.
    pub fn explicit_coefficients(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Add, exprs) => {
                let exprs = exprs
                    .into_iter()
                    .map(Expression::explicit_coefficients)
                    .map(|expr| match expr {
                        Expression::Variadic(Operator::Mul, mut exprs) => {
                            if !exprs
                                .iter()
                                .any(|expr| matches!(expr, Expression::Lit(Term::Numeric(_))))
                            {
                                exprs.push(Expression::integer_expression(1));
                            }

                            Expression::Variadic(Operator::Mul, exprs)
                        }
                        expr @ Expression::Lit(Term::Numeric(_)) => expr,
                        other => Expression::Variadic(
                            Operator::Mul,
                            vec![Expression::integer_expression(1), other],
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
            Expression::Variadic(Operator::Mul, exprs) => {
                let exprs = exprs
                    .into_iter()
                    .map(Expression::collect_like_muls)
                    .filter_map(|expr| match expr {
                        Expression::Binary(Operator::Exp, base, pow) => Some((base, pow)),
                        _ => None,
                    })
                    .collect();
                let grouped = group_similar_by(exprs, |(base_a, _), (base_b, _)| base_a == base_b)
                    .into_iter()
                    .filter_map(|vec| match vec.first().cloned() {
                        Some((base, _)) => Some(Expression::Binary(
                            Operator::Exp,
                            base,
                            Box::new(Expression::Variadic(
                                Operator::Add,
                                vec.into_iter().map(|(_, b)| *b).collect(),
                            )),
                        )),
                        None => None,
                    })
                    .collect();
                Expression::Variadic(Operator::Mul, grouped)
            }
            other => other.apply_on_others(Expression::collect_like_muls),
        }
    }

    //Groups products with the same variables
    pub fn collect_like_adds(self) -> Expression {
        match self {
            Expression::Variadic(Operator::Add, exprs) => {
                let exprs = exprs
                    .into_iter()
                    .map(Expression::collect_like_adds)
                    .filter_map(|expr| match expr {
                        Expression::Variadic(Operator::Mul, exprs) => {
                            Some(exprs.into_iter().partition(|expr| {
                                matches!(expr, Expression::Lit(Term::Numeric(_)))
                            }))
                        }
                        expr @ Expression::Lit(Term::Numeric(_)) => Some((vec![expr], Vec::new())),
                        _ => None,
                    })
                    .collect::<Vec<(Vec<Expression>, Vec<Expression>)>>();

                let grouped =
                    group_similar_by(exprs, |(_, terms_a), (_, terms_b)| terms_a == terms_b)
                        .into_iter()
                        .map(|vec| {
                            let (coeffs, mut terms) = vec.into_iter().fold(
                                (Vec::new(), Vec::new()),
                                |(mut coeffs_acc, _), (mut coeffs_x, terms_x)| {
                                    coeffs_acc.append(&mut coeffs_x);
                                    (coeffs_acc, terms_x)
                                },
                            );
                            //let initial = if terms.is_empty() {Expression::integer_expression(0)} else {Expression::integer_expression(1)};
                            //let op_i128 = if terms.is_empty() {Expression::integer_expre

                            terms.push(coeffs.into_iter().fold(
                                Expression::integer_expression(0),
                                |acc, expr| match (acc, expr) {
                                    (
                                        Expression::Lit(Term::Numeric(a)),
                                        Expression::Lit(Term::Numeric(b)),
                                    ) => Expression::Lit(Term::Numeric(Literal::apply(
                                        a,
                                        b,
                                        i128::add,
                                        f64::add,
                                    ))),
                                    (acc, _) => acc,
                                },
                            ));
                            Expression::Variadic(Operator::Mul, terms)
                        })
                        .collect();

                Expression::Variadic(Operator::Add, grouped)
            }
            other => other.apply_on_others(Expression::collect_like_adds),
        }
    }

    pub fn distribute_exponents(self) -> Expression {
        match self {
            Expression::Binary(Operator::Exp, base, pow) => match *base {
                Expression::Variadic(Operator::Mul, exprs) => Expression::Variadic(
                    Operator::Mul,
                    exprs
                        .into_iter()
                        .map(|expr| match expr {
                            Expression::Binary(Operator::Exp, base, inner_pow) => {
                                Expression::Binary(
                                    Operator::Exp,
                                    base,
                                    Box::new(Expression::Variadic(
                                        Operator::Mul,
                                        vec![*pow.clone(), *inner_pow],
                                    )),
                                )
                            }
                            expr => Expression::Binary(Operator::Exp, Box::new(expr), pow.clone()),
                        })
                        .collect(),
                ),
                Expression::Binary(Operator::Exp, base, inner_pow) => Expression::Binary(
                    Operator::Exp,
                    base,
                    Box::new(Expression::Variadic(Operator::Mul, vec![*pow, *inner_pow])),
                ),
                _ => Expression::Binary(Operator::Exp, base, pow),
            },
            other => other.apply_on_others(Expression::distribute_exponents),
        }
    }

    pub fn simplify_exponents(self) -> Expression {
        match self {
            Expression::Binary(Operator::Exp, base, pow) => {
                let base = base.simplify_exponents();
                let pow = pow.simplify_exponents();
                if pow.is_zero() && !base.is_zero() {
                    Expression::integer_expression(1)
                } else if pow.is_one() || base.is_one() || (base.is_zero() && !pow.is_zero()) {
                    base
                } else {
                    Expression::Binary(Operator::Exp, Box::new(base), Box::new(pow))
                }
            }
            other => other.apply_on_others(Expression::simplify_exponents),
        }
    }
    //Evaluate constants literals in addition and multiplication nodes.
    pub fn fold_constants(self) -> Expression {
        match self {
            Expression::Variadic(operator, exprs) => {
                let (consts, mut vars): (Vec<Expression>, Vec<Expression>) = exprs
                    .into_iter()
                    .map(Expression::fold_constants)
                    .partition(|expr| matches!(expr, Expression::Lit(Term::Numeric(_))));
                let initial = match operator {
                    Operator::Add => Expression::integer_expression(0),
                    _ => Expression::integer_expression(1),
                };
                let op_i128 = match operator {
                    Operator::Add => i128::add,
                    _ => i128::mul,
                };
                let op_f64 = match operator {
                    Operator::Add => f64::add,
                    _ => f64::mul,
                };
                let result = consts.into_iter().fold(initial, |acc, x| match (acc, x) {
                    (Expression::Lit(Term::Numeric(a)), Expression::Lit(Term::Numeric(b))) => {
                        Expression::Lit(Term::Numeric(Literal::apply(a, b, op_i128, op_f64)))
                    }
                    (acc, _) => acc,
                });
                if vars.is_empty() {
                    result
                } else if (operator == Operator::Add && result.is_zero())
                    || (operator == Operator::Mul && result.is_one())
                {
                    if vars.len() == 1 {
                        vars.remove(0)
                    } else {
                        Expression::Variadic(operator, vars)
                    }
                } else if operator == Operator::Mul && result.is_zero() {
                    result
                } else {
                    vars.push(result);
                    Expression::Variadic(operator, vars)
                }
            }
            other => other.apply_on_others(Expression::fold_constants),
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
            .strip()
            .factor_out_neg()
            .factor_out_sub()
            .flatten()
            .remove_div_in_numer()
            .remove_div_in_denom()
            .remove_div_in_mul_node()
            .flatten()
            .explicit_exponents()
            .collect_like_muls()
            .flatten()
            .simplify_exponents()
            .fold_constants();
        if simplified == last_self {
            simplified.order()
        } else {
            simplified.simplify()
        }
    }

    fn divs_to_neg_exponents(self) -> Expression {
        match self {
            Expression::Binary(Operator::Div, a, b) => Expression::Variadic(
                Operator::Mul,
                vec![
                    a.divs_to_neg_exponents(),
                    Expression::Binary(
                        Operator::Exp,
                        Box::new(b.divs_to_neg_exponents()),
                        Box::new(Expression::integer_expression(-1)),
                    ),
                ],
            ),
            others => others.apply_on_others(Expression::divs_to_neg_exponents),
        }
    }

    fn neg_exponents_to_divs(self) -> Expression {
        match self {
            Expression::Binary(Operator::Exp, a, b) if b.is_less_than_zero() => {
                if let Expression::Lit(Term::Numeric(lit)) = *b {
                    let pow = Expression::Lit(Term::Numeric(Literal::apply(
                        lit,
                        Literal::Integer(-1),
                        i128::mul,
                        f64::mul,
                    )));
                    Expression::Binary(
                        Operator::Div,
                        Box::new(Expression::integer_expression(1)),
                        Box::new(Expression::Binary(
                            Operator::Exp,
                            Box::new(a.neg_exponents_to_divs()),
                            Box::new(pow),
                        )),
                    )
                } else {
                    Expression::Binary(Operator::Exp, a, b)
                }
            }
            others => others.apply_on_others(Expression::neg_exponents_to_divs),
        }
    }

    //An attempt at obtaining an easier to look at expression
    pub fn present(self) -> Expression {
        let last_self = self.clone();
        let simplified = self
            .strip()
            .divs_to_neg_exponents()
            .factor_out_neg()
            .factor_out_sub()
            .flatten()
            .remove_div_in_numer()
            .remove_div_in_denom()
            .remove_div_in_mul_node()
            .distribute_exponents()
            .flatten()
            .explicit_exponents()
            .collect_like_muls()
            .flatten()
            .simplify_exponents()
            .fold_constants()
            .explicit_coefficients()
            .collect_like_adds()
            .flatten()
            .simplify_exponents()
            .fold_constants()
            .distribute_exponents()
            .order();

        if simplified == last_self {
            simplified.neg_exponents_to_divs().present_phase_2()
        } else {
            simplified.present()
        }
    }
    fn present_phase_2(self) -> Expression {
        let last_self = self.clone();
        let simplified = self
            .strip()
            .remove_div_in_denom()
            .remove_div_in_numer()
            .remove_div_in_mul_node()
            .flatten()
            .simplify_exponents()
            .fold_constants();

        if simplified == last_self {
            simplified.order()
        } else {
            simplified.present_phase_2()
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
            Expression::Unary(Operator::Custom(f), x) if f == "ln" => {
                Expression::Binary(Operator::Div, Box::new(x.clone().derive(wrt)), x)
            }

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
}

fn group_similar_by<A: Clone, F: Fn(&A, &A) -> bool>(vec: Vec<A>, f: F) -> Vec<Vec<A>> {
    let mut output = Vec::new();
    let first = vec.first();
    if let Some(first) = first.cloned() {
        let (like_first, unlike_first) = vec.into_iter().partition(|x| f(x, &first));
        let mut grouped = group_similar_by(unlike_first, f);
        grouped.insert(0, like_first);
        output = grouped;
    }
    output
}
