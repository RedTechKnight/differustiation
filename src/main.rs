fn main() {
    println!(
        "{:?}",
        Expression::binary_expression(
            Operator::Mul,
            Expression::real_expression(1.232),
            Expression::binary_expression(
                Operator::Div,
                Expression::real_expression(2.2323),
                Expression::binary_expression(
                    Operator::Div,
                    Expression::real_expression(23.33),
                    Expression::binary_expression(
                        Operator::Add,
                        Expression::real_expression(1.0),
                        Expression::variable_expression('a')
                    )
                )
            )
        )
        .factor_out_sub()
        .flatten_add()
        .flatten_mul()
        .simplify_rational_1()
        .simplify_rational_2()
        .simplify_rational_3()
        .flatten_mul()
        .explicit_exponents()
        .explicit_coefficients()
        .explicit_exponents()
    );
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
enum Literal {
    Integer(i128),
    Real(f64),
}

impl Literal {
    fn new_real_literal(a: f64) -> Literal {
        Literal::Real(a)
    }

    fn new_integer_literal(a: i128) -> Literal {
        Literal::Integer(a)
    }

    fn on_reals<F: Fn(f64, f64) -> f64>(f: F, a: Literal, b: Literal) -> Option<Literal> {
        if let Literal::Real(a) = a {
            match b {
                Literal::Real(b) => return Some(Literal::Real(f(a, b))),
                Literal::Integer(b) => return Some(Literal::Real(f(a, b as f64))),
            }
        }
        None
    }

    fn on_integers<F: Fn(i128, i128) -> i128>(f: F, a: Literal, b: Literal) -> Option<Literal> {
        if let Literal::Integer(a) = a {
            if let Literal::Integer(b) = b {
                return Some(Literal::Integer(f(a, b)));
            }
        }
        None
    }

    fn as_integer(self) -> Literal {
        if let Literal::Real(a) = self {
            return Literal::Integer(a as i128);
        }
        self
    }

    fn as_real(self) -> Literal {
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

impl Term {
    fn real_term(a: f64) -> Term {
        Term::Numeric(Literal::new_real_literal(a))
    }

    fn integer_term(a: i128) -> Term {
        Term::Numeric(Literal::new_integer_literal(a))
    }

    fn variable_term(a: char) -> Term {
        Term::Variable(a)
    }

    fn get_real(self) -> Option<f64> {
        if let Term::Numeric(Literal::Real(a)) = self {
            return Some(a);
        }
        None
    }

    fn get_integer(self) -> Option<i128> {
        if let Term::Numeric(Literal::Integer(a)) = self {
            return Some(a);
        }
        None
    }

    fn get_variable(self) -> Option<char> {
        if let Term::Variable(a) = self {
            return Some(a);
        }
        None
    }
}
#[derive(Debug, Clone, PartialOrd, PartialEq)]
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

#[derive(Debug, Clone, PartialOrd, PartialEq)]
enum Expression {
    Lit(Term),
    Unary(Operator, Box<Expression>),
    Binary(Operator, Box<Expression>, Box<Expression>),
    Variadic(Operator, Vec<Expression>),
}

impl Expression {
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

    fn get_literal(self) -> Option<Term> {
        if let (Expression::Lit(a)) = self {
            return Some(a);
        }
        None
    }

    fn get_unary_expression(self) -> Option<(Operator, Expression)> {
        if let (Expression::Unary(f, a)) = self {
            return Some((f, *a));
        }
        None
    }

    fn get_binary_expression(self) -> Option<(Operator, Expression, Expression)> {
        if let (Expression::Binary(f, a, b)) = self {
            return Some((f, *a, *b));
        }
        None
    }

    fn get_variadic_expression(self) -> Option<(Operator, Vec<Expression>)> {
        if let Expression::Variadic(f, exprs) = self {
            return Some((f, exprs));
        }
        None
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.factor_out_neg()),
            Expression::Binary(f, a, b) => {
                Expression::binary_expression(f, a.factor_out_neg(), b.factor_out_neg())
            }
            Expression::Variadic(f, exprs) => Expression::variadic_expression(
                f,
                exprs.into_iter().map(Expression::factor_out_neg).collect(),
            ),
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.factor_out_sub()),
            Expression::Binary(f, a, b) => {
                Expression::binary_expression(f, a.factor_out_sub(), b.factor_out_sub())
            }
            Expression::Variadic(f, exprs) => Expression::variadic_expression(
                f,
                exprs
                    .into_iter()
                    .map(Expression::factor_out_sub)
                    .collect::<Vec<Expression>>(),
            ),
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.flatten_add()),
            Expression::Binary(f, a, b) => {
                Expression::binary_expression(f, a.flatten_add(), b.flatten_add())
            }
            Expression::Variadic(f, exprs) => {
                Expression::Variadic(f, exprs.into_iter().map(Expression::flatten_add).collect())
            }
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.flatten_mul()),
            Expression::Binary(f, a, b) => {
                Expression::binary_expression(f, a.flatten_mul(), b.flatten_mul())
            }
            Expression::Variadic(f, exprs) => {
                Expression::Variadic(f, exprs.into_iter().map(Expression::flatten_mul).collect())
            }
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.simplify_rational_1()),
            Expression::Binary(f, a, b) => {
                Expression::binary_expression(f, a.simplify_rational_1(), b.simplify_rational_1())
            }
            Expression::Variadic(f, exprs) => Expression::variadic_expression(
                f,
                exprs
                    .into_iter()
                    .map(Expression::simplify_rational_1)
                    .collect(),
            ),
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.simplify_rational_2()),
            Expression::Binary(f, a, b) => {
                Expression::binary_expression(f, a.simplify_rational_2(), b.simplify_rational_2())
            }
            Expression::Variadic(f, exprs) => Expression::variadic_expression(
                f,
                exprs
                    .into_iter()
                    .map(Expression::simplify_rational_2)
                    .collect(),
            ),
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.simplify_rational_3()),
            Expression::Binary(f, a, b) => {
                Expression::binary_expression(f, a.simplify_rational_3(), b.simplify_rational_3())
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
            Expression::Variadic(f, exprs) => Expression::variadic_expression(
                f,
                exprs
                    .into_iter()
                    .map(Expression::simplify_rational_3)
                    .collect(),
            ),
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.explicit_exponents()),
            Expression::Binary(f, a, b) => {
                Expression::binary_expression(f, a.explicit_exponents(), b.explicit_exponents())
            }
            Expression::Variadic(f, exprs) => Expression::variadic_expression(
                f,
                exprs
                    .into_iter()
                    .map(Expression::explicit_exponents)
                    .collect(),
            ),
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
            l @ Expression::Lit(_) => l,
            Expression::Unary(f, a) => Expression::unary_expression(f, a.explicit_coefficients()),
            Expression::Binary(f, a, b) => Expression::binary_expression(
                f,
                a.explicit_coefficients(),
                b.explicit_coefficients(),
            ),
            Expression::Variadic(f, exprs) => Expression::variadic_expression(
                f,
                exprs
                    .into_iter()
                    .map(Expression::explicit_coefficients)
                    .collect(),
            ),
        }
    }
}
