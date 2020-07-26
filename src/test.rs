mod tests {

    use crate::{Expression, Literal, Operator, Term};
    use quickcheck::{Arbitrary, Gen};

    use rand::prelude::*;
    impl Arbitrary for crate::Literal {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            match rand::random::<usize>() % 2 {
                0 => Literal::Integer(i128::arbitrary(g)),
                _ => Literal::Real(f64::arbitrary(g)),
            }
        }
    }

    impl Arbitrary for Term {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            match rand::random::<usize>() % 2 {
                0 => Term::Numeric(Literal::arbitrary(g)),
                _ => Term::Variable('x'),
            }
        }
    }

    impl Arbitrary for Expression {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            match rand::random::<usize>() % 3 {
                0 => Expression::Binary(
                    match rand::random::<usize>() % 5 {
                        0 => Operator::Add,
                        1 => Operator::Mul,
                        2 => Operator::Div,
                        3 => Operator::Sub,
                        _ => Operator::Exp,
                    },
                    Box::new(Expression::arbitrary(g)),
                    Box::new(Expression::arbitrary(g)),
                ),
                1 => Expression::Lit(Term::arbitrary(g)),
                _ => Expression::Unary(
                    match rand::random::<usize>() % 2 {
                        0 => Operator::Neg,
                        _ => Operator::Paren,
                    },
                    Box::new(Expression::arbitrary(g)),
                ),
            }
        }
    }
    fn no_neg_expr(expr: Expression) -> bool {
        match expr {
            Expression::Unary(Operator::Neg, _) => false,
            Expression::Unary(_, expr) => no_neg_expr(*expr),
            Expression::Binary(_, lhs, rhs) => no_neg_expr(*lhs) && no_neg_expr(*rhs),
            Expression::Variadic(_, exprs) => exprs.into_iter().all(no_neg_expr),
            _ => true,
        }
    }
    #[quickcheck]
    fn negs_factored_out(expr: Expression) -> bool {
        let new_expr = expr.factor_out_neg();
        no_neg_expr(new_expr)
    }

    fn no_sub_expr(expr: Expression) -> bool {
        match expr {
            Expression::Binary(Operator::Sub, _, _) => false,
            Expression::Unary(_, expr) => no_sub_expr(*expr),
            Expression::Binary(_, lhs, rhs) => no_sub_expr(*lhs) && no_sub_expr(*rhs),
            Expression::Variadic(_, exprs) => exprs.into_iter().all(no_sub_expr),
            _ => true,
        }
    }

    #[quickcheck]
    fn subs_factored_out(expr: Expression) -> bool {
        no_sub_expr(expr.factor_out_sub())
    }

    fn add_trees_flattened(expr: Expression) -> bool {
        match expr {
            Expression::Binary(Operator::Add, _, _) => false,
            Expression::Variadic(Operator::Add, exprs) => {
                !exprs.iter().any(|expr| {
                    matches!(
                        expr,
                        Expression::Binary(Operator::Add, _, _) |
                        Expression::Variadic(Operator::Add, _)
                    )
                }) && exprs.into_iter().all(add_trees_flattened)
            }
            Expression::Variadic(_, exprs) => exprs.into_iter().all(add_trees_flattened),
            Expression::Binary(_, lhs, rhs) => {
                add_trees_flattened(*lhs) && add_trees_flattened(*rhs)
            }
            Expression::Unary(_, expr) => add_trees_flattened(*expr),
            _ => true,
        }
    }

    #[quickcheck]
    fn add_trees_flatten(expr: Expression) -> bool {
        add_trees_flattened(expr.flatten_add())
    }

    fn mul_trees_flattened(expr: Expression) -> bool {
        match expr {
            Expression::Binary(Operator::Mul, _, _) => false,
            Expression::Variadic(Operator::Mul, exprs) => {
                !exprs.iter().any(|expr| {
                    matches!(
                        expr,
                        Expression::Binary(Operator::Mul, _, _) |
                        Expression::Variadic(Operator::Mul, _)
                    )
                }) && exprs.into_iter().all(mul_trees_flattened)
            }
            Expression::Variadic(_, exprs) => exprs.into_iter().all(mul_trees_flattened),
            Expression::Binary(_, lhs, rhs) => {
                mul_trees_flattened(*lhs) && mul_trees_flattened(*rhs)
            }
            Expression::Unary(_, expr) => mul_trees_flattened(*expr),
            _ => true,
        }
    }

    #[quickcheck]
    fn mul_trees_flatten(expr: Expression) -> bool {
        mul_trees_flattened(expr.flatten_mul())
    }
}
