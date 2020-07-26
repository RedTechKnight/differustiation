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

                1 => Expression::Unary(
                    match rand::random::<usize>() % 2 {
                        0 => Operator::Paren,
                        _ => Operator::Neg,
                    },
                    Box::new(Expression::arbitrary(g)),
                ),
                _ => Expression::Lit(Term::arbitrary(g)),
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
        add_trees_flattened(expr.strip_paren().flatten_comm(&Operator::Add))
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
        mul_trees_flattened(expr.strip_paren().flatten_comm(&Operator::Mul))
    }

    fn no_nested_divs_1(expr: Expression) -> bool {
        match expr {
            Expression::Binary(Operator::Div, a, _)
                if matches!(*a, Expression::Binary(Operator::Div, _, _)) =>
            {
                false
            }
            Expression::Unary(_, expr) => no_nested_divs_1(*expr),
            Expression::Binary(_, lhs, rhs) => no_nested_divs_1(*lhs) && no_nested_divs_1(*rhs),
            Expression::Variadic(_, exprs) => exprs.into_iter().all(no_nested_divs_1),
            _ => true,
        }
    }

    #[quickcheck]
    fn no_nested_1(expr: Expression) -> bool {
        no_nested_divs_1(expr.strip_paren().simplify_rational_1())
    }

    #[quickcheck]
    fn no_nested_2(expr: Expression) -> bool {
        no_nested_divs_2(expr.strip_paren().simplify_rational_2())
    }

    fn no_nested_divs_2(expr: Expression) -> bool {
        match expr {
            Expression::Binary(Operator::Div, _, b)
                if matches!(*b, Expression::Binary(Operator::Div, _, _)) =>
            {
                false 
            }
            Expression::Unary(_, expr) => no_nested_divs_2(*expr),
            Expression::Binary(_, lhs, rhs) => no_nested_divs_2(*lhs) && no_nested_divs_2(*rhs),
            Expression::Variadic(_, exprs) => exprs.into_iter().all(no_nested_divs_2),
            _ => true,
        }
    }

    fn no_divs_in_muls(mut expr: Expression) -> bool {
        let mut last = expr.clone();
        match expr {
            Expression::Binary(Operator::Mul, a, b) => {
                !(matches!(*a, Expression::Binary(Operator::Div, _, _))
                    || matches!(*b, Expression::Binary(Operator::Div, _, _)))
                    && no_divs_in_muls(*a)
                    && no_divs_in_muls(*b)
            }
            Expression::Variadic(Operator::Mul, exprs) => {
                !exprs
                    .iter()
                    .any(|x| matches!(x, Expression::Binary(Operator::Div, _, _)))
                    && exprs.into_iter().all(no_divs_in_muls)
            }
            Expression::Unary(_, expr) => no_divs_in_muls(*expr),
            Expression::Binary(_, lhs, rhs) => no_divs_in_muls(*lhs) && no_divs_in_muls(*rhs),
            Expression::Variadic(_, exprs) => exprs.into_iter().all(no_divs_in_muls),
            _ => true,
        }
    }

    #[quickcheck]
    fn no_nested_3(expr: Expression) -> bool {
        no_divs_in_muls(
            expr.strip_paren()
                .flatten_comm(&Operator::Mul)
                .simplify_rational_3(),
        )
    }

    fn all_exponents_explicit(expr: Expression) -> bool {
        match expr {
            Expression::Variadic(Operator::Mul, exprs) => {
                exprs
                    .iter()
                    .all(|x| matches!(x, Expression::Binary(Operator::Exp, _, _)))
                    && exprs.into_iter().all(all_exponents_explicit)
            }
            Expression::Unary(_, expr) => all_exponents_explicit(*expr),
            Expression::Binary(_, lhs, rhs) => {
                all_exponents_explicit(*lhs) && all_exponents_explicit(*rhs)
            }
            Expression::Variadic(_, exprs) => exprs.into_iter().all(all_exponents_explicit),
            _ => true,
        }
    }
}
