mod tests {

    use crate::expression::{Expression, Literal, Operator, Term};
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    impl Arbitrary for Literal {
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
                _ => Term::Variable(char::arbitrary(g)),
            }
        }
    }
    fn sized_gen<G: Gen>(g: &mut G, max_depth: i32) -> Expression {
        if max_depth <= 0 {
            return Expression::Lit(Term::arbitrary(g));
        }
        match rand::random::<usize>() % 3 {
            0 => Expression::Binary(
                match rand::random::<usize>() % 5 {
                    0 => Operator::Add,
                    1 => Operator::Mul,
                    2 => Operator::Div,
                    3 => Operator::Sub,
                    _ => Operator::Exp,
                },
                Box::new(sized_gen(g, max_depth - 1)),
                Box::new(sized_gen(g, max_depth - 1)),
            ),

            1 => Expression::Unary(
                match rand::random::<usize>() % 2 {
                    0 => Operator::Paren,
                    _ => Operator::Neg,
                },
                Box::new(sized_gen(g, max_depth - 1)),
            ),
            _ => Expression::Lit(Term::arbitrary(g)),
        }
    }
    impl Arbitrary for Expression {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            sized_gen(g, 200)
        }
    }

    //These all test if the various expression simplification functions work as intended basically.

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
    fn negation_expressions_factored_out(expr: Expression) -> bool {
        no_neg_expr(expr.strip().factor_out_neg())
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
    fn subtraction_expressions_factored_out(expr: Expression) -> bool {
        no_sub_expr(expr.strip().factor_out_sub())
    }

    fn comm_trees_flattened(expr: Expression, operator: &Operator) -> bool {
        match expr {
            Expression::Binary(op, _, _) if &op == operator => false,
            Expression::Variadic(op, exprs) if &op == operator => {
                !exprs.iter().any(|expr| {
                    matches!(
                        expr,
                        Expression::Binary(op, _, _)|
                        Expression::Variadic(op, _) if op == operator
                    )
                }) && exprs
                    .into_iter()
                    .all(|expr| comm_trees_flattened(expr, operator))
            }
            Expression::Variadic(_, exprs) => exprs
                .into_iter()
                .all(|expr| comm_trees_flattened(expr, operator)),
            Expression::Binary(_, lhs, rhs) => {
                comm_trees_flattened(*lhs, operator) && comm_trees_flattened(*rhs, operator)
            }
            Expression::Unary(_, expr) => comm_trees_flattened(*expr, operator),
            _ => true,
        }
    }

    #[quickcheck]
    fn addition_operations_flattened(expr: Expression) -> bool {
        comm_trees_flattened(expr.strip().flatten_comm(&Operator::Add), &Operator::Add)
    }

    #[quickcheck]
    fn multiplication_operations_flattened(expr: Expression) -> bool {
        comm_trees_flattened(expr.strip().flatten_comm(&Operator::Mul), &Operator::Mul)
    }

    fn no_divs_in_numer(expr: Expression) -> bool {
        match expr {
            Expression::Binary(Operator::Div, a, _)
                if matches!(*a, Expression::Binary(Operator::Div, _, _)) =>
            {
                false
            }
            Expression::Unary(_, expr) => no_divs_in_numer(*expr),
            Expression::Binary(_, lhs, rhs) => no_divs_in_numer(*lhs) && no_divs_in_numer(*rhs),
            Expression::Variadic(_, exprs) => exprs.into_iter().all(no_divs_in_numer),
            _ => true,
        }
    }

    #[quickcheck]
    fn no_numerators_are_div_expressions(expr: Expression) -> bool {
        no_divs_in_numer(expr.strip().remove_div_in_numer())
    }

    fn no_divs_in_denom(expr: Expression) -> bool {
        match expr {
            Expression::Binary(Operator::Div, _, b)
                if matches!(*b, Expression::Binary(Operator::Div, _, _)) =>
            {
                false
            }
            Expression::Unary(_, expr) => no_divs_in_denom(*expr),
            Expression::Binary(_, lhs, rhs) => no_divs_in_denom(*lhs) && no_divs_in_denom(*rhs),
            Expression::Variadic(_, exprs) => exprs.into_iter().all(no_divs_in_denom),
            _ => true,
        }
    }

    #[quickcheck]
    fn no_denominators_are_div_expressions(expr: Expression) -> bool {
        no_divs_in_denom(expr.strip().remove_div_in_denom())
    }

    fn no_divs_in_muls(expr: Expression) -> bool {
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
    fn no_div_expressions_in_mul_expressions(expr: Expression) -> bool {
        no_divs_in_muls(
            expr.strip()
                .flatten_comm(&Operator::Mul)
                .remove_div_in_mul_node(),
        )
    }

    fn all_exponents_in_mul(expr: Expression) -> bool {
        match expr {
            Expression::Variadic(Operator::Mul, exprs) => {
                exprs
                    .iter()
                    .all(|x| matches!(x, Expression::Binary(Operator::Exp, _, _)))
                    && exprs.into_iter().all(all_exponents_in_mul)
            }
            Expression::Unary(_, expr) => all_exponents_in_mul(*expr),
            Expression::Binary(_, lhs, rhs) => {
                all_exponents_in_mul(*lhs) && all_exponents_in_mul(*rhs)
            }
            Expression::Variadic(_, exprs) => exprs.into_iter().all(all_exponents_in_mul),
            _ => true,
        }
    }

    #[quickcheck]
    fn all_expressions_in_mul_expression_are_exponents(expr: Expression) -> bool {
        all_exponents_in_mul(
            expr.strip()
                .flatten_comm(&Operator::Mul)
                .explicit_exponents(),
        )
    }

    fn no_repeating_bases(expr: Expression) -> bool {
        all_exponents_in_mul(expr.clone())
            && match expr {
                Expression::Variadic(Operator::Mul, exprs) if exprs.len() == 1 => {
                    exprs.into_iter().all(no_repeating_bases)
                }
                Expression::Variadic(Operator::Mul, exprs) => {
                    let mut bases = Vec::new();
                    for expr in &exprs {
                        if let Expression::Binary(Operator::Exp, base, _) = expr {
                            if bases.contains(&base) {
                                return false;
                            } else {
                                bases.push(base)
                            }
                        }
                    }
                    true && exprs.into_iter().all(no_repeating_bases)
                }
                Expression::Unary(_, expr) => no_repeating_bases(*expr),
                Expression::Binary(_, lhs, rhs) => {
                    no_repeating_bases(*lhs) && no_repeating_bases(*rhs)
                }
                Expression::Variadic(_, exprs) => exprs.into_iter().all(no_repeating_bases),
                _ => true,
            }
    }

    #[quickcheck]
    fn no_repeating_bases_in_mul_expression(expr: Expression) -> bool {
        no_repeating_bases(
            expr.strip()
                .flatten()
                .explicit_exponents()
                .collect_like_muls(),
        )
    }

    #[quickcheck]
    fn simplification_complete(expr: Expression) -> bool {
        let expr = expr.simplify();
        no_neg_expr(expr.clone())
            && no_sub_expr(expr.clone())
            && comm_trees_flattened(expr.clone(), &Operator::Add)
            && comm_trees_flattened(expr.clone(), &Operator::Mul)
            && no_divs_in_numer(expr.clone())
            && no_divs_in_denom(expr.clone())
            && no_divs_in_muls(expr.clone())
            && no_repeating_bases(expr.explicit_exponents())
    }
}
