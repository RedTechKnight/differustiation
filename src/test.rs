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
                _ => Term::Variable(char::arbitrary(g)),
            }
        }
    }

    impl Arbitrary for Expression {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            match rand::random::<usize>() % 4 {
                0 => Expression::Lit(Term::arbitrary(g)),
                1 => Expression::Unary(
                    match rand::random::<usize>() % 2 {
                        0 => Operator::Neg,
                        _ => Operator::Paren,
                    },
                    Box::new(Expression::arbitrary(g)),
                ),
                2 => Expression::Binary(
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
                _ => Expression::Variadic(
                    match rand::random::<usize>() % 2 {
                        0 => Operator::Add,
                        _ => Operator::Mul,
                    },
                    Vec::new(),
                ),
            }
        }
    }
    fn recursive(expr: Expression) -> bool {
        match expr {
            Expression::Unary(Operator::Neg, _) => false,
            Expression::Unary(_, expr) => recursive(*expr),
            Expression::Binary(_, lhs, rhs) => recursive(*lhs) && recursive(*rhs),
            Expression::Variadic(_, exprs) => exprs.into_iter().all(recursive),
            _ => true,
        }
    }
    #[quickcheck]
    fn negs_factored_out(expr: Expression) -> bool {
        recursive(expr.factor_out_neg())
    }
}
