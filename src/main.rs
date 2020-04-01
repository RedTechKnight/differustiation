use std::fmt;

fn main() {
    let mut expr = Expression::Operator(
        Function::Add,
        vec![
            Expression::Operator(
                Function::Add,
                vec![
                    Expression::Operand(Value::Variable('a')),
                    Expression::Operand(Value::Variable('b')),
                ],
            ),
            Expression::Operator(
                Function::Add,
                vec![
                    Expression::Operand(Value::Variable('c')),
                    Expression::Operand(Value::Variable('d')),
                ],
            ),
        ],
    );

    let mut div_expr = Expression::Operator(
        Function::Div,
        vec![
            Expression::Operator(
                Function::Div,
                vec![
                    Expression::Operand(Value::Variable('a')),
                    Expression::Operand(Value::Variable('b')),
                ],
            ),
            Expression::Operand(Value::Variable('c')),
        ],
    );
    div_expr.simplify_rational_1();
    expr.factor_subs();
    expr.factor_negs();
    println!("{}", expr);
    println!("{}", expr.flatten());
    println!("{}", div_expr);
}
impl Expression {
    fn factor_negs(&mut self) {
        match self {
            Expression::Operator(op @ Function::Neg, exprs) => {
                if exprs.len() != 1 {
                    panic!("")
                } else {
                    exprs[0].factor_negs();
                    exprs.insert(0, Expression::Operand(Value::Integer(-1)));
                    *op = Function::Mul;
                }
            }
            Expression::Operator(_, exprs) => exprs.iter_mut().for_each(Expression::factor_negs),
            _ => (),
        }
    }

    fn factor_subs(&mut self) {
        match self {
            Expression::Operator(op @ Function::Sub, exprs) => {
                if exprs.len() != 2 {
                    panic!("")
                } else {
                    exprs.iter_mut().for_each(Expression::factor_subs);
                    let rhs = exprs.pop().unwrap();
                    exprs.push(Expression::Operator(
                        Function::Mul,
                        vec![Expression::Operand(Value::Integer(-1)), rhs],
                    ));
                    *op = Function::Add;
                }
            }
            Expression::Operator(_, exprs) => exprs.iter_mut().for_each(Expression::factor_subs),

            _ => (),
        };
    }

    fn flatten(self) -> Self {
        match self {
            Expression::Operator(op @ Function::Add, exprs)
            | Expression::Operator(op @ Function::Mul, exprs) => {
                let get_operands = move |x| {
                    if let Expression::Operator(fun, operands) = x {
                        if op == fun {
                            Some(operands)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                };
                let (add, non_add) = exprs.into_iter().partition::<Vec<_>, _>(|expr| match expr {
                    Expression::Operator(fun, _) if *fun == op => true,
                    _ => false,
                });
                let add_ops = add
                    .into_iter()
                    .filter_map(get_operands)
                    .flatten()
                    .collect::<Vec<_>>();

                Expression::Operator(
                    op,
                    non_add
                        .into_iter()
                        .chain(add_ops)
                        .map(Expression::flatten)
                        .collect(),
                )
            }
            Expression::Operator(op, exprs) => {
                Expression::Operator(op, exprs.into_iter().map(Expression::flatten).collect())
            }
            other => other,
        }
    }

    fn simplify_rational_1(&mut self) {
        match self {
            Expression::Operator(op @ Function::Div, exprs) => {
                if exprs.len() != 2 {
                    panic!("")
                } else {
                    let lhs = exprs[0].clone();

                    if let Expression::Operator(Function::Div, mut expr) = lhs.clone() {
                        if expr.len() != 2 {
                            panic!()
                        } else {
                            let mut rhs = exprs.pop().unwrap();
                            rhs.simplify_rational_1();
                            exprs.pop();
                            let mut left = expr.remove(0);
                            expr[0].simplify_rational_1();
                            left.simplify_rational_1();
                            expr.insert(0, rhs);
                            exprs.push(left);
                            exprs.push(Expression::Operator(Function::Mul, expr));
                        }
                    }
                }
            }
            Expression::Operator(_, exprs) => {
                exprs.iter_mut().for_each(Expression::simplify_rational_1)
            }
            _ => (),
        }
    }
}

#[derive(Clone, Copy)]
enum Value {
    Integer(i128),
    Real(f64),
    Variable(char),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Value::Integer(i) => i.to_string(),
                Value::Real(f) => f.to_string(),
                Value::Variable(v) => v.to_string(),
            }
        )
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Function {
    Add,
    Mul,
    Sub,
    Div,
    Exp,
    Neg,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Function::Add => "+",
                Function::Mul => "*",
                Function::Sub => "-",
                Function::Div => "/",
                Function::Exp => "^",
                Function::Neg => "-",
            }
        )
    }
}

#[derive(Clone)]
enum Expression {
    Operand(Value),
    Operator(Function, Vec<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Expression::Operand(t) => format!("{}", t),
                Expression::Operator(fun, exprs) => format!(
                    "{} ({})",
                    fun,
                    exprs.iter().map(|x| format!("{} ", x)).collect::<String>()
                ),
            }
        )
    }
}
