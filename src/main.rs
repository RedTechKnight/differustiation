use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};

fn main() {}


#[derive(Clone, Copy, Debug,PartialEq, PartialOrd)]
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
		Literal::Real(b) => return Some(Literal::Real(f(a,b))),
		Literal::Integer(b) => return Some(Literal::Real(f(a,b as f64)))
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
	    return Literal::Integer(a as i128)
	}
	self
    }

    fn as_real(self) -> Literal {
	if let Literal::Integer(a) = self {
	    return Literal::Real(a as f64)
	}
	self
    }

}
#[derive(Debug,Clone,Copy,PartialOrd,PartialEq)]
enum Term {
    Numeric(Literal),
    Variable(char)
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
	    return Some(a)
	}
	None
    }

    fn get_variable(self) -> Option<char> {
	if let Term::Variable(a) = self {
	    return Some(a)
	}
	None
    }
}
