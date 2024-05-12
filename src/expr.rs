use std::{
    fmt::{Debug, Display},
    ops::{self, *},
};

#[derive(Debug, Clone)]
enum Expr<T> {
    Leaf(T),
    Binary(Box<Expr<T>>, BinOp, Box<Expr<T>>),
    Unary(Box<Expr<T>>),
}

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    Xor,
    Shl,
    Shr,
}
impl BinOp {
    fn apply<T>(self, lhs: T, rhs: T) -> T
    where
        T: Add<T, Output = T>
            + Sub<T, Output = T>
            + Mul<T, Output = T>
            + Div<T, Output = T>
            + BitAnd<T, Output = T>
            + BitOr<T, Output = T>
            + BitXor<T, Output = T>
            + Shl<T, Output = T>
            + Shr<T, Output = T>
    {
        match self {
            BinOp::Add => lhs + rhs,
            BinOp::Sub => todo!(),
            BinOp::Mul => todo!(),
            BinOp::Div => todo!(),
            BinOp::And => todo!(),
            BinOp::Or => todo!(),
            BinOp::Xor => todo!(),
            BinOp::Shl => todo!(),
            BinOp::Shr => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnOp {
    Neg,
    Not,
    Flip,
}

pub trait Eval {
    type Result: Add + Sub + Mul + Div + BitAnd + BitOr + BitXor + Shl + Shr + Neg + Not;
    fn eval(&self) -> Self::Result;
}

impl<T: Eval> Eval for Expr<T> {
    type Result = T::Result;

    fn eval(&self) -> Self::Result {
        let x: bool = false;
        let y: f32 = x.into();

        match self {
            Expr::Leaf(val) => val.eval(),
            Expr::Binary(left, op, right) => todo!(),
            Expr::Unary(_) => todo!(),
        }
    }
}

pub trait Parse {
    type Input: Display;
    fn parse(input: &mut Self::Input);
}
