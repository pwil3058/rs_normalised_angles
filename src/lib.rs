// Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
///! This crate provides floating point types that represent angles restricted to the confines
///! of a circle (i.e. their value is guaranteed to be in the range -PI to +PI).

#[macro_use]
extern crate serde_derive;

use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    hash::{Hash, Hasher},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub use float_plus::*;

pub mod degrees;
pub mod radians;

pub use crate::degrees::*;
pub use crate::radians::*;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum Angle<F: FloatPlus + RadiansConst + DegreesConst> {
    Degrees(Degrees<F>),
    Radians(Radians<F>),
}

impl<F: FloatPlus + RadiansConst + DegreesConst> Angle<F> {
    pub fn abs(&self) -> Self {
        match self {
            Angle::Degrees(degrees) => Angle::Degrees(degrees.abs()),
            Angle::Radians(radians) => Angle::Radians(radians.abs()),
        }
    }

    pub fn radians(&self) -> Radians<F> {
        match self {
            Angle::Degrees(degrees) => degrees.radians().into(),
            Angle::Radians(radians) => radians.radians().into(),
        }
    }

    pub fn degrees(&self) -> Degrees<F> {
        match self {
            Angle::Degrees(degrees) => degrees.degrees().into(),
            Angle::Radians(radians) => radians.degrees().into(),
        }
    }

    pub fn opposite(&self) -> Self {
        match self {
            Angle::Degrees(degrees) => Angle::Degrees(degrees.opposite()),
            Angle::Radians(radians) => Angle::Radians(radians.opposite()),
        }
    }

    pub fn cos(&self) -> F {
        match self {
            Angle::Degrees(degrees) => degrees.cos(),
            Angle::Radians(radians) => radians.cos(),
        }
    }

    pub fn sin(&self) -> F {
        match self {
            Angle::Degrees(degrees) => degrees.sin(),
            Angle::Radians(radians) => radians.sin(),
        }
    }

    pub fn tan(&self) -> F {
        match self {
            Angle::Degrees(degrees) => degrees.tan(),
            Angle::Radians(radians) => radians.tan(),
        }
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> FloatApproxEq<F> for Angle<F> {
    fn abs_diff(&self, other: &Self) -> F {
        match self {
            Angle::Degrees(degrees) => match other {
                Angle::Degrees(other) => degrees.abs_diff(other),
                Angle::Radians(other) => degrees.abs_diff(&other.into()),
            },
            Angle::Radians(radians) => match other {
                Angle::Degrees(other) => radians.abs_diff(&other.into()),
                Angle::Radians(other) => radians.abs_diff(other),
            },
        }
    }

    fn rel_diff_scale_factor(&self, other: &Self) -> F {
        match self {
            Angle::Degrees(degrees) => match other {
                Angle::Degrees(other) => degrees.rel_diff_scale_factor(other),
                Angle::Radians(other) => degrees.rel_diff_scale_factor(&other.into()),
            },
            Angle::Radians(radians) => match other {
                Angle::Degrees(other) => radians.rel_diff_scale_factor(&other.into()),
                Angle::Radians(other) => radians.rel_diff_scale_factor(other),
            },
        }
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> From<Radians<F>> for Angle<F> {
    fn from(radians: Radians<F>) -> Self {
        Angle::Radians(radians)
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> From<Degrees<F>> for Angle<F> {
    fn from(degrees: Degrees<F>) -> Self {
        Angle::Degrees(degrees)
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> Neg for Angle<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Angle::Degrees(degrees) => Angle::Degrees(degrees.neg()),
            Angle::Radians(radians) => Angle::Radians(radians.neg()),
        }
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> Add for Angle<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        match self {
            Angle::Degrees(degrees) => match other {
                Angle::Degrees(other) => Angle::Degrees(degrees.add(other)),
                Angle::Radians(other) => Angle::Degrees(degrees.add((other).into())),
            },
            Angle::Radians(radians) => match other {
                Angle::Degrees(other) => Angle::Radians(radians.add((other).into())),
                Angle::Radians(other) => Angle::Radians(radians.add(other)),
            },
        }
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> AddAssign for Angle<F> {
    fn add_assign(&mut self, other: Self) {
        match self {
            Angle::Degrees(ref mut degrees) => match other {
                Angle::Degrees(other) => degrees.add_assign(other),
                Angle::Radians(other) => degrees.add_assign(other.into()),
            },
            Angle::Radians(ref mut radians) => match other {
                Angle::Degrees(other) => radians.add_assign(other.into()),
                Angle::Radians(other) => radians.add_assign(other),
            },
        }
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> Sub for Angle<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        match self {
            Angle::Degrees(degrees) => match other {
                Angle::Degrees(other) => Angle::Degrees(degrees.sub(other)),
                Angle::Radians(other) => Angle::Degrees(degrees.sub((other).into())),
            },
            Angle::Radians(radians) => match other {
                Angle::Degrees(other) => Angle::Radians(radians.sub((other).into())),
                Angle::Radians(other) => Angle::Radians(radians.sub(other)),
            },
        }
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> SubAssign for Angle<F> {
    fn sub_assign(&mut self, other: Self) {
        match self {
            Angle::Degrees(ref mut degrees) => match other {
                Angle::Degrees(other) => degrees.sub_assign(other),
                Angle::Radians(other) => degrees.sub_assign(other.into()),
            },
            Angle::Radians(ref mut radians) => match other {
                Angle::Degrees(other) => radians.sub_assign(other.into()),
                Angle::Radians(other) => radians.sub_assign(other),
            },
        }
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating equality i.e. -PI and PI are the same angle.
impl<F: FloatPlus + RadiansConst + DegreesConst> PartialEq for Angle<F> {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Angle::Degrees(degrees) => match other {
                Angle::Degrees(other) => degrees.eq(other),
                Angle::Radians(other) => degrees.eq(&(*other).into()),
            },
            Angle::Radians(radians) => match other {
                Angle::Degrees(other) => radians.eq(&(*other).into()),
                Angle::Radians(other) => radians.eq(other),
            },
        }
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating equality i.e. -180 and 180 have the same hash value.
impl<F: FloatPlus + RadiansConst + DegreesConst + Hash> Hash for Angle<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let degrees: Degrees<F> = match *self {
            Angle::Degrees(angle) => angle,
            Angle::Radians(angle) => angle.into(),
        };
        degrees.hash(state);
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating order.
impl<F: FloatPlus + RadiansConst + DegreesConst> PartialOrd for Angle<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            Angle::Degrees(degrees) => match other {
                Angle::Degrees(other) => degrees.partial_cmp(other),
                Angle::Radians(other) => degrees.partial_cmp(&(*other).into()),
            },
            Angle::Radians(radians) => match other {
                Angle::Degrees(other) => radians.partial_cmp(&(*other).into()),
                Angle::Radians(other) => radians.partial_cmp(other),
            },
        }
    }
}

impl<F, Scalar> Div<Scalar> for Angle<F>
where
    F: FloatPlus + RadiansConst + DegreesConst,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn div(self, rhs: Scalar) -> Self::Output {
        match self {
            Angle::Degrees(degrees) => Angle::Degrees(degrees.div(rhs)),
            Angle::Radians(radians) => Angle::Radians(radians.div(rhs)),
        }
    }
}

impl<F, Scalar> DivAssign<Scalar> for Angle<F>
where
    F: FloatPlus + RadiansConst + DegreesConst,
    Scalar: Into<F> + Copy,
{
    fn div_assign(&mut self, rhs: Scalar) {
        match self {
            Angle::Degrees(ref mut degrees) => degrees.div_assign(rhs),
            Angle::Radians(ref mut radians) => radians.div_assign(rhs),
        }
    }
}

impl<F, Scalar> Mul<Scalar> for Angle<F>
where
    F: FloatPlus + RadiansConst + DegreesConst,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self::Output {
        match self {
            Angle::Degrees(degrees) => Angle::Degrees(degrees.mul(rhs)),
            Angle::Radians(radians) => Angle::Radians(radians.mul(rhs)),
        }
    }
}

impl<F, Scalar> MulAssign<Scalar> for Angle<F>
where
    F: FloatPlus + RadiansConst + DegreesConst,
    Scalar: Into<F> + Copy,
{
    fn mul_assign(&mut self, rhs: Scalar) {
        match self {
            Angle::Degrees(ref mut degrees) => degrees.mul_assign(rhs),
            Angle::Radians(ref mut radians) => radians.mul_assign(rhs),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn addition() {
        assert_eq!(
            Angle::<f64>::from(Degrees::from(30.0)) + Angle::<f64>::from(Degrees::from(60.0)),
            Angle::<f64>::from(Degrees::from(90.0))
        );
        let mut angle = Angle::<f64>::from(Degrees::from(15.0));
        angle += Angle::<f64>::from(Degrees::from(30.0));
        assert_eq!(angle.degrees().degrees(), 45.0);
    }

    #[test]
    fn subtraction() {
        assert_eq!(
            Angle::<f64>::from(Degrees::from(30.0)) - Angle::<f64>::from(Degrees::from(60.0)),
            Angle::<f64>::from(Degrees::from(-30.0))
        );
        let mut angle = Angle::<f64>::from(Degrees::from(15.0));
        angle -= Angle::<f64>::from(Degrees::from(30.0));
        assert_approx_eq!(angle, Angle::<f64>::from(Degrees::from(-15.0)));
    }

    #[test]
    fn compare() {
        assert!(
            Angle::<f64>::from(Degrees::from(-160.0)) > Angle::<f64>::from(Degrees::from(160.0))
        );
        assert!(Angle::<f64>::from(Degrees::from(30.0)) > Angle::<f64>::from(Degrees::from(-30.0)));
    }

    #[test]
    fn division() {
        assert_eq!(
            Angle::<f64>::from(Degrees::from(45.0)) / 3.0,
            Angle::<f64>::from(Degrees::from(15.0))
        );
        let mut angle = Angle::<f64>::from(Degrees::from(15.0));
        angle /= 3.0;
        assert_approx_eq!(angle, Angle::<f64>::from(Degrees::from(5.0)));
    }

    #[test]
    fn multiplication() {
        assert_eq!(
            Angle::<f64>::from(Degrees::from(45.0)) * 3.0,
            Angle::<f64>::from(Degrees::from(135.0))
        );
        let mut angle = Angle::<f64>::from(Degrees::from(15.0));
        angle *= 3.0;
        assert_approx_eq!(angle, Angle::<f64>::from(Degrees::from(45.0)));
    }

    #[test]
    fn opposite() {
        assert_approx_eq!(
            Angle::<f64>::from(Degrees::from(45.0)).opposite(),
            Angle::<f64>::from(Degrees::from(-135.0))
        );
        assert_approx_eq!(
            Angle::<f64>::from(Degrees::from(-60.0)).opposite(),
            Angle::<f64>::from(Degrees::from(120.0))
        );
    }
}
