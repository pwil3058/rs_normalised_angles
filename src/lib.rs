// Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
///! This crate provides floating point types that represent angles restricted to the confines
///! of a circle (i.e. their value is guaranteed to be in the range -PI to +PI).

#[macro_use]
extern crate serde_derive;

use num::traits::{Float, FloatConst, NumAssign, NumOps};
use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
pub struct Angle<F: Float + FloatConst + NumAssign + NumOps>(F);

impl<F: Float + FloatConst + NumAssign + NumOps> Angle<F> {
    fn normalize<A: Into<F> + Copy>(arg: A) -> F {
        let mut result: F = arg.into();
        if !result.is_nan() {
            if result > F::PI() {
                while result > F::PI() {
                    result -= F::PI() * F::from(2.0).unwrap();
                }
            } else if result < -F::PI() {
                while result < -F::PI() {
                    result += F::PI() * F::from(2.0).unwrap();
                }
            }
        };
        result
    }

    pub fn atan2(x: F, y: F) -> Self {
        let zero = F::from(0.0).unwrap();
        if x == zero && y == zero {
            Self(F::nan())
        } else {
            Self(y.atan2(x))
        }
    }

    pub fn from_radians(f: F) -> Self {
        f.into()
    }

    pub fn from_degrees(f: F) -> Self {
        f.to_radians().into()
    }

    pub fn is_nan(self) -> bool {
        self.0.is_nan()
    }

    pub fn radians(self) -> F {
        self.0
    }

    pub fn degrees(self) -> F {
        self.0.to_degrees()
    }

    pub fn opposite(self) -> Self {
        (self.0 + F::PI()).into()
    }

    pub fn cos(self) -> F {
        self.0.cos()
    }

    pub fn sin(self) -> F {
        self.0.sin()
    }

    pub fn tan(self) -> F {
        self.0.tan()
    }
}

impl<F: Float + FloatConst + NumAssign + NumOps> From<F> for Angle<F> {
    fn from(f: F) -> Self {
        Self(Self::normalize(f))
    }
}

impl<F: Float + FloatConst + NumAssign + NumOps> Neg for Angle<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::from(-self.0)
    }
}

impl<F: Float + FloatConst + NumAssign + NumOps> Add for Angle<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self::from(self.0 + other.0)
    }
}

impl<F: Float + FloatConst + NumAssign + NumOps> AddAssign for Angle<F> {
    fn add_assign(&mut self, other: Self) {
        self.0 = Self::normalize(self.0 + other.0)
    }
}

impl<F: Float + FloatConst + NumAssign + NumOps> Sub for Angle<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Self::from(self.0 - other.0)
    }
}

impl<F: Float + FloatConst + NumAssign + NumOps> SubAssign for Angle<F> {
    fn sub_assign(&mut self, other: Self) {
        self.0 = Self::normalize(self.0 - other.0)
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating equality i.e. -PI and PI are the same angle.
impl<F: Float + FloatConst + NumAssign + NumOps> PartialEq for Angle<F> {
    fn eq(&self, other: &Self) -> bool {
        if self.0.is_nan() {
            other.0.is_nan()
        } else if other.0.is_nan() {
            false
        } else {
            (*self - *other).0 == F::from(0.0).unwrap()
        }
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating order.
impl<F: Float + FloatConst + NumAssign + NumOps> PartialOrd for Angle<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.0.is_nan() {
            if other.0.is_nan() {
                Some(Ordering::Equal)
            } else {
                None
            }
        } else if other.0.is_nan() {
            None
        } else {
            let diff = (*self - *other).0;
            if diff < F::from(0.0).unwrap() {
                Some(Ordering::Less)
            } else if diff > F::from(0.0).unwrap() {
                Some(Ordering::Greater)
            } else {
                Some(Ordering::Equal)
            }
        }
    }
}

impl<F, Scalar> Div<Scalar> for Angle<F>
where
    F: Float + FloatConst + NumAssign + NumOps,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn div(self, rhs: Scalar) -> Self::Output {
        Angle::from(self.0 / rhs.into())
    }
}

impl<F, Scalar> DivAssign<Scalar> for Angle<F>
where
    F: Float + FloatConst + NumAssign + NumOps,
    Scalar: Into<F> + Copy,
{
    fn div_assign(&mut self, rhs: Scalar) {
        self.0 = Self::normalize(self.0 / rhs.into())
    }
}

impl<F, Scalar> Mul<Scalar> for Angle<F>
where
    F: Float + FloatConst + NumAssign + NumOps,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self::Output {
        Angle::from(self.0 * rhs.into())
    }
}

impl<F, Scalar> MulAssign<Scalar> for Angle<F>
where
    F: Float + FloatConst + NumAssign + NumOps,
    Scalar: Into<F> + Copy,
{
    fn mul_assign(&mut self, rhs: Scalar) {
        self.0 = Self::normalize(self.0 * rhs.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalize() {
        assert_eq!(
            Angle::<f64>::normalize(4.0),
            4.0_f64 - std::f64::consts::PI * 2.0
        );
    }

    #[test]
    fn atan2() {
        assert!(Angle::<f64>::atan2(0.0, 0.0).is_nan());
        assert!(!Angle::<f64>::atan2(0.0, 0.01).is_nan());
        assert_eq!(Angle::<f64>::atan2(0.0, 0.01).degrees(), 90.0);
        assert_eq!(Angle::<f64>::atan2(0.0, -0.1).degrees(), -90.0);
        assert_eq!(Angle::<f64>::atan2(0.1, 0.1).degrees(), 45.0);
        assert_eq!(Angle::<f64>::atan2(-0.1, 0.1).degrees(), 135.0);
    }

    #[test]
    fn addition() {
        assert_eq!(
            Angle::<f64>::from_degrees(30.0) + Angle::<f64>::from_degrees(60.0),
            Angle::<f64>::from_degrees(90.0)
        );
        let mut angle = Angle::<f64>::from_degrees(15.0);
        angle += Angle::<f64>::from_degrees(30.0);
        assert_eq!(angle.degrees(), 45.0);
    }

    #[test]
    fn subtraction() {
        assert_eq!(
            Angle::<f64>::from_degrees(30.0) - Angle::<f64>::from_degrees(60.0),
            Angle::<f64>::from_degrees(-30.0)
        );
        let mut angle = Angle::<f64>::from_degrees(15.0);
        angle -= Angle::<f64>::from_degrees(30.0);
        assert_eq!(angle.degrees().round(), -15.0);
    }

    #[test]
    fn compare() {
        assert!(Angle::<f64>::from_degrees(-160.0) > Angle::<f64>::from_degrees(160.0));
        assert!(Angle::<f64>::from_degrees(30.0) > Angle::<f64>::from_degrees(-30.0));
    }

    #[test]
    fn division() {
        assert_eq!(
            Angle::<f64>::from_degrees(45.0) / 3.0,
            Angle::<f64>::from_degrees(15.0)
        );
        let mut angle = Angle::<f64>::from_degrees(15.0);
        angle /= 3.0;
        assert_eq!(angle.degrees().round(), 5.0);
    }

    #[test]
    fn multiplication() {
        assert_eq!(
            Angle::<f64>::from_degrees(45.0) * 3.0,
            Angle::<f64>::from_degrees(135.0)
        );
        let mut angle = Angle::<f64>::from_degrees(15.0);
        angle *= 3.0;
        assert_eq!(angle.degrees().round(), 45.0);
    }

    #[test]
    fn opposite() {
        assert_eq!(
            Angle::<f64>::from_degrees(45.0)
                .opposite()
                .degrees()
                .round(),
            Angle::<f64>::from_degrees(-135.0).degrees().round()
        );
        assert_eq!(
            Angle::<f64>::from_degrees(-60.0)
                .opposite()
                .degrees()
                .round(),
            Angle::<f64>::from_degrees(120.0).degrees().round()
        );
    }
}
