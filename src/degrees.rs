// Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
///! This module provides floating point types that represent angles (in degrees) restricted to the
///! confines of a circle (i.e. their value is guaranteed to be in the range -180 to +180).
use num::traits::{Float, NumAssign, NumOps};
use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crate::{radians::Radians, AngleConst, RadiansConst};

#[derive(Serialize, Deserialize, Debug, Clone, Copy, Hash, Default)]
pub struct Degrees<F: Float + NumAssign + NumOps + AngleConst>(F);

impl<F: Float + NumAssign + NumOps + AngleConst> Degrees<F> {
    fn normalize<A: Into<F> + Copy>(arg: A) -> F {
        let mut result: F = arg.into();
        if !result.is_nan() {
            let half_circle = F::from(180.0).unwrap();
            if result > half_circle {
                while result > half_circle {
                    result -= F::from(360.0).unwrap();
                }
            } else if result < -half_circle {
                while result < -half_circle {
                    result += F::from(360.0).unwrap();
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
            Self(y.atan2(x).to_degrees())
        }
    }

    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    pub fn is_nan(self) -> bool {
        self.0.is_nan()
    }

    pub fn radians(self) -> F {
        self.0.to_radians()
    }

    pub fn degrees(self) -> F {
        self.0
    }

    pub fn opposite(self) -> Self {
        (self.0 + F::from(180.0).unwrap()).into()
    }

    pub fn cos(self) -> F {
        self.0.to_radians().cos()
    }

    pub fn sin(self) -> F {
        self.0.to_radians().sin()
    }

    pub fn tan(self) -> F {
        self.0.to_radians().tan()
    }

    /// For use during testing where limitations of float representation of real numbers
    /// means exact equivalence is unrealistic.
    pub fn approx_eq(self, other: Self) -> bool {
        if self.0.is_nan() {
            other.0.is_nan()
        } else if other.0.is_nan() {
            false
        } else if self.0 == F::from(0.0).unwrap() || other.0 == F::from(0.0).unwrap() {
            (self.0 + other.0).abs() < F::ANGLE_APPROX_EQ_LIMIT
        } else {
            ((self - other).0 / self.0).abs() < F::ANGLE_APPROX_EQ_LIMIT
        }
    }
}

impl<F: Float + NumAssign + NumOps + AngleConst> From<F> for Degrees<F> {
    fn from(f: F) -> Self {
        Self(Self::normalize(f))
    }
}

impl<F: Float + NumAssign + NumOps + AngleConst> From<(F, F)> for Degrees<F> {
    fn from(xy: (F, F)) -> Self {
        Self::atan2(xy.0, xy.1)
    }
}

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> From<Radians<F>> for Degrees<F> {
    fn from(radians: Radians<F>) -> Self {
        Self(radians.degrees())
    }
}

impl<F: Float + NumAssign + NumOps + AngleConst> Neg for Degrees<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::from(-self.0)
    }
}

impl<F: Float + NumAssign + NumOps + AngleConst> Add for Degrees<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self::from(self.0 + other.0)
    }
}

impl<F: Float + NumAssign + NumOps + AngleConst> AddAssign for Degrees<F> {
    fn add_assign(&mut self, other: Self) {
        self.0 = Self::normalize(self.0 + other.0)
    }
}

impl<F: Float + NumAssign + NumOps + AngleConst> Sub for Degrees<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Self::from(self.0 - other.0)
    }
}

impl<F: Float + NumAssign + NumOps + AngleConst> SubAssign for Degrees<F> {
    fn sub_assign(&mut self, other: Self) {
        self.0 = Self::normalize(self.0 - other.0)
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating equality i.e. -PI and PI are the same angle.
impl<F: Float + NumAssign + NumOps + AngleConst> PartialEq for Degrees<F> {
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
impl<F: Float + NumAssign + NumOps + AngleConst> PartialOrd for Degrees<F> {
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

impl<F, Scalar> Div<Scalar> for Degrees<F>
where
    F: Float + NumAssign + NumOps + AngleConst,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn div(self, rhs: Scalar) -> Self::Output {
        Degrees::from(self.0 / rhs.into())
    }
}

impl<F, Scalar> DivAssign<Scalar> for Degrees<F>
where
    F: Float + NumAssign + NumOps + AngleConst,
    Scalar: Into<F> + Copy,
{
    fn div_assign(&mut self, rhs: Scalar) {
        self.0 = Self::normalize(self.0 / rhs.into())
    }
}

impl<F, Scalar> Mul<Scalar> for Degrees<F>
where
    F: Float + NumAssign + NumOps + AngleConst,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self::Output {
        Degrees::from(self.0 * rhs.into())
    }
}

impl<F, Scalar> MulAssign<Scalar> for Degrees<F>
where
    F: Float + NumAssign + NumOps + AngleConst,
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
    fn default() {
        assert_eq!(Degrees::<f32>::default().degrees(), 0.0);
        assert_eq!(Degrees::<f64>::default().degrees(), 0.0);
    }

    #[test]
    fn radians() {
        assert!(Degrees::<f64>::from(-150.0).approx_eq(Radians::NEG_DEG_150.into()));
    }

    #[test]
    fn normalize() {
        assert_eq!(Degrees::<f64>::normalize(270.0), -90.0);
        assert_eq!(Degrees::<f64>::normalize(320.0), -40.0);
        assert_eq!(Degrees::<f64>::normalize(400.0), 40.0);
    }

    #[test]
    fn atan2() {
        assert!(Degrees::<f64>::atan2(0.0, 0.0).is_nan());
        assert!(!Degrees::<f64>::atan2(0.0, 0.01).is_nan());
        assert_eq!(Degrees::<f64>::atan2(0.0, 0.01).degrees(), 90.0);
        assert_eq!(Degrees::<f64>::atan2(0.0, -0.1).degrees(), -90.0);
        assert_eq!(Degrees::<f64>::atan2(0.1, 0.1).degrees(), 45.0);
        assert_eq!(Degrees::<f64>::atan2(-0.1, 0.1).degrees(), 135.0);
    }

    #[test]
    fn addition() {
        assert_eq!(
            Degrees::<f64>::from(30.0) + Degrees::<f64>::from(60.0),
            Degrees::<f64>::from(90.0)
        );
        let mut angle = Degrees::<f64>::from(15.0);
        angle += Degrees::<f64>::from(30.0);
        assert_eq!(angle.degrees(), 45.0);
    }

    #[test]
    fn subtraction() {
        assert_eq!(
            Degrees::<f64>::from(30.0) - Degrees::<f64>::from(60.0),
            Degrees::<f64>::from(-30.0)
        );
        let mut angle = Degrees::<f64>::from(15.0);
        angle -= Degrees::<f64>::from(30.0);
        assert!(angle.approx_eq(Degrees::<f64>::from(-15.0)));
    }

    #[test]
    fn compare() {
        assert!(Degrees::<f64>::from(-160.0) > Degrees::<f64>::from(160.0));
        assert!(Degrees::<f64>::from(30.0) > Degrees::<f64>::from(-30.0));
    }

    #[test]
    fn division() {
        assert_eq!(Degrees::<f64>::from(45.0) / 3.0, Degrees::<f64>::from(15.0));
        let mut angle = Degrees::<f64>::from(15.0);
        angle /= 3.0;
        assert!(angle.approx_eq(Degrees::<f64>::from(5.0)));
    }

    #[test]
    fn multiplication() {
        assert_eq!(
            Degrees::<f64>::from(45.0) * 3.0,
            Degrees::<f64>::from(135.0)
        );
        let mut angle = Degrees::<f64>::from(15.0);
        angle *= 3.0;
        assert!(angle.approx_eq(Degrees::<f64>::from(45.0)));
    }

    #[test]
    fn opposite() {
        assert!(Degrees::<f64>::from(45.0)
            .opposite()
            .approx_eq(Degrees::<f64>::from(-135.0)));
        assert!(Degrees::<f64>::from(-60.0)
            .opposite()
            .approx_eq(Degrees::<f64>::from(120.0)));
    }
}
