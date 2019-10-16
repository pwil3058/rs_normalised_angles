// Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
///! This module provides floating point types that represent angles (in degrees) restricted to the
///! confines of a circle (i.e. their value is guaranteed to be in the range -180 to +180).
use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crate::radians::*;
pub use float_plus::*;

pub trait DegreesConst: Copy {
    const DEG_0: Self;
    const DEG_30: Self;
    const DEG_45: Self;
    const DEG_60: Self;
    const DEG_90: Self;
    const DEG_120: Self;
    const DEG_135: Self;
    const DEG_150: Self;
    const DEG_180: Self;
    const DEG_360: Self;
    const NEG_DEG_30: Self;
    const NEG_DEG_45: Self;
    const NEG_DEG_60: Self;
    const NEG_DEG_90: Self;
    const NEG_DEG_120: Self;
    const NEG_DEG_135: Self;
    const NEG_DEG_150: Self;
    const NEG_DEG_180: Self;
}

#[derive(Serialize, Deserialize, Debug, Clone, Copy, Hash, Default)]
pub struct Degrees<F: FloatPlus + DegreesConst>(F);

impl<F: FloatPlus + DegreesConst> Degrees<F> {
    pub const DEG_0: Self = Self(F::DEG_0);
    pub const DEG_30: Self = Self(F::DEG_30);
    pub const DEG_45: Self = Self(F::DEG_45);
    pub const DEG_60: Self = Self(F::DEG_60);
    pub const DEG_90: Self = Self(F::DEG_90);
    pub const DEG_120: Self = Self(F::DEG_120);
    pub const DEG_135: Self = Self(F::DEG_135);
    pub const DEG_150: Self = Self(F::DEG_150);
    pub const DEG_180: Self = Self(F::DEG_180);
    pub const DEG_360: Self = Self(F::DEG_360);
    pub const NEG_DEG_30: Self = Self(F::NEG_DEG_30);
    pub const NEG_DEG_45: Self = Self(F::NEG_DEG_45);
    pub const NEG_DEG_60: Self = Self(F::NEG_DEG_60);
    pub const NEG_DEG_90: Self = Self(F::NEG_DEG_90);
    pub const NEG_DEG_120: Self = Self(F::NEG_DEG_120);
    pub const NEG_DEG_135: Self = Self(F::NEG_DEG_135);
    pub const NEG_DEG_150: Self = Self(F::NEG_DEG_150);
    pub const NEG_DEG_180: Self = Self(F::NEG_DEG_180);

    fn normalize<A: Into<F> + Copy>(arg: A) -> F {
        let mut result: F = arg.into();
        debug_assert!(result.is_finite());
        result %= F::DEG_360;
        if result > F::DEG_180 {
            result -= F::DEG_360;
        } else if result < F::NEG_DEG_180 {
            result += F::DEG_360;
        };
        result
    }

    pub fn asin(sin: F) -> Self {
        debug_assert!(sin >= F::NEG_ONE && sin <= F::ONE);
        Self(sin.asin().to_degrees())
    }

    pub fn acos(cos: F) -> Self {
        debug_assert!(cos >= F::NEG_ONE && cos <= F::ONE);
        Self(cos.acos().to_degrees())
    }

    pub fn atan2(y: F, x: F) -> Option<Self> {
        if x == F::ZERO && y == F::ZERO {
            None
        } else {
            Some(Self(y.atan2(x).to_degrees()))
        }
    }

    pub fn abs(self) -> Self {
        Self(self.0.abs())
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

    pub fn xy(self) -> (F, F) {
        debug_assert!(self.0.is_finite());
        (self.0.to_radians().cos(), self.0.to_radians().sin())
    }
}

impl<F: FloatPlus + DegreesConst> FloatApproxEq<F> for Degrees<F> {
    fn abs_diff(&self, other: &Self) -> F {
        (self.0 - other.0).abs() % F::DEG_360
    }

    fn rel_diff_scale_factor(&self, other: &Self) -> F {
        self.0.abs().max(other.0.abs())
    }
}

impl<F: FloatPlus + DegreesConst> From<F> for Degrees<F> {
    fn from(f: F) -> Self {
        debug_assert!(f.is_finite());
        Self(Self::normalize(f))
    }
}

impl<F: FloatPlus + DegreesConst> std::convert::TryFrom<(F, F)> for Degrees<F> {
    type Error = &'static str;

    fn try_from(xy: (F, F)) -> Result<Self, Self::Error> {
        if let Some(degrees) = Self::atan2(xy.1, xy.0) {
            Ok(degrees)
        } else {
            Err("(0.0, 0.0) cannot be converted to an angle")
        }
    }
}

impl<F: FloatPlus + DegreesConst + RadiansConst> From<Radians<F>> for Degrees<F> {
    fn from(radians: Radians<F>) -> Self {
        Self(radians.degrees())
    }
}

impl<F: FloatPlus + DegreesConst + RadiansConst> From<&Radians<F>> for Degrees<F> {
    fn from(radians: &Radians<F>) -> Self {
        Self(radians.degrees())
    }
}

impl<F: FloatPlus + DegreesConst> Neg for Degrees<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::from(-self.0)
    }
}

impl<F: FloatPlus + DegreesConst> Add for Degrees<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self::from(self.0 + other.0)
    }
}

impl<F: FloatPlus + DegreesConst> AddAssign for Degrees<F> {
    fn add_assign(&mut self, other: Self) {
        self.0 = Self::normalize(self.0 + other.0)
    }
}

impl<F: FloatPlus + DegreesConst> Sub for Degrees<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Self::from(self.0 - other.0)
    }
}

impl<F: FloatPlus + DegreesConst> SubAssign for Degrees<F> {
    fn sub_assign(&mut self, other: Self) {
        self.0 = Self::normalize(self.0 - other.0)
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating equality i.e. -PI and PI are the same angle.
impl<F: FloatPlus + DegreesConst> PartialEq for Degrees<F> {
    fn eq(&self, other: &Self) -> bool {
        debug_assert!(self.0.is_finite() && other.0.is_finite());
        (*self - *other).0 == F::from(0.0).unwrap()
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating order.
impl<F: FloatPlus + DegreesConst> PartialOrd for Degrees<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        debug_assert!(self.0.is_finite() && other.0.is_finite());
        let diff = (*self - *other).0;
        if diff < F::ZERO {
            Some(Ordering::Less)
        } else if diff > F::ZERO {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl<F, Scalar> Div<Scalar> for Degrees<F>
where
    F: FloatPlus + DegreesConst,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn div(self, rhs: Scalar) -> Self::Output {
        let rhs: F = rhs.into();
        debug_assert!(rhs.is_normal());
        Degrees::from(self.0 / rhs)
    }
}

impl<F, Scalar> DivAssign<Scalar> for Degrees<F>
where
    F: FloatPlus + DegreesConst,
    Scalar: Into<F> + Copy,
{
    fn div_assign(&mut self, rhs: Scalar) {
        let rhs: F = rhs.into();
        debug_assert!(rhs.is_normal());
        self.0 = Self::normalize(self.0 / rhs)
    }
}

impl<F, Scalar> Mul<Scalar> for Degrees<F>
where
    F: FloatPlus + DegreesConst,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self::Output {
        Degrees::from(self.0 * rhs.into())
    }
}

impl<F, Scalar> MulAssign<Scalar> for Degrees<F>
where
    F: FloatPlus + DegreesConst,
    Scalar: Into<F> + Copy,
{
    fn mul_assign(&mut self, rhs: Scalar) {
        self.0 = Self::normalize(self.0 * rhs.into())
    }
}

impl DegreesConst for f64 {
    const DEG_0: Self = 0.0;
    const DEG_30: Self = 30.0;
    const DEG_45: Self = 45.0;
    const DEG_60: Self = 60.0;
    const DEG_90: Self = 90.0;
    const DEG_120: Self = 120.0;
    const DEG_135: Self = 135.0;
    const DEG_150: Self = 150.0;
    const DEG_180: Self = 180.0;
    const DEG_360: Self = 360.0;
    const NEG_DEG_30: Self = -30.0;
    const NEG_DEG_45: Self = -45.0;
    const NEG_DEG_60: Self = -60.0;
    const NEG_DEG_90: Self = -90.0;
    const NEG_DEG_120: Self = -120.0;
    const NEG_DEG_135: Self = -135.0;
    const NEG_DEG_150: Self = -150.0;
    const NEG_DEG_180: Self = -180.0;
}

impl DegreesConst for f32 {
    const DEG_0: Self = 0.0;
    const DEG_30: Self = 30.0;
    const DEG_45: Self = 45.0;
    const DEG_60: Self = 60.0;
    const DEG_90: Self = 90.0;
    const DEG_120: Self = 120.0;
    const DEG_135: Self = 135.0;
    const DEG_150: Self = 150.0;
    const DEG_180: Self = 180.0;
    const DEG_360: Self = 360.0;
    const NEG_DEG_30: Self = -30.0;
    const NEG_DEG_45: Self = -45.0;
    const NEG_DEG_60: Self = -60.0;
    const NEG_DEG_90: Self = -90.0;
    const NEG_DEG_120: Self = -120.0;
    const NEG_DEG_135: Self = -135.0;
    const NEG_DEG_150: Self = -150.0;
    const NEG_DEG_180: Self = -180.0;
}

#[cfg(test)]
mod tests {
    use super::*;
    use float_plus::assert_approx_eq;

    #[test]
    fn default() {
        assert_eq!(Degrees::<f32>::default().degrees(), 0.0);
        assert_eq!(Degrees::<f64>::default().degrees(), 0.0);
    }

    #[test]
    fn radians() {
        assert_approx_eq!(
            Degrees::<f64>::from(-150.0),
            Radians::NEG_DEG_150_RAD.into()
        );
    }

    #[test]
    fn normalize() {
        assert_eq!(Degrees::<f64>::normalize(270.0), -90.0);
        assert_eq!(Degrees::<f64>::normalize(320.0), -40.0);
        assert_eq!(Degrees::<f64>::normalize(400.0), 40.0);
        assert_approx_eq!(Degrees::<f64>::DEG_180, Degrees::<f64>::NEG_DEG_180);
        assert_approx_ne!(Degrees::<f64>::DEG_90, Degrees::<f64>::NEG_DEG_90);
    }

    #[test]
    fn atan2() {
        assert!(Degrees::<f64>::atan2(0.0, 0.0).is_none());
        assert_eq!(Degrees::<f64>::atan2(0.01, 0.0).unwrap().degrees(), 90.0);
        assert_eq!(Degrees::<f64>::atan2(-0.1, 0.0).unwrap().degrees(), -90.0);
        assert_eq!(Degrees::<f64>::atan2(0.1, 0.1).unwrap().degrees(), 45.0);
        assert_eq!(Degrees::<f64>::atan2(0.1, -0.1).unwrap().degrees(), 135.0);
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
        assert_approx_eq!(angle, Degrees::<f64>::from(-15.0));
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
        assert_approx_eq!(angle, Degrees::<f64>::from(5.0));
    }

    #[test]
    fn multiplication() {
        assert_eq!(
            Degrees::<f64>::from(45.0) * 3.0,
            Degrees::<f64>::from(135.0)
        );
        let mut angle = Degrees::<f64>::from(15.0);
        angle *= 3.0;
        assert_approx_eq!(angle, Degrees::<f64>::from(45.0));
    }

    #[test]
    fn opposite() {
        assert_approx_eq!(
            Degrees::<f64>::from(45.0).opposite(),
            Degrees::<f64>::from(-135.0)
        );
        assert_approx_eq!(
            Degrees::<f64>::from(-60.0).opposite(),
            Degrees::<f64>::from(120.0)
        );
    }
}
