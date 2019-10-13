// Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
///! This module provides floating point types that represent angles (in radians) restricted to the
///! confines of a circle (i.e. their value is guaranteed to be in the range -PI to +PI).
use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use float_plus::*;

use crate::degrees::Degrees;
use crate::DegreesConst;

pub trait RadiansConst: Copy {
    const DEG_0_RAD: Self;
    const DEG_30_RAD: Self;
    const DEG_45_RAD: Self;
    const DEG_60_RAD: Self;
    const DEG_90_RAD: Self;
    const DEG_120_RAD: Self;
    const DEG_135_RAD: Self;
    const DEG_150_RAD: Self;
    const DEG_180_RAD: Self;
    const DEG_360_RAD: Self;
    const NEG_DEG_30_RAD: Self;
    const NEG_DEG_45_RAD: Self;
    const NEG_DEG_60_RAD: Self;
    const NEG_DEG_90_RAD: Self;
    const NEG_DEG_120_RAD: Self;
    const NEG_DEG_135_RAD: Self;
    const NEG_DEG_150_RAD: Self;
    const NEG_DEG_180_RAD: Self;
}

#[derive(Serialize, Deserialize, Debug, Clone, Copy, Hash)]
pub struct Radians<F: FloatPlus + RadiansConst>(F);

impl<F: FloatPlus + RadiansConst> Radians<F> {
    pub const DEG_0_RAD: Self = Self(F::DEG_0_RAD);
    pub const DEG_30_RAD: Self = Self(F::DEG_30_RAD);
    pub const DEG_45_RAD: Self = Self(F::DEG_45_RAD);
    pub const DEG_60_RAD: Self = Self(F::DEG_60_RAD);
    pub const DEG_90_RAD: Self = Self(F::DEG_90_RAD);
    pub const DEG_120_RAD: Self = Self(F::DEG_120_RAD);
    pub const DEG_135_RAD: Self = Self(F::DEG_135_RAD);
    pub const DEG_150_RAD: Self = Self(F::DEG_150_RAD);
    pub const DEG_180_RAD: Self = Self(F::DEG_180_RAD);
    pub const NEG_DEG_30_RAD: Self = Self(F::NEG_DEG_30_RAD);
    pub const NEG_DEG_45_RAD: Self = Self(F::NEG_DEG_45_RAD);
    pub const NEG_DEG_60_RAD: Self = Self(F::NEG_DEG_60_RAD);
    pub const NEG_DEG_90_RAD: Self = Self(F::NEG_DEG_90_RAD);
    pub const NEG_DEG_120_RAD: Self = Self(F::NEG_DEG_120_RAD);
    pub const NEG_DEG_135_RAD: Self = Self(F::NEG_DEG_135_RAD);
    pub const NEG_DEG_150_RAD: Self = Self(F::NEG_DEG_150_RAD);
    pub const NEG_DEG_180_RAD: Self = Self(F::NEG_DEG_180_RAD);

    fn normalize<A: Into<F> + Copy>(arg: A) -> F {
        let mut result: F = arg.into();
        if !result.is_nan() {
            if result > F::DEG_180_RAD {
                while result > F::DEG_180_RAD {
                    result -= F::DEG_180_RAD * F::from(2.0).unwrap();
                }
            } else if result < -F::DEG_180_RAD {
                while result < -F::DEG_180_RAD {
                    result += F::DEG_180_RAD * F::from(2.0).unwrap();
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

    pub fn abs(self) -> Self {
        Self(self.0.abs())
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
        (self.0 + F::DEG_180_RAD).into()
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

    pub fn xy(self) -> (F, F) {
        if self.0.is_nan() {
            (F::from(0.0).unwrap(), F::from(0.0).unwrap())
        } else {
            (self.0.to_radians().cos(), self.0.to_radians().sin())
        }
    }
}

impl<F: FloatPlus + RadiansConst> FloatApproxEq<F> for Radians<F> {
    fn abs_diff(&self, other: &Self) -> F {
        (self.0 - other.0).abs() % F::DEG_360_RAD
    }

    fn rel_diff_scale_factor(&self, other: &Self) -> F {
        self.0.abs().max(other.0.abs())
    }
}

impl<F: FloatPlus + RadiansConst> From<F> for Radians<F> {
    fn from(f: F) -> Self {
        Self(Self::normalize(f))
    }
}

impl<F: FloatPlus + RadiansConst> From<(F, F)> for Radians<F> {
    fn from(xy: (F, F)) -> Self {
        Self::atan2(xy.0, xy.1)
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> From<Degrees<F>> for Radians<F> {
    fn from(degrees: Degrees<F>) -> Self {
        Self(degrees.radians())
    }
}

impl<F: FloatPlus + RadiansConst + DegreesConst> From<&Degrees<F>> for Radians<F> {
    fn from(degrees: &Degrees<F>) -> Self {
        Self(degrees.radians())
    }
}

impl<F: FloatPlus + RadiansConst> Neg for Radians<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::from(-self.0)
    }
}

impl<F: FloatPlus + RadiansConst> Add for Radians<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self::from(self.0 + other.0)
    }
}

impl<F: FloatPlus + RadiansConst> AddAssign for Radians<F> {
    fn add_assign(&mut self, other: Self) {
        self.0 = Self::normalize(self.0 + other.0)
    }
}

impl<F: FloatPlus + RadiansConst> Sub for Radians<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Self::from(self.0 - other.0)
    }
}

impl<F: FloatPlus + RadiansConst> SubAssign for Radians<F> {
    fn sub_assign(&mut self, other: Self) {
        self.0 = Self::normalize(self.0 - other.0)
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating equality i.e. -PI and PI are the same angle.
impl<F: FloatPlus + RadiansConst> PartialEq for Radians<F> {
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
impl<F: FloatPlus + RadiansConst> PartialOrd for Radians<F> {
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

impl<F, Scalar> Div<Scalar> for Radians<F>
where
    F: FloatPlus + RadiansConst,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn div(self, rhs: Scalar) -> Self::Output {
        Radians::from(self.0 / rhs.into())
    }
}

impl<F, Scalar> DivAssign<Scalar> for Radians<F>
where
    F: FloatPlus + RadiansConst,
    Scalar: Into<F> + Copy,
{
    fn div_assign(&mut self, rhs: Scalar) {
        self.0 = Self::normalize(self.0 / rhs.into())
    }
}

impl<F, Scalar> Mul<Scalar> for Radians<F>
where
    F: FloatPlus + RadiansConst,
    Scalar: Into<F> + Copy,
{
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self::Output {
        Radians::from(self.0 * rhs.into())
    }
}

impl<F, Scalar> MulAssign<Scalar> for Radians<F>
where
    F: FloatPlus + RadiansConst,
    Scalar: Into<F> + Copy,
{
    fn mul_assign(&mut self, rhs: Scalar) {
        self.0 = Self::normalize(self.0 * rhs.into())
    }
}

impl RadiansConst for f32 {
    const DEG_0_RAD: Self = 0.0;
    const DEG_30_RAD: Self = std::f32::consts::FRAC_PI_6;
    const DEG_45_RAD: Self = std::f32::consts::FRAC_PI_4;
    const DEG_60_RAD: Self = std::f32::consts::FRAC_PI_3;
    const DEG_90_RAD: Self = std::f32::consts::FRAC_PI_2;
    const DEG_120_RAD: Self = std::f32::consts::FRAC_PI_3 * 2.0;
    const DEG_135_RAD: Self = std::f32::consts::FRAC_PI_4 * 3.0;
    const DEG_150_RAD: Self = std::f32::consts::FRAC_PI_6 * 5.0;
    const DEG_180_RAD: Self = std::f32::consts::PI;
    const DEG_360_RAD: Self = std::f32::consts::PI * 2.0;
    const NEG_DEG_30_RAD: Self = -std::f32::consts::FRAC_PI_6;
    const NEG_DEG_45_RAD: Self = -std::f32::consts::FRAC_PI_4;
    const NEG_DEG_60_RAD: Self = -std::f32::consts::FRAC_PI_3;
    const NEG_DEG_90_RAD: Self = -std::f32::consts::FRAC_PI_2;
    const NEG_DEG_120_RAD: Self = -std::f32::consts::FRAC_PI_3 * 2.0;
    const NEG_DEG_135_RAD: Self = -std::f32::consts::FRAC_PI_4 * 3.0;
    const NEG_DEG_150_RAD: Self = -std::f32::consts::FRAC_PI_6 * 5.0;
    const NEG_DEG_180_RAD: Self = -std::f32::consts::PI;
}

impl RadiansConst for f64 {
    const DEG_0_RAD: Self = 0.0;
    const DEG_30_RAD: Self = std::f64::consts::FRAC_PI_6;
    const DEG_45_RAD: Self = std::f64::consts::FRAC_PI_4;
    const DEG_60_RAD: Self = std::f64::consts::FRAC_PI_3;
    const DEG_90_RAD: Self = std::f64::consts::FRAC_PI_2;
    const DEG_120_RAD: Self = std::f64::consts::FRAC_PI_3 * 2.0;
    const DEG_135_RAD: Self = std::f64::consts::FRAC_PI_4 * 3.0;
    const DEG_150_RAD: Self = std::f64::consts::FRAC_PI_6 * 5.0;
    const DEG_180_RAD: Self = std::f64::consts::PI;
    const DEG_360_RAD: Self = std::f64::consts::PI * 2.0;
    const NEG_DEG_30_RAD: Self = -std::f64::consts::FRAC_PI_6;
    const NEG_DEG_45_RAD: Self = -std::f64::consts::FRAC_PI_4;
    const NEG_DEG_60_RAD: Self = -std::f64::consts::FRAC_PI_3;
    const NEG_DEG_90_RAD: Self = -std::f64::consts::FRAC_PI_2;
    const NEG_DEG_120_RAD: Self = -std::f64::consts::FRAC_PI_3 * 2.0;
    const NEG_DEG_135_RAD: Self = -std::f64::consts::FRAC_PI_4 * 3.0;
    const NEG_DEG_150_RAD: Self = -std::f64::consts::FRAC_PI_6 * 5.0;
    const NEG_DEG_180_RAD: Self = -std::f64::consts::PI;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalize() {
        assert_eq!(
            Radians::<f64>::normalize(4.0),
            4.0_f64 - std::f64::consts::PI * 2.0
        );
    }

    #[test]
    fn degrees() {
        assert_approx_eq!(
            Radians::<f64>::NEG_DEG_150_RAD,
            Degrees::from(-150.0).into()
        );
    }

    #[test]
    fn atan2() {
        assert!(Radians::<f64>::atan2(0.0, 0.0).is_nan());
        assert!(!Radians::<f64>::atan2(0.0, 0.01).is_nan());
        assert_eq!(Radians::<f64>::atan2(0.0, 0.01).degrees(), 90.0);
        assert_eq!(Radians::<f64>::atan2(0.0, -0.1).degrees(), -90.0);
        assert_eq!(Radians::<f64>::atan2(0.1, 0.1).degrees(), 45.0);
        assert_eq!(Radians::<f64>::atan2(-0.1, 0.1).degrees(), 135.0);
    }

    #[test]
    fn addition() {
        assert_eq!(
            Radians::<f64>::from_degrees(30.0) + Radians::<f64>::from_degrees(60.0),
            Radians::<f64>::from_degrees(90.0)
        );
        let mut angle = Radians::<f64>::from_degrees(15.0);
        angle += Radians::<f64>::from_degrees(30.0);
        assert_eq!(angle.degrees(), 45.0);
    }

    #[test]
    fn subtraction() {
        assert_eq!(
            Radians::<f64>::from_degrees(30.0) - Radians::<f64>::from_degrees(60.0),
            Radians::<f64>::from_degrees(-30.0)
        );
        let mut angle = Radians::<f64>::from_degrees(15.0);
        angle -= Radians::<f64>::from_degrees(30.0);
        assert_approx_eq!(angle, Radians::<f64>::from_degrees(-15.0));
    }

    #[test]
    fn compare() {
        assert!(Radians::<f64>::from_degrees(-160.0) > Radians::<f64>::from_degrees(160.0));
        assert!(Radians::<f64>::from_degrees(30.0) > Radians::<f64>::from_degrees(-30.0));
    }

    #[test]
    fn division() {
        assert_eq!(
            Radians::<f64>::from_degrees(45.0) / 3.0,
            Radians::<f64>::from_degrees(15.0)
        );
        let mut angle = Radians::<f64>::from_degrees(15.0);
        angle /= 3.0;
        assert_approx_eq!(angle, Radians::<f64>::from_degrees(5.0));
    }

    #[test]
    fn multiplication() {
        assert_eq!(
            Radians::<f64>::from_degrees(45.0) * 3.0,
            Radians::<f64>::from_degrees(135.0)
        );
        let mut angle = Radians::<f64>::from_degrees(15.0);
        angle *= 3.0;
        assert_approx_eq!(angle, Radians::<f64>::from_degrees(45.0));
    }

    #[test]
    fn opposite() {
        assert_approx_eq!(
            Radians::<f64>::from_degrees(45.0).opposite(),
            Radians::<f64>::from_degrees(-135.0)
        );
        assert_approx_eq!(
            Radians::<f64>::from_degrees(-60.0).opposite(),
            Radians::<f64>::from_degrees(120.0)
        );
    }
}
