// Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
///! This crate provides floating point types that represent angles restricted to the confines
///! of a circle (i.e. their value is guaranteed to be in the range -PI to +PI).

#[macro_use]
extern crate serde_derive;

use num::traits::{Float, NumAssign, NumOps};
use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub mod degrees;
pub mod radians;

pub use crate::degrees::*;
pub use crate::radians::*;

#[derive(Serialize, Deserialize, Debug, Clone, Hash)]
pub enum Angle<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> {
    Degrees(Degrees<F>),
    Radians(Radians<F>),
}

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> Angle<F> {
    pub fn abs(&self) -> Self {
        match self {
            Angle::Degrees(degrees) => Angle::Degrees(degrees.abs()),
            Angle::Radians(radians) => Angle::Radians(radians.abs()),
        }
    }

    pub fn is_nan(&self) -> bool {
        match self {
            Angle::Degrees(degrees) => degrees.is_nan(),
            Angle::Radians(radians) => radians.is_nan(),
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

    /// For use during testing where limitations of float representation of real numbers
    /// means exact equivalence is unrealistic.
    pub fn approx_eq(&self, other: &Self) -> bool {
        match self {
            Angle::Degrees(degrees) => match other {
                Angle::Degrees(other) => degrees.approx_eq(*other),
                Angle::Radians(other) => degrees.approx_eq((*other).into()),
            },
            Angle::Radians(radians) => match other {
                Angle::Degrees(other) => radians.approx_eq((*other).into()),
                Angle::Radians(other) => radians.approx_eq(*other),
            },
        }
    }
}

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> From<Radians<F>> for Angle<F> {
    fn from(radians: Radians<F>) -> Self {
        Angle::Radians(radians)
    }
}

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> From<Degrees<F>> for Angle<F> {
    fn from(degrees: Degrees<F>) -> Self {
        Angle::Degrees(degrees)
    }
}

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> Neg for Angle<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Angle::Degrees(degrees) => Angle::Degrees(degrees.neg()),
            Angle::Radians(radians) => Angle::Radians(radians.neg()),
        }
    }
}

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> Add for Angle<F> {
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

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> AddAssign for Angle<F> {
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

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> Sub for Angle<F> {
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

impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> SubAssign for Angle<F> {
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
impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> PartialEq for Angle<F> {
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
/// evaluating order.
impl<F: Float + NumAssign + NumOps + RadiansConst + AngleConst> PartialOrd for Angle<F> {
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
    F: Float + NumAssign + NumOps + RadiansConst + AngleConst,
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
    F: Float + NumAssign + NumOps + RadiansConst + AngleConst,
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
    F: Float + NumAssign + NumOps + RadiansConst + AngleConst,
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
    F: Float + NumAssign + NumOps + RadiansConst + AngleConst,
    Scalar: Into<F> + Copy,
{
    fn mul_assign(&mut self, rhs: Scalar) {
        match self {
            Angle::Degrees(ref mut degrees) => degrees.mul_assign(rhs),
            Angle::Radians(ref mut radians) => radians.mul_assign(rhs),
        }
    }
}

pub trait RadiansConst: AngleConst {
    const DEG_0: Self;
    const DEG_30: Self;
    const DEG_45: Self;
    const DEG_60: Self;
    const DEG_90: Self;
    const DEG_120: Self;
    const DEG_135: Self;
    const DEG_150: Self;
    const DEG_180: Self;
    const NEG_DEG_30: Self;
    const NEG_DEG_45: Self;
    const NEG_DEG_60: Self;
    const NEG_DEG_90: Self;
    const NEG_DEG_120: Self;
    const NEG_DEG_135: Self;
    const NEG_DEG_150: Self;
    const NEG_DEG_180: Self;
}

pub trait AngleConst {
    const ANGLE_APPROX_EQ_LIMIT: Self;
}

impl RadiansConst for f32 {
    const DEG_0: Self = 0.0;
    const DEG_30: Self = std::f32::consts::FRAC_PI_6;
    const DEG_45: Self = std::f32::consts::FRAC_PI_4;
    const DEG_60: Self = std::f32::consts::FRAC_PI_3;
    const DEG_90: Self = std::f32::consts::FRAC_PI_2;
    const DEG_120: Self = std::f32::consts::FRAC_PI_3 * 2.0;
    const DEG_135: Self = std::f32::consts::FRAC_PI_4 * 3.0;
    const DEG_150: Self = std::f32::consts::FRAC_PI_6 * 5.0;
    const DEG_180: Self = std::f32::consts::PI;
    const NEG_DEG_30: Self = -std::f32::consts::FRAC_PI_6;
    const NEG_DEG_45: Self = -std::f32::consts::FRAC_PI_4;
    const NEG_DEG_60: Self = -std::f32::consts::FRAC_PI_3;
    const NEG_DEG_90: Self = -std::f32::consts::FRAC_PI_2;
    const NEG_DEG_120: Self = -std::f32::consts::FRAC_PI_3 * 2.0;
    const NEG_DEG_135: Self = -std::f32::consts::FRAC_PI_4 * 3.0;
    const NEG_DEG_150: Self = -std::f32::consts::FRAC_PI_6 * 5.0;
    const NEG_DEG_180: Self = -std::f32::consts::PI;
}

impl AngleConst for f32 {
    const ANGLE_APPROX_EQ_LIMIT: Self = 0.000001;
}

impl RadiansConst for f64 {
    const DEG_0: Self = 0.0;
    const DEG_30: Self = std::f64::consts::FRAC_PI_6;
    const DEG_45: Self = std::f64::consts::FRAC_PI_4;
    const DEG_60: Self = std::f64::consts::FRAC_PI_3;
    const DEG_90: Self = std::f64::consts::FRAC_PI_2;
    const DEG_120: Self = std::f64::consts::FRAC_PI_3 * 2.0;
    const DEG_135: Self = std::f64::consts::FRAC_PI_4 * 3.0;
    const DEG_150: Self = std::f64::consts::FRAC_PI_6 * 5.0;
    const DEG_180: Self = std::f64::consts::PI;
    const NEG_DEG_30: Self = -std::f64::consts::FRAC_PI_6;
    const NEG_DEG_45: Self = -std::f64::consts::FRAC_PI_4;
    const NEG_DEG_60: Self = -std::f64::consts::FRAC_PI_3;
    const NEG_DEG_90: Self = -std::f64::consts::FRAC_PI_2;
    const NEG_DEG_120: Self = -std::f64::consts::FRAC_PI_3 * 2.0;
    const NEG_DEG_135: Self = -std::f64::consts::FRAC_PI_4 * 3.0;
    const NEG_DEG_150: Self = -std::f64::consts::FRAC_PI_6 * 5.0;
    const NEG_DEG_180: Self = -std::f64::consts::PI;
}

impl AngleConst for f64 {
    const ANGLE_APPROX_EQ_LIMIT: Self = 0.0000000001;
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
        assert!(angle.approx_eq(&Angle::<f64>::from(Degrees::from(-15.0))));
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
        assert!(angle.approx_eq(&Angle::<f64>::from(Degrees::from(5.0))));
    }

    #[test]
    fn multiplication() {
        assert_eq!(
            Angle::<f64>::from(Degrees::from(45.0)) * 3.0,
            Angle::<f64>::from(Degrees::from(135.0))
        );
        let mut angle = Angle::<f64>::from(Degrees::from(15.0));
        angle *= 3.0;
        assert!(angle.approx_eq(&Angle::<f64>::from(Degrees::from(45.0))));
    }

    #[test]
    fn opposite() {
        assert!(Angle::<f64>::from(Degrees::from(45.0))
            .opposite()
            .approx_eq(&Angle::<f64>::from(Degrees::from(-135.0))));
        assert!(Angle::<f64>::from(Degrees::from(-60.0))
            .opposite()
            .approx_eq(&Angle::<f64>::from(Degrees::from(120.0))));
    }
}
