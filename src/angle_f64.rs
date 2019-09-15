// Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>

pub use std::{convert::From, f64::consts::PI, ops::Sub};

fn normalise<A: Into<f64> + Copy>(arg: A) -> f64 {
    let mut result: f64 = arg.into();
    if !result.is_nan() {
        if result > PI {
            while result > PI {
                result -= 2.0 * PI;
            }
        } else if result < -PI {
            while result < -PI {
                result += 2.0 * PI;
            }
        }
    };
    result
}

#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
pub struct Angle64(f64);

impl From<f64> for Angle64 {
    fn from(f: f64) -> Self {
        Self(normalise(f))
    }
}

impl From<f32> for Angle64 {
    fn from(f: f32) -> Self {
        Self(normalise(f as f64))
    }
}

impl Sub for &Angle64 {
    type Output = Angle64;

    fn sub(self, other: Self) -> Self::Output {
        Angle64::from(self.0 - other.0)
    }
}

/// Takes into account the circular nature of angle values when
/// evaluating equality i.e. -PI and PI are the same angle.
impl PartialEq for Angle64 {
    fn eq(&self, other: &Self) -> bool {
        if self.0.is_nan() {
            other.0.is_nan()
        } else if other.0.is_nan() {
            false
        } else {
            (self - other).0 == 0.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Angle64;
    use std::f64::consts::PI;

    macro_rules! is_normalised {
        ( $x:expr ) => {{
            ($x <= std::f64::consts::PI) && ($x >= -std::f64::consts::PI)
        }};
    }

    #[test]
    fn from() {
        assert!(is_normalised!(Angle64::from(4.0_f64).0));
        assert_eq!(
            Angle64::from(4.0_f64).0,
            4.0_f64 - std::f64::consts::PI * 2.0
        );
        assert_eq!(
            Angle64::from(-4.0_f64).0,
            -4.0_f64 + std::f64::consts::PI * 2.0
        );
        assert!(is_normalised!(Angle64::from(4.0_f32).0));
        assert_eq!(
            Angle64::from(4.0_f32).0,
            4.0_f64 - std::f64::consts::PI * 2.0
        );
    }

    #[test]
    fn equality() {
        assert_eq!(Angle64::from(PI), Angle64::from(-PI));
        assert_ne!(Angle64::from(PI), Angle64::from(-PI + 0.0001));
    }
}
