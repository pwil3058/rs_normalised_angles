// Copyright 2019 Peter Williams <pwil3058@gmail.com> <pwil3058@bigpond.net.au>
///! This crate provides floating point types that represent angles restricted to the confines
///! of a circle (i.e. their value is guaranteed to be in the range -PI to +PI).

#[macro_use]
extern crate serde_derive;

pub mod angle_f64;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
