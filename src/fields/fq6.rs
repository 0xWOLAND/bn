use crate::fields::{const_fq, FieldElement, Fq, Fq2};
use core::ops::{Add, Mul, Neg, Sub};
use rand::Rng;

fn frobenius_coeffs_c1(n: usize) -> Fq2 {
    match n % 6 {
        0 => Fq2::one(),
        1 => Fq2::new(
            const_fq([
                0x99e39557176f553d,
                0xb78cc310c2c3330c,
                0x4c0bec3cf559b143,
                0x2fb347984f7911f7,
            ]),
            const_fq([
                0x1665d51c640fcba2,
                0x32ae2a1d0b7c9dce,
                0x4ba4cc8bd75a0794,
                0x16c9e55061ebae20,
            ]),
        ),
        2 => Fq2::new(
            const_fq([
                0xe4bd44e5607cfd48,
                0xc28f069fbb966e3d,
                0x5e6dd9e7e0acccb0,
                0x30644e72e131a029,
            ]),
            Fq::zero(),
        ),
        3 => Fq2::new(
            const_fq([
                0x7b746ee87bdcfb6d,
                0x805ffd3d5d6942d3,
                0xbaff1c77959f25ac,
                0x856e078b755ef0a,
            ]),
            const_fq([
                0x380cab2baaa586de,
                0xfdf31bf98ff2631,
                0xa9f30e6dec26094f,
                0x4f1de41b3d1766f,
            ]),
        ),
        _ => unimplemented!(),
    }
}
fn frobenius_coeffs_c2(n: usize) -> Fq2 {
    match n % 6 {
        0 => Fq2::one(),
        1 => Fq2::new(
            const_fq([
                0x848a1f55921ea762,
                0xd33365f7be94ec72,
                0x80f3c0b75a181e84,
                0x5b54f5e64eea801,
            ]),
            const_fq([
                0xc13b4711cd2b8126,
                0x3685d2ea1bdec763,
                0x9f3a80b03b0b1c92,
                0x2c145edbe7fd8aee,
            ]),
        ),
        2 => Fq2::new(
            const_fq([
                0x5763473177fffffe,
                0xd4f263f1acdb5c4f,
                0x59e26bcea0d48bac,
                0x0,
            ]),
            Fq::zero(),
        ),
        3 => Fq2::new(
            const_fq([
                0xe1a92bc3ccbf066,
                0xe633094575b06bcb,
                0x19bee0f7b5b2444e,
                0xbc58c6611c08dab,
            ]),
            const_fq([
                0x5fe3ed9d730c239f,
                0xa44a9e08737f96e5,
                0xfeb0f6ef0cd21d04,
                0x23d5e999e1910a12,
            ]),
        ),
        _ => unimplemented!(),
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Fq6 {
    pub c0: Fq2,
    pub c1: Fq2,
    pub c2: Fq2,
}

impl Fq6 {
    pub fn new(c0: Fq2, c1: Fq2, c2: Fq2) -> Self {
        Fq6 {
            c0: c0,
            c1: c1,
            c2: c2,
        }
    }

    pub fn mul_by_nonresidue(&self) -> Self {
        Fq6 {
            c0: self.c2.mul_by_nonresidue(),
            c1: self.c0,
            c2: self.c1,
        }
    }

    pub fn scale(&self, by: Fq2) -> Self {
        Fq6 {
            c0: self.c0 * by,
            c1: self.c1 * by,
            c2: self.c2 * by,
        }
    }

    pub fn frobenius_map(&self, power: usize) -> Self {
        Fq6 {
            c0: self.c0.frobenius_map(power),
            c1: self.c1.frobenius_map(power) * frobenius_coeffs_c1(power),
            c2: self.c2.frobenius_map(power) * frobenius_coeffs_c2(power),
        }
    }
}

impl FieldElement for Fq6 {
    fn zero() -> Self {
        Fq6 {
            c0: Fq2::zero(),
            c1: Fq2::zero(),
            c2: Fq2::zero(),
        }
    }

    fn one() -> Self {
        Fq6 {
            c0: Fq2::one(),
            c1: Fq2::zero(),
            c2: Fq2::zero(),
        }
    }

    fn random<R: Rng>(rng: &mut R) -> Self {
        Fq6 {
            c0: Fq2::random(rng),
            c1: Fq2::random(rng),
            c2: Fq2::random(rng),
        }
    }

    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }

    fn squared(&self) -> Self {
        let s0 = self.c0.squared();
        let ab = self.c0 * self.c1;
        let s1 = ab + ab;
        let s2 = (self.c0 - self.c1 + self.c2).squared();
        let bc = self.c1 * self.c2;
        let s3 = bc + bc;
        let s4 = self.c2.squared();

        Fq6 {
            c0: s0 + s3.mul_by_nonresidue(),
            c1: s1 + s4.mul_by_nonresidue(),
            c2: s1 + s2 + s3 - s0 - s4,
        }
    }

    fn inverse(self) -> Option<Self> {
        let c0 = self.c0.squared() - self.c1 * self.c2.mul_by_nonresidue();
        let c1 = self.c2.squared().mul_by_nonresidue() - self.c0 * self.c1;
        let c2 = self.c1.squared() - self.c0 * self.c2;
        match ((self.c2 * c1 + self.c1 * c2).mul_by_nonresidue() + self.c0 * c0).inverse() {
            Some(t) => Some(Fq6 {
                c0: t * c0,
                c1: t * c1,
                c2: t * c2,
            }),
            None => None,
        }
    }

    fn inverse_unconstrained(self) -> Option<Self> {
        self.inverse() // same as constrained
    }
}

impl Mul for Fq6 {
    type Output = Fq6;

    fn mul(self, other: Fq6) -> Fq6 {
        let a_a = self.c0 * other.c0;
        let b_b = self.c1 * other.c1;
        let c_c = self.c2 * other.c2;

        Fq6 {
            c0: ((self.c1 + self.c2) * (other.c1 + other.c2) - b_b - c_c).mul_by_nonresidue() + a_a,
            c1: (self.c0 + self.c1) * (other.c0 + other.c1) - a_a - b_b + c_c.mul_by_nonresidue(),
            c2: (self.c0 + self.c2) * (other.c0 + other.c2) - a_a + b_b - c_c,
        }
    }
}

impl Sub for Fq6 {
    type Output = Fq6;

    fn sub(self, other: Fq6) -> Fq6 {
        Fq6 {
            c0: self.c0 - other.c0,
            c1: self.c1 - other.c1,
            c2: self.c2 - other.c2,
        }
    }
}

impl Add for Fq6 {
    type Output = Fq6;

    fn add(self, other: Fq6) -> Fq6 {
        Fq6 {
            c0: self.c0 + other.c0,
            c1: self.c1 + other.c1,
            c2: self.c2 + other.c2,
        }
    }
}

impl Neg for Fq6 {
    type Output = Fq6;

    fn neg(self) -> Fq6 {
        Fq6 {
            c0: -self.c0,
            c1: -self.c1,
            c2: -self.c2,
        }
    }
}
