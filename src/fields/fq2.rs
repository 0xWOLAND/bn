use crate::arith::{U256, U512};
use crate::fields::{const_fq, FieldElement, Fq};
use core::ops::{Add, Mul, Neg, Sub};
use rand::Rng;

cfg_if::cfg_if! {
    if #[cfg(target_os = "zkvm")] {
        use core::mem::transmute;
        use sp1_lib::io::{hint_slice, read_vec};
        use core::convert::TryInto;
    }
}

#[inline]
fn fq_non_residue() -> Fq {
    // (q - 1) is a quadratic nonresidue in Fq
    // 21888242871839275222246405745257275088696311157297823662689037894645226208582
    const_fq([
        0x3c208c16d87cfd46,
        0x97816a916871ca8d,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ])
}

#[inline]
pub fn fq2_nonresidue() -> Fq2 {
    Fq2::new(const_fq([9, 0, 0, 0]), const_fq([1, 0, 0, 0]))
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Fq2 {
    c0: Fq,
    c1: Fq,
}

impl Fq2 {
    pub fn new(c0: Fq, c1: Fq) -> Self {
        Fq2 { c0: c0, c1: c1 }
    }

    pub fn scale(&self, by: Fq) -> Self {
        Fq2 {
            c0: self.c0 * by,
            c1: self.c1 * by,
        }
    }

    pub fn mul_by_nonresidue(&self) -> Self {
        *self * fq2_nonresidue()
    }

    pub fn frobenius_map(&self, power: usize) -> Self {
        if power % 2 == 0 {
            *self
        } else {
            Fq2 {
                c0: self.c0,
                c1: self.c1 * fq_non_residue(),
            }
        }
    }

    pub fn real(&self) -> &Fq {
        &self.c0
    }

    pub fn imaginary(&self) -> &Fq {
        &self.c1
    }

    fn _add(self, other: Fq2) -> Fq2 {
        Fq2 {
            c0: self.c0._add(other.c0),
            c1: self.c1._add(other.c1),
        }
    }

    fn _mul(self, other: Fq2) -> Fq2 {
        // Devegili OhEig Scott Dahab
        //     Multiplication and Squaring on Pairing-Friendly Fields.pdf
        //     Section 3 (Karatsuba)

        let aa = self.c0._mul(other.c0);
        let bb = self.c1._mul(other.c1);

        Fq2 {
            c0: bb._mul(fq_non_residue())._add(aa),
            c1: (self.c0._add(self.c1))
                ._mul(other.c0._add(other.c1))
                ._sub(aa)
                ._sub(bb),
        }
    }

    fn _neg(self) -> Fq2 {
        Fq2 {
            c0: self.c0._neg(),
            c1: self.c1._neg(),
        }
    }
}

impl FieldElement for Fq2 {
    fn zero() -> Self {
        Fq2 {
            c0: Fq::zero(),
            c1: Fq::zero(),
        }
    }

    fn one() -> Self {
        Fq2 {
            c0: Fq::one(),
            c1: Fq::zero(),
        }
    }

    fn random<R: Rng>(rng: &mut R) -> Self {
        Fq2 {
            c0: Fq::random(rng),
            c1: Fq::random(rng),
        }
    }

    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    fn squared(&self) -> Self {
        // Devegili OhEig Scott Dahab
        //     Multiplication and Squaring on Pairing-Friendly Fields.pdf
        //     Section 3 (Complex squaring)

        *self * *self
    }

    fn inverse(self) -> Option<Self> {
        // "High-Speed Software Implementation of the Optimal Ate Pairing
        // over Barreto–Naehrig Curves"; Algorithm 8

        match (self
            .c0
            ._mul(self.c0)
            ._sub((self.c1._mul(self.c1))._mul(fq_non_residue())))
        .inverse()
        {
            Some(t) => Some(Fq2 {
                c0: self.c0._mul(t),
                c1: (self.c1._mul(t))._neg(),
            }),
            None => None,
        }
    }

    fn inverse_unconstrained(self) -> Option<Self> {
        #[cfg(target_os = "zkvm")]
        {
            // Compute the inverse using the zkvm syscall
            sp1_lib::unconstrained! {
                let mut buf = [0u8; 65];
                self.inverse().map(|inv| {
                    let bytes = unsafe { transmute::<[u128; 4], [u8; 64]>(inv.to_u512().0) };
                    buf[0..64].copy_from_slice(&bytes);
                    buf[64] = 1;
                });
                hint_slice(&buf);
            }
            let byte_vec = read_vec();
            let bytes: [u8; 65] = byte_vec.try_into().unwrap();
            match bytes[64] {
                0 => None,
                _ => {
                    let inv =
                        unsafe { transmute::<[u8; 64], Fq2>(bytes[0..64].try_into().unwrap()) };
                    Some(inv).filter(|inv| !self.is_zero() && self * *inv == Fq2::one())
                }
            }
        }
        #[cfg(not(target_os = "zkvm"))]
        {
            self.inverse()
        }
    }
}

impl Mul for Fq2 {
    type Output = Fq2;

    fn mul(self, other: Fq2) -> Fq2 {
        #[cfg(target_os = "zkvm")]
        {
            unsafe {
                let mut lhs = transmute::<Fq2, [u32; 16]>(self);
                let rhs = transmute::<&Fq2, &[u32; 16]>(&other);
                sp1_lib::syscall_bn254_fp2_mulmod(lhs.as_mut_ptr(), rhs.as_ptr());
                transmute::<[u32; 16], Fq2>(lhs)
            }
        }
        #[cfg(not(target_os = "zkvm"))]
        {
            // Devegili OhEig Scott Dahab
            //     Multiplication and Squaring on Pairing-Friendly Fields.pdf
            //     Section 3 (Karatsuba)

            let aa = self.c0 * other.c0;
            let bb = self.c1 * other.c1;

            Fq2 {
                c0: bb * fq_non_residue() + aa,
                c1: (self.c0 + self.c1) * (other.c0 + other.c1) - aa - bb,
            }
        }
    }
}

impl Sub for Fq2 {
    type Output = Fq2;

    fn sub(self, other: Fq2) -> Fq2 {
        Fq2 {
            c0: self.c0 - other.c0,
            c1: self.c1 - other.c1,
        }
    }
}

impl Add for Fq2 {
    type Output = Fq2;

    fn add(self, other: Fq2) -> Fq2 {
        Fq2 {
            c0: self.c0 + other.c0,
            c1: self.c1 + other.c1,
        }
    }
}

impl Neg for Fq2 {
    type Output = Fq2;

    fn neg(self) -> Fq2 {
        Fq2 {
            c0: -self.c0,
            c1: -self.c1,
        }
    }
}

lazy_static::lazy_static! {
    static ref FQ: U256 = U256::from([
        0x3c208c16d87cfd47,
        0x97816a916871ca8d,
        0xb85045b68181585d,
        0x30644e72e131a029
    ]);

    static ref FQ_MINUS3_DIV4: Fq =
        Fq::new(3.into()).expect("3 is a valid field element and static; qed").neg() *
        Fq::new(4.into()).expect("4 is a valid field element and static; qed").inverse()
        .expect("4 has inverse in Fq and is static; qed");

    static ref FQ_MINUS1_DIV2: Fq =
        Fq::new(1.into()).expect("1 is a valid field element and static; qed").neg() *
        Fq::new(2.into()).expect("2 is a valid field element and static; qed").inverse()
            .expect("2 has inverse in Fq and is static; qed");
}

impl Fq2 {
    pub fn i() -> Fq2 {
        Fq2::new(Fq::zero(), Fq::one())
    }

    fn _sqrt(&self) -> Option<Self> {
        let a1 = self.pow::<U256>((*FQ_MINUS3_DIV4).into());
        let a1a = a1._mul(*self);
        let alpha = a1._mul(a1a);
        let a0 = alpha.pow(*FQ)._mul(alpha);

        if a0 == Fq2::one()._neg() {
            return None;
        }

        if alpha == Fq2::one()._neg() {
            Some(Self::i()._mul(a1a))
        } else {
            let b = (alpha._add(Fq2::one())).pow::<U256>((*FQ_MINUS1_DIV2).into());
            Some(b._mul(a1a))
        }
    }

    pub fn sqrt(&self) -> Option<Self> {
        #[cfg(target_os = "zkvm")]
        {
            // Compute the square root using the zkvm syscall
            sp1_lib::unconstrained! {
                let mut buf = [0u8; 65];
                self._sqrt().map(|sqrt| {
                    let bytes = unsafe { transmute::<[u128; 4], [u8; 64]>(sqrt.to_u512().0) };
                    buf[0..64].copy_from_slice(&bytes);
                    buf[64] = 1;
                });
                hint_slice(&buf);
            }
            let byte_vec = read_vec();
            let bytes: [u8; 65] = byte_vec.try_into().unwrap();
            match bytes[64] {
                0 => None,
                _ => {
                    let sqrt =
                        unsafe { transmute::<[u8; 64], Fq2>(bytes[0..64].try_into().unwrap()) };
                    Some(sqrt).filter(|sqrt| *sqrt * *sqrt == *self)
                }
            }
        }
        #[cfg(not(target_os = "zkvm"))]
        {
            self._sqrt()
        }
    }

    pub fn to_u512(&self) -> U512 {
        let c0: U256 = (*self.real()).into();
        let c1: U256 = (*self.imaginary()).into();

        U512::new(&c1, &c0, &FQ)
    }
}

#[test]
fn sqrt_fq2() {
    // from zcash test_proof.cpp
    let x1 = Fq2::new(
        Fq::from_str(
            "12844195307879678418043983815760255909500142247603239203345049921980497041944",
        )
        .unwrap(),
        Fq::from_str(
            "7476417578426924565731404322659619974551724117137577781074613937423560117731",
        )
        .unwrap(),
    );

    let x2 = Fq2::new(
        Fq::from_str(
            "3345897230485723946872934576923485762803457692345760237495682347502347589474",
        )
        .unwrap(),
        Fq::from_str(
            "1234912378405347958234756902345768290345762348957605678245967234857634857676",
        )
        .unwrap(),
    );

    assert_eq!(x2.sqrt().unwrap(), x1);

    // i is sqrt(-1)
    assert_eq!(Fq2::one().neg().sqrt().unwrap(), Fq2::i(),);

    // no sqrt for (1 + 2i)
    assert!(
        Fq2::new(Fq::from_str("1").unwrap(), Fq::from_str("2").unwrap())
            .sqrt()
            .is_none()
    );
}
