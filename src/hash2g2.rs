use ark_bn254::{fq::Fq, fq2::Fq2, Fr, G1Projective, G2Affine, G2Projective};
// use ark_ec::short_weierstrass::Affine;
use ark_ff::{Field, LegendreSymbol};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
// use digest::generic_array::GenericArray;
// use num_integer::Integer;
// use digest::generic_array::{typenum::U48, typenum::U32};
pub use sha2::{digest::Digest, Sha256};
// use subtle::{Choice, ConditionallySelectable};
use crate::hash2g1;
use std::str::FromStr;
// use crate::hash2g1::ExpandMsgSHA256;
use crate::hash2g1::Hash2FieldBN254;
// use crate::hash2g1::FromOkm;
use ark_ec::{AffineRepr, CurveGroup, Group};

const GNARK_CONSTANTS: &str = r###"{
  "Z": {
    "X0": "1",
    "X1": "0"
  },
  "C1": {
    "X0": "19485874751759354771024239261021720505790618469301721065564631296452457478374",
    "X1": "266929791119991161246907387137283842545076965332900288569378510910307636690"
  },
  "C2": {
    "X0": "10944121435919637611123202872628637544348155578648911831344518947322613104291",
    "X1": "0"
  },
  "C3": {
    "X0": "18992192239972082890849143911285057164064277369389217330423471574879236301292",
    "X1": "21819008332247140148575583693947636719449476128975323941588917397607662637108"
  },
  "C4": {
    "X0": "10499238450719652342378357227399831140106360636427411350395554762472100376473",
    "X1": "6940174569119770192419592065569379906172001098655407502803841283667998553941"
  },
  "B": {
    "X0": "19485874751759354771024239261021720505790618469301721065564631296452457478373",
    "X1": "266929791119991161246907387137283842545076965332900288569378510910307636690"
  },
  "Endo": {
    "X" : {
        "X0": "21575463638280843010398324269430826099269044274347216827212613867836435027261",
        "X1": "10307601595873709700152284273816112264069230130616436755625194854815875713954"
    },
    "Y" : {
        "X0": "2821565182194536844548159561693502659359617185244120367078079554186484126554",
        "X1": "3505843767911556378687030309984248845540243509899259641013678093033130930403"
    }
  },
  "Seed": "4965661367192848881"
}"###;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct PointString {
    #[serde(rename = "X")]
    pub x: FieldString,
    #[serde(rename = "Y")]
    pub y: FieldString,
}

impl PointString {
    pub fn to_point(&self) -> G2Affine {
        let x = self.x.to_field();
        let y = self.y.to_field();
        G2Affine::new(x, y)
    }
    pub fn to_tuple(&self) -> (Fq2, Fq2) {
        let x = self.x.to_field();
        let y = self.y.to_field();
        (x, y)
    }
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FieldString {
    X0: String,
    X1: String,
}

impl FieldString {
    pub fn to_field(&self) -> Fq2 {
        Fq2 {
            c0: Fq::from_str(&self.X0).unwrap(),
            c1: Fq::from_str(&self.X1).unwrap(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Constants {
    pub Z: FieldString,
    pub C1: FieldString,
    pub C2: FieldString,
    pub C3: FieldString,
    pub C4: FieldString,
    pub B: FieldString,
    pub Endo: PointString,
    pub Seed: String,
}

impl Constants {
    fn seed(&self) -> BigUint {
        BigUint::from_str(&self.Seed).unwrap()
    }
}

#[allow(non_snake_case)]
pub fn MapToCurve2(c: Constants, U: Fq2) -> G2Affine {
    //constants
    //c1 = g(Z)
    //c2 = -Z / 2
    //c3 = sqrt(-g(Z) * (3 * Z² + 4 * A))     # sgn0(c3) MUST equal 0
    //c4 = -4 * g(Z) / (3 * Z² + 4 * A)

    let z = c.Z.to_field();

    let c1 = c.C1.to_field();

    let c2 = c.C2.to_field();

    let c3 = c.C3.to_field();

    let c4 = c.C4.to_field();
    let B = c.B.to_field();
    // tv1 = u²
    let mut tv1 = U.square();
    // tv1 = tv1 * c1
    tv1 = tv1 * c1;

    // tv2 = 1 + tv1
    let tv2 = Fq2::ONE + tv1;

    // tv1 = 1 - tv1
    tv1 = Fq2::ONE - tv1;
    // tv3 = tv1 * tv2
    let mut tv3 = tv1 * tv2;

    // tv3 = inv0(tv3);
    tv3 = tv3.inverse().unwrap();
    // tv4 = u * tv1
    let mut tv4 = U * tv1;
    // tv4 = tv4 * tv3
    tv4 = tv4 * tv3;
    // tv4 = tv4 * c3
    tv4 = tv4 * c3;
    // x1 = c2 - tv4
    let x1 = c2 - tv4;

    // gx1 = x1²
    let mut gx1 = x1.square();
    // gx1 = gx1 + A - pass since A = 0
    // gx1 * x1
    gx1 = gx1 * x1;
    // gx1 + B
    gx1 = gx1 + B;

    // gx1NotSquare = 0 if gx1 is square, -1 otherwise
    let gx1NotSquare = match gx1.legendre() {
        LegendreSymbol::QuadraticResidue => Fq2::ZERO,
        _ => {
            let mut o = Fq2::ONE;
            o.neg_in_place();
            o
        }
    };

    // x2 = c2 + tv4
    let x2 = c2 + tv4;
    // gx2 = x2^2
    let mut gx2 = x2.square();
    // gx2 = gx2 + A - but A = 0
    // gx2 = gx2 * x2
    gx2 = gx2 * x2;
    // gx2 = gx2 + B
    gx2 = gx2 + B;

    println!("gx2 {}", gx2.to_string());

    // gx2Square = 0 <=> gx2 square, -1 otherwise
    // ?? gx1SquareOrgGx2Not

    // x3 = tv2²
    let mut x3 = tv2.square();
    // x3 = x3 * tv3
    x3 = x3 * tv3;
    // x3 = x3²
    x3 = x3.square();
    // x3 = x3 * c4
    x3 = x3 * c4;
    // x3 = x3 + Z
    x3 = x3 + z;

    let mut x = if gx1.legendre().is_qr() { x1 } else { x3 };
    // x 0 x2 if gx2 is square and gx2 is not
    x = if gx2.legendre().is_qr() && !gx1.legendre().is_qr() {
        x2
    } else {
        x
    };

    // gx = x²
    let mut gx = x.square();
    // gx = gx * x
    gx = gx * x;
    // gx = gx + B
    gx = gx + B;

    // y = sqrt(gx)
    let mut y = gx.sqrt().unwrap();

    #[allow(non_snake_case)]
    let signsNotEqual = g2Sgn0(U) ^ g2Sgn0(y);
    // tv1 = tv1.neg()
    let mut yneg = y.clone();
    yneg.neg_in_place();

    y = match signsNotEqual {
        0 => y,
        _ => -y,
    };

    let res = G2Affine::new_unchecked(x, y);

    if !res.is_on_curve() {
        panic!("Point not on curve")
    }

    res
}

#[allow(non_snake_case)]
pub fn g2Sgn0(u: Fq2) -> u64 {
    let mut sign = 0u64;
    let mut zero = 1u64;

    let t: BigUint = u.c0.into();
    let mut sign_i = *BigUint::to_bytes_le(&t).get(0).unwrap() as u64 & 1;
    // let mut zero_i = hash2g1::g1NotZero(u.c0);
    let t: BigUint = u.c0.into();
    let zero_i = (*t.to_u64_digits().get(0).unwrap() == 0) as u64;
    sign = sign | (zero & sign_i);
    zero = zero & zero_i;

    let t: BigUint = u.c1.into();
    sign_i = *BigUint::to_bytes_le(&t).get(0).unwrap() as u64 & 1;

    sign = sign | (zero & sign_i);

    return sign;
}

#[allow(non_snake_case)]
pub fn g2NotZero(x: Fq2) -> u64 {
    //Assuming G1 is over Fp and that if hashing is available for G2, it also is for G1
    return hash2g1::g1NotZero(x.c0) | hash2g1::g1NotZero(x.c1);
}

#[allow(non_snake_case)]
pub fn HashToG2(msg: &[u8], dst: &[u8]) -> G2Affine {
    let c: Constants = serde_json::from_str(GNARK_CONSTANTS).unwrap();
    let u = Fq::hash_to_field(msg, dst, 4);
    println!(
        "U before Map : {:?}",
        u.iter().map(|i| i.to_string()).collect::<Vec<_>>()
    );

    let q0 = MapToCurve2(c.clone(), Fq2 { c0: u[0], c1: u[1] });

    // println!("{:?}", q0.x.c0 * Fq::from(Fq::R));

    let q1 = MapToCurve2(c.clone(), Fq2 { c0: u[2], c1: u[3] });

    let q: G2Affine = (q0 + q1).into();
    println!("Q before clearing out {}\n", q.to_string());
    // println!("{:?}", q.y.c0 * Fq::from(Fq::R));
    let _q = q.clear_cofactor();
    let _q3 = q.mul_by_cofactor();
    // let qr: G2Projective = _q.into();
    let q2 = (q0 + q1).into_affine().clear_cofactor();
    println!("Q AFTER clearing out {}", _q.to_string());
    println!("Q2 AFTER clearing out {}", q2.to_string());
    println!("Q3 AFTER clearing out {}", _q3.to_string());
    let q4 = clear_cofactor(&c, &q);
    println!("Q4 AFTER clearing out {}", q4.to_string());
    q4.into()
}

use ark_ff::PrimeField;
fn clear_cofactor(c: &Constants, a: &G2Affine) -> G2Affine {
    // Gen.SetString("4965661367192848881", 10)
    let seed = c.seed();
    let seed_fr = Fr::from(seed);
    println!("seed fr = {}", seed_fr);
    // points[0].ScalarMultiplication(a, &xGen)
    let p0 = a.mul_bigint(&seed_fr.into_bigint().as_ref().to_vec());
    println!("p0 = {}", p0.to_string());
    // points[1].Double(&points[0]).AddAssign(&points[0]).psi(&points[1])
    let p1 = psi(&c, &(p0.double() + p0));
    println!("p1 = {}", p1.to_string());
    // points[2].psi(&points[0]).psi(&points[2])
    let p2 = psi(&c, &psi(&c, &p0));
    println!("p2 = {}", p2.to_string());

    // points[3].psi(a).psi(&points[3]).psi(&points[3])
    let p3 = psi(&c, &psi(&c, &psi(&c, &a.into_group())));
    println!("p3 = {}", p3.to_string());
    let p = G2Affine::identity().into_group() + p0 + p1 + p2 + p3;
    println!("final p = {}", p.to_string());
    p.into_affine()
}

fn psi(c: &Constants, p: &G2Projective) -> G2Projective {
    let (u, v) = c.Endo.to_tuple();
    let mut p = p.clone();
    p.x.conjugate_in_place();
    p.x = p.x * u;
    p.y.conjugate_in_place();
    p.y = p.y * v;
    p.z.conjugate_in_place();
    p
}

#[cfg(test)]
mod tests {

    use crate::hash2g2::FieldString;
    use crate::hash2g2::Fq;
    use crate::hash2g2::HashToG2;
    use crate::hash2g2::MapToCurve2;
    use ark_bn254::Fq2;
    use ark_bn254::G2Affine;
    use serde::Deserialize;
    use serde::Serialize;
    use std::str::FromStr;
    // use ark_ff::Field;
    use crate::hash2g2::PointString;

    #[test]
    #[allow(non_snake_case)]
    fn test_hash_to_curve_g2_gnark_compatible() {
        #[derive(Serialize, Deserialize)]
        struct TestCase {
            #[serde(rename = "Dst")]
            pub dst: String,
            #[serde(rename = "Msg")]
            pub msg: String,
            #[serde(rename = "Output")]
            pub output: PointString,
        }
        const GNARK_TESTCASE: &str = r###"{
              "Dst": "6d792d6473742d69732d617765736f6d65",
              "Msg": "6d792d6d73672d69732d617765736f6d65",
              "Output": {
                "X": {
                  "X0": "13420984239446854365237369501661400800877883824300185456264815606136605104049",
                  "X1": "9098110816480530776598953815928287228176875826371177380413528896851914614329"
                },
                "Y": {
                  "X0": "5090289085945947546283621135556459578516270650752305390009333015498453414897",
                  "X1": "20437926047425299413969483442593892404146288914063877559396153874250292958281"
                }
              }
            }"###;
        let test_case: TestCase = serde_json::from_str(GNARK_TESTCASE).unwrap();
        let dst = hex::decode(&test_case.dst).unwrap();
        let msg = hex::decode(&test_case.msg).unwrap();
        let expected_point = test_case.output.to_point();
        let computed_point = HashToG2(&msg, &dst);
        assert_eq!(expected_point, computed_point);
    }
}
