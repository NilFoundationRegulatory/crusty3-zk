use std::io::{self, Read, Write};
use crate::bls::{Engine, PairingCurveAffine, Bls12, Fr, Fq, Fq2, Fq6, Fq12, FqRepr, FrRepr};
use ff::{Field, PrimeField};
use groupy::{CurveAffine, CurveProjective, EncodedPoint};
use rayon::prelude::*;

use byteorder::{ByteOrder, BigEndian, LittleEndian};

use super::{multiscalar, PreparedVerifyingKey, Proof, VerifyingKey, GROTH16VerificationKey};
use crate::multicore::VERIFIER_POOL as POOL;
use crate::SynthesisError;

pub fn fr_process<E: Engine>(proof_bytes: &[u8]) -> Result<Fr, SynthesisError>{

    let fr_byteblob_size = 32;

    let fr_byteblob : Vec<u8> = proof_bytes[..fr_byteblob_size].to_vec();

    let mut dst = [0; 4];
    LittleEndian::read_u64_into(&fr_byteblob, &mut dst);

    let fr_element = Fr::from_repr(FrRepr(dst)).unwrap();

    Ok(fr_element)
}

pub fn fp_process<E: Engine>(proof_bytes: &[u8]) -> Result<Fq, SynthesisError>{

    let fp_byteblob_size = 48;

    let fp_byteblob : Vec<u8> = proof_bytes[..fp_byteblob_size].to_vec();

    let mut dst = [0; 6];
    LittleEndian::read_u64_into(&fp_byteblob, &mut dst);

    let fq_element = Fq::from_repr(FqRepr(dst)).unwrap();

    Ok(fq_element)
}

pub fn fp2_process<E: Engine>(proof_bytes: &[u8]) -> Result<Fq2, SynthesisError>{

    let fp_byteblob_size = 48;

    let mut c0 = fp_process::<E>(&proof_bytes[..fp_byteblob_size]).unwrap();
    let mut c1 = fp_process::<E>(&proof_bytes[fp_byteblob_size..]).unwrap();
    
    let fq2_element = Fq2 {c0: c0, c1: c1};

    Ok(fq2_element)
}

pub fn fp6_3over2_process<E: Engine>(proof_bytes: &[u8]) -> Result<Fq6, SynthesisError>{

    let fp_byteblob_size = 48;
    let fp2_byteblob_size = 2*fp_byteblob_size;

    let mut c0 = fp2_process::<E>(&proof_bytes[..fp2_byteblob_size]).unwrap();
    let mut c1 = fp2_process::<E>(&proof_bytes[fp2_byteblob_size..2*fp2_byteblob_size]).unwrap();
    let mut c2 = fp2_process::<E>(&proof_bytes[2*fp2_byteblob_size..]).unwrap();
    
    let fq6_3over2_element = Fq6 {c0: c0, c1: c1, c2: c2};

    Ok(fq6_3over2_element)
}

pub fn fp12_2over3over2_process<E: Engine>(proof_bytes: &[u8]) -> Result<Fq12, SynthesisError>{

    let fp_byteblob_size = 48;
    let fp6_3over2_bytblob_size = 3*2*fp_byteblob_size;

    let mut c0_processed = fp6_3over2_process::<E>(&proof_bytes[..fp6_3over2_bytblob_size]).unwrap();
    let mut c1_processed = fp6_3over2_process::<E>(&proof_bytes[fp6_3over2_bytblob_size..]).unwrap();
    
    let fq12_2over3over2_element = Fq12 {c0: c0_processed, c1: c1_processed};

    Ok(fq12_2over3over2_element)
}

pub fn g1_affine_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::G1Affine, SynthesisError>{

    let g1_byteblob_size = <E::G1Affine as CurveAffine>::Compressed::size();

    let mut g1_repr = <E::G1Affine as CurveAffine>::Compressed::empty();
        let start = 0;
        let end = start + g1_byteblob_size;
        g1_repr.as_mut().copy_from_slice(&proof_bytes[start..end]);

        // let mut g1_repr = g1_repr as <<<E as Engine>::G1Affine as groupy::CurveAffine>::Compressed as groupy::EncodedPoint>;

        let g1_affine_element = g1_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })?;

    Ok(g1_affine_element)
}

pub fn g2_affine_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::G2Affine, SynthesisError>{

    let g2_byteblob_size = <E::G2Affine as CurveAffine>::Compressed::size();

    let mut g2_repr = <E::G2Affine as CurveAffine>::Compressed::empty();
        let start = 0;
        let end = start + g2_byteblob_size;
        g2_repr.as_mut().copy_from_slice(&proof_bytes[start..end]);

        let g2_affine_element = g2_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })?;

    Ok(g2_affine_element)
}

pub fn accumulation_vector_process<E: Engine>(proof_bytes: &[u8]) -> Result<Vec<E::G1Affine>, SynthesisError>{
    let g1_byteblob_size = <E::G1Affine as CurveAffine>::Compressed::size();
    let accumulation_vector_size = proof_bytes.len()/g1_byteblob_size;
    let mut accumulation_vector = Vec::new();

    for i in 0..accumulation_vector_size {
        accumulation_vector.push(g1_affine_process::<E>(&proof_bytes[i*g1_byteblob_size..(i+1)*g1_byteblob_size]).unwrap());
    }

    Ok(accumulation_vector)
}

pub fn groth16_vk_from_byteblob(proof_bytes: &[u8]) -> Result<GROTH16VerificationKey::<Bls12>, SynthesisError>{
    let fp_byteblob_size = 48;
    let fqk_byteblob_size = 2*3*2*fp_byteblob_size;
    let g1_byteblob_size = <<Bls12 as Engine>::G1Affine as CurveAffine>::Compressed::size();
    let g2_byteblob_size = <<Bls12 as Engine>::G2Affine as CurveAffine>::Compressed::size();

    let mut alpha_g1_beta_g2_processed = fp12_2over3over2_process::<Bls12>(&proof_bytes[..fqk_byteblob_size]).unwrap();
    let mut gamma_g2_processed = g2_affine_process::<Bls12>(&proof_bytes[fqk_byteblob_size..fqk_byteblob_size+g2_byteblob_size]).unwrap();
    let mut delta_g2_processed = g2_affine_process::<Bls12>(&proof_bytes[fqk_byteblob_size+g2_byteblob_size..fqk_byteblob_size+2*g2_byteblob_size]).unwrap();
    let mut ic_processed = accumulation_vector_process::<Bls12>(&proof_bytes[fqk_byteblob_size+2*g2_byteblob_size..]).unwrap();

    let mut alpha_g1_beta_g2_processed = alpha_g1_beta_g2_processed as <paired::bls12_381::Bls12 as Engine>::Fqk;
    let mut gamma_g2_processed = gamma_g2_processed as <paired::bls12_381::Bls12 as Engine>::G2Affine;
    let mut delta_g2_processed = delta_g2_processed as <paired::bls12_381::Bls12 as Engine>::G2Affine;
    let mut ic_processed = ic_processed as Vec<<paired::bls12_381::Bls12 as Engine>::G1Affine>;

    let groth16_key = GROTH16VerificationKey::<Bls12>{
            alpha_g1_beta_g2: alpha_g1_beta_g2_processed,
            gamma_g2: gamma_g2_processed,
            delta_g2: delta_g2_processed,
            ic: ic_processed
        };

    Ok(groth16_key)
}

pub fn groth16_proof_from_byteblob<E: Engine>(proof_bytes: &[u8]) -> Result<Proof<E>, SynthesisError>{
    
    let g1_byteblob_size = <E::G1Affine as CurveAffine>::Compressed::size();
    let g2_byteblob_size = <E::G2Affine as CurveAffine>::Compressed::size();

    let proof_byteblob_size = g1_byteblob_size + g2_byteblob_size + g1_byteblob_size;

    let de_prf = Proof::<E>::read(&proof_bytes[..proof_byteblob_size]).unwrap();

    Ok(de_prf)
}

pub fn groth16_primary_input_from_byteblob<E: Engine>(proof_bytes: &[u8]) -> Result<Vec<Fr>, SynthesisError>{
    let fr_byteblob_size = 32;
    let groth16_primary_input_size = proof_bytes.len()/fr_byteblob_size;
    let mut groth16_primary_input = Vec::new();

    for i in 0..groth16_primary_input_size {
        groth16_primary_input.push(fr_process::<E>(&proof_bytes[i*fr_byteblob_size..(i+1)*fr_byteblob_size]).unwrap());
    }

    Ok(groth16_primary_input)
}