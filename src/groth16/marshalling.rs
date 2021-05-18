use crate::bls::{Engine, PairingCurveAffine};
use ff::{Field, PrimeField};
use groupy::{CurveAffine, CurveProjective};
use rayon::prelude::*;

use super::{multiscalar, PreparedVerifyingKey, Proof, VerifyingKey, GROTH16VerificationKey};
use crate::multicore::VERIFIER_POOL as POOL;
use crate::SynthesisError;

pub fn fr_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::Fr, SynthesisError>{

    let mut repr = E:FqRepr::default();
    repr.read_be(Cursor::new([0; 16]).chain(Cursor::new(&okm[..32])))
    let fq_element = E::Fr::from_repr(repr).unwrap();

    Ok(fq_element)
}

pub fn fp_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::Fq, SynthesisError>{

    let mut repr = E:FqRepr::default();
    repr.read_be(Cursor::new([0; 16]).chain(Cursor::new(&okm[..32])))
    let fq_element = E::Fq::from_repr(repr).unwrap();

    Ok(fq_element)
}

pub fn fp2_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::Fq2, SynthesisError>{

    let fp_size = ?;

    let mut c0 = fp_process(proof_bytes[..fp_size]);
    let mut c1 = fp_process(proof_bytes[fp_size..]);
    
    let fq2_element = E:Fq2 {c0: c0, c1: c1};

    Ok(fq2_element)
}

pub fn fp6_3over2_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::Fq6, SynthesisError>{

    let fp2_size = ?;

    let mut c0 = fp2_process(proof_bytes[..fp2_size]);
    let mut c1 = fp2_process(proof_bytes[fp2_size..2*fp2_size]);
    let mut c2 = fp2_process(proof_bytes[2*fp2_size..]);
    
    let fq6_3over2_element = E:Fq6 {c0: c0, c1: c1, c2: c2};

    Ok(fq6_3over2_element)
}

pub fn fp12_2over3over2_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::Fq12, SynthesisError>{

    let fp6_3over2_size = ?;

    let mut c0 = fp6_3over2_process(proof_bytes[..fp6_3over2_size]);
    let mut c1 = fp6_3over2_process(proof_bytes[fp6_3over2_size..]);
    
    let fq12_2over3over2_element = E:Fq12 {c0: c0, c1: c1};

    Ok(fq12_2over3over2_element)
}

pub fn g1_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::G1, SynthesisError>{

    let fp_size = ?;

    let mut x_processed = fp_process(proof_bytes[..fp_size]);
    let mut y_processed = fp_process(proof_bytes[fp_size..2*fp_size]);
    let mut z_processed = fp_process(proof_bytes[2*fp_size..]);
    
    let g1_element = E:G1 {x: x_processed, y: y_processed, z: z_processed};

    Ok(g1_element)
}

pub fn g1_affine_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::G1Affine, SynthesisError>{

    let g1_affine_element = g1_process(proof_bytes).into_affine();
    Ok(g1_affine_element)
}

pub fn g2_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::G2, SynthesisError>{

    let fp2_size = ?;

    let mut x_processed = fp2_process(proof_bytes[..fp2_size]);
    let mut y_processed = fp2_process(proof_bytes[fp2_size..2*fp2_size]);
    let mut z_processed = fp2_process(proof_bytes[2*fp2_size..]);
    
    let g2_element = E:G2 {x: x_processed, y: y_processed, z: z_processed};

    Ok(g2_element)
}

pub fn g2_affine_process<E: Engine>(proof_bytes: &[u8]) -> Result<E::G2Affine, SynthesisError>{

    let g2_affine_element = g2_process(proof_bytes).into_affine();
    Ok(g2_affine_element)
}

pub fn accumulation_vector_process<E: Engine>(proof_bytes: &[u8]) -> Result<Vec<E::G1Affine>, SynthesisError>{
    let g1_size = ?;
    let accumulation_vector_size = proof_bytes.len()/g1_size;
    let mut accumulation_vector = Vec::new();

    for i in 0..accumulation_vector_size {
        accumulation_vector.push(g1_affine_process(proof_bytes[i*g1_size..(i+1)*g1_size]));
    }

    Ok(accumulation_vector)
}

pub fn groth16_vk_from_byteblob<E: Engine>(proof_bytes: &[u8]) -> Result<GROTH16VerificationKey<E>, SynthesisError>{
    let fqk_size = ?;
    let g2_affine_size = ?;
    let g1_affine_size = ?;

    let mut alpha_g1_beta_g2_processed = fp12_2over3over2_process(proof_bytes[..fqk_size]);
    let mut gamma_g2_processed = g2_affine_process(proof_bytes[fqk_size..fqk_size+g2_affine_size]);
    let mut delta_g2_processed = g2_affine_process(proof_bytes[fqk_size+g2_affine_size..fqk_size+2*g2_affine_size]);
    let mut ic_processed = accumulation_vector_process(proof_bytes[fqk_size+2*g2_affine_size..]);

    let groth16_key = GROTH16VerificationKey<E>{
            alpha_g1_beta_g2: alpha_g1_beta_g2_processed,
            gamma_g2: gamma_g2_processed,
            delta_g2: delta_g2_processed,
            ic: ic_processed
        };

    Ok(groth16_key)
}

pub fn groth16_proof_from_byteblob<E: Engine>(proof_bytes: &[u8]) -> Result<Proof<E>, SynthesisError>{
    let g2_affine_size = ?;
    let g1_affine_size = ?;

    let mut proof_a_processed = g1_affine_process(proof_bytes[..g1_affine_size]);
    let mut proof_b_processed = g2_affine_process(proof_bytes[g1_affine_size..g1_affine_size+g2_affine_size]);
    let mut proof_c_processed = g1_affine_process(proof_bytes[g1_affine_size+g2_affine_size..]);

    let groth16_proof = Proof<E>{a: proof_a_processed,
                                 b: proof_b_processed,
                                 c: proof_c_processed};

    Ok(groth16_proof)
}

pub fn groth16_primary_input_from_byteblob<E: Engine>(proof_bytes: &[u8]) -> Result<Vec<E:Fr>, SynthesisError>{
    let fr_size = ?;
    let groth16_primary_input_size = proof_bytes.len()/fr_size;
    let mut groth16_primary_input = Vec::new();

    for i in 0..groth16_primary_input_size {
        groth16_primary_input.push(fr_process(proof_bytes[i*fr_size..(i+1)*fr_size]));
    }

    Ok(groth16_primary_input)
}