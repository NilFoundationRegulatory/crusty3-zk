use crate::bls::{Bls12, Engine, PairingCurveAffine};
use ff::{Field, PrimeField};
use groupy::{CurveAffine, CurveProjective, EncodedPoint};
use rayon::prelude::*;

use super::{multiscalar, PreparedVerifyingKey, Proof, VerifyingKey, GROTH16VerificationKey,
            GROTH16ExtendedVerificationKey, ElGamalVerifiablePublicKey,
            groth16_vk_from_byteblob, groth16_proof_from_byteblob, groth16_primary_input_from_byteblob, std_size_t_process,
            g1_array_from_byteblob, groth16_ext_vk_from_byteblob, elgamal_verifiable_public_key_from_byteblob};

use crate::multicore::VERIFIER_POOL as POOL;
use crate::SynthesisError;

/// Generate a prepared verifying key, required to verify a proofs.
pub fn prepare_verifying_key<E: Engine>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    //let mut neg_gamma = vk.gamma_g2;
    //neg_gamma.negate();
    //let mut neg_delta = vk.delta_g2;
    //neg_delta.negate();

    let multiscalar = multiscalar::precompute_fixed_window(&vk.ic, multiscalar::WINDOW_SIZE);

    PreparedVerifyingKey {
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2),
        //neg_gamma_g2: neg_gamma.prepare(),
        //neg_delta_g2: neg_delta.prepare(),
        //gamma_g2: vk.gamma_g2.prepare(),
        //delta_g2: vk.delta_g2.prepare(),
        gamma_g2: vk.gamma_g2,
        delta_g2: vk.delta_g2,
        ic: vk.ic.clone(),
        multiscalar,
    }
}

pub fn groth16vk_to_pvk<E: Engine>(vk: &GROTH16VerificationKey<E>) -> PreparedVerifyingKey<E> {
    //let mut neg_gamma = vk.gamma_g2;
    //neg_gamma.negate();
    //let mut neg_delta = vk.delta_g2;
    //neg_delta.negate();

    let multiscalar = multiscalar::precompute_fixed_window(&vk.ic, multiscalar::WINDOW_SIZE);

    PreparedVerifyingKey {
        alpha_g1_beta_g2: vk.alpha_g1_beta_g2,
        //neg_gamma_g2: neg_gamma.prepare(),
        //neg_delta_g2: neg_delta.prepare(),
        //gamma_g2: vk.gamma_g2.prepare(),
        //delta_g2: vk.delta_g2.prepare(),
        gamma_g2: vk.gamma_g2,
        delta_g2: vk.delta_g2,
        ic: vk.ic.clone(),
        multiscalar,
    }
}

pub fn verify_groth16_proof_from_byteblob<E: Engine>(byteblob: &[u8]) -> Result<bool, SynthesisError> {

    let std_size_byteblob_size = 8;
    let g1_byteblob_size = <<Bls12 as Engine>::G1Affine as CurveAffine>::Compressed::size();
    let g2_byteblob_size = <<Bls12 as Engine>::G2Affine as CurveAffine>::Compressed::size();
    let proof_byteblob_size = g1_byteblob_size + g2_byteblob_size + g1_byteblob_size;
    let fr_byteblob_size = 32;
    let fp_byteblob_size = 48;
    let gt_byteblob_size = 12 * fp_byteblob_size;

    if (byteblob.len() < proof_byteblob_size){
        return Ok(false)
    }

    let de_prf = groth16_proof_from_byteblob::<Bls12>(&byteblob[..proof_byteblob_size]);
    let mut de_prf = match de_prf {
        Ok(result) => result,
        Err(e) => return Ok(false),
    };

    if (byteblob.len() < proof_byteblob_size + std_size_byteblob_size){
        return Ok(false)
    }

    let mut primary_input_byteblob_size = match std_size_t_process(&byteblob[proof_byteblob_size..proof_byteblob_size+std_size_byteblob_size]) {
        Ok(result) => fr_byteblob_size * result,
        Err(e) => return Ok(false),
    };

    if (byteblob.len() < proof_byteblob_size + std_size_byteblob_size + primary_input_byteblob_size){
        return Ok(false)
    }

    let de_pi = groth16_primary_input_from_byteblob::<Bls12>(&byteblob[proof_byteblob_size + std_size_byteblob_size..proof_byteblob_size + std_size_byteblob_size + primary_input_byteblob_size]);
    let mut de_pi = match de_pi {
        Ok(result) => result,
        Err(e) => return Ok(false),
    };

    let de_vk = groth16_vk_from_byteblob(&byteblob[proof_byteblob_size + std_size_byteblob_size + primary_input_byteblob_size..]);
    let mut de_vk = match de_vk {
        Ok(result) => result,
        Err(e) => return Ok(false),
    };

    let verified = verify_groth16_proof::<Bls12>(&de_vk, &de_prf, &de_pi);
    
    match verified {
        Ok(result) => Ok(result),
        Err(e) => return Ok(false),
    }
}

/// Verify a single Proof.
pub fn verify_groth16_proof<'a, E: Engine>(
    groth16_vk: &'a GROTH16VerificationKey<E>,
    proof: &Proof<E>,
    primary_input: &[E::Fr],
) -> Result<bool, SynthesisError> {

    let pvk = groth16vk_to_pvk(groth16_vk);

    let result = verify_proof(&pvk, &proof, &primary_input)?;

    Ok(result)
}

/// Verify a single Proof.
pub fn verify_proof<'a, E: Engine>(
    pvk: &'a PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    primary_input: &[E::Fr],
) -> Result<bool, SynthesisError> {
    use multiscalar::MultiscalarPrecomp;

    let mut neg_gamma_g2 = pvk.gamma_g2;
    neg_gamma_g2.negate();
    let mut neg_gamma_g2 = neg_gamma_g2.prepare();

    let mut neg_delta_g2 = pvk.delta_g2;
    neg_delta_g2.negate();
    let mut neg_delta_g2 = neg_delta_g2.prepare();

    let mut gamma_g2 = pvk.gamma_g2.prepare();
    let mut delta_g2 = pvk.delta_g2.prepare();

    if (primary_input.len() + 1) != pvk.ic.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    // The original verification equation is:
    // A * B = alpha * beta + inputs * gamma + C * delta
    // ... however, we rearrange it so that it is:
    // A * B - inputs * gamma - C * delta = alpha * beta
    // or equivalently:
    // A * B + inputs * (-gamma) + C * (-delta) = alpha * beta
    // which allows us to do a single final exponentiation.

    // Miller Loop for alpha * beta
    let mut ml_a_b = E::Fqk::zero();
    // Miller Loop for C * (-delta)
    let mut ml_all = E::Fqk::zero();
    // Miller Loop for inputs * (-gamma)
    let mut ml_acc = E::Fqk::zero();

    POOL.install(|| {
        // Start the two independent miller loops
        rayon::scope(|s| {
            // - Thread 1: Calculate ML alpha * beta
            let ml_a_b = &mut ml_a_b;
            s.spawn(move |_| {
                *ml_a_b = E::miller_loop(&[(&proof.a.prepare(), &proof.b.prepare())]);
            });

            // - Thread 2: Calculate ML C * (-delta)
            let ml_all = &mut ml_all;
            s.spawn(move |_| *ml_all = E::miller_loop(&[(&proof.c.prepare(), &neg_delta_g2)]));

            // - Accumulate inputs (on the current thread)
            let subset = pvk.multiscalar.at_point(1);
            let primary_input_repr: Vec<_> =
                primary_input.iter().map(PrimeField::into_repr).collect();

            let mut acc = multiscalar::par_multiscalar::<&multiscalar::Getter<E>, E>(
                &multiscalar::ScalarList::Slice(&primary_input_repr),
                &subset,
                std::mem::size_of::<<E::Fr as PrimeField>::Repr>() * 8,
            );

            acc.add_assign_mixed(&pvk.ic[0]);

            // Calculate ML inputs * (-gamma)
            let acc_aff = acc.into_affine();
            ml_acc = E::miller_loop(&[(&acc_aff.prepare(), &neg_gamma_g2)]);
        });
    });
    // Wait for the threaded miller loops to finish

    // Combine the results.
    ml_all.mul_assign(&ml_a_b);
    ml_all.mul_assign(&ml_acc);

    // Calculate the final exponentiation
    let QAP = E::final_exponentiation(&ml_all).unwrap();

    Ok(QAP == pvk.alpha_g1_beta_g2)
}

pub fn verify_encrypted_input_groth16_proof_from_byteblob<E: Engine>(byteblob: &[u8]) -> Result<bool, SynthesisError> {
    // TODO:
    //  use std::mem;
    //  mem::size_of::<usize>()
    let std_size_byteblob_size = 8;
    let g1_byteblob_size = <<Bls12 as Engine>::G1Affine as CurveAffine>::Compressed::size();
    let g2_byteblob_size = <<Bls12 as Engine>::G2Affine as CurveAffine>::Compressed::size();
    let proof_byteblob_size = g1_byteblob_size + g2_byteblob_size + g1_byteblob_size;
    let fr_byteblob_size = 32;
    let fp_byteblob_size = 48;
    let gt_byteblob_size = 12 * fp_byteblob_size;

    if (byteblob.len() < proof_byteblob_size){
        return Ok(false)
    }

    let de_prf = groth16_proof_from_byteblob::<Bls12>(&byteblob[..proof_byteblob_size]);
    let mut de_prf = match de_prf {
        Ok(result) => result,
        Err(e) => return Ok(false),
    };

    let vk_begin = proof_byteblob_size;
    let de_vk = groth16_ext_vk_from_byteblob(&byteblob[vk_begin..]);
    let mut de_vk = match de_vk {
        Ok(result) => result,
        Err(e) => return Ok(false),
    };

    let pubkey_begin = vk_begin + de_vk.1;
    let de_pubkey = elgamal_verifiable_public_key_from_byteblob(&byteblob[pubkey_begin..]);
    let mut de_pubkey = match de_pubkey {
        Ok(result) => result,
        Err(e) => return Ok(false),
    };

    let ct_begin = pubkey_begin + de_pubkey.1;
    let de_ct = g1_array_from_byteblob(&byteblob[ct_begin..]);
    let mut de_ct = match de_ct {
        Ok(result) => result,
        Err(e) => return Ok(false),
    };

    let pinput_begin = ct_begin + de_ct.1;
    let mut primary_input_byteblob_size = match std_size_t_process(&byteblob[pinput_begin..pinput_begin + std_size_byteblob_size]) {
        Ok(result) => fr_byteblob_size * result,
        Err(e) => return Ok(false),
    };
    let de_pi = groth16_primary_input_from_byteblob::<Bls12>(&byteblob[pinput_begin + std_size_byteblob_size..pinput_begin + std_size_byteblob_size + primary_input_byteblob_size]);
    let mut de_pi = match de_pi {
        Ok(result) => result,
        Err(e) => return Ok(false),
    };

    let verified = verify_encrypted_input_proof::<Bls12>(&de_prf, &de_vk.0, &de_pubkey.0, &de_ct.0, &de_pi);

    match verified {
        Ok(result) => Ok(result),
        Err(e) => return Ok(false),
    }
}

pub fn verify_encrypted_input_proof<'a, E: Engine>(
    proof: &Proof<E>,
    ext_vk: &'a GROTH16ExtendedVerificationKey<E>,
    pubkey: &'a ElGamalVerifiablePublicKey<E>,
    ct: &[E::G1Affine],
    unencrypted_primary_input: &[E::Fr],
) -> Result<bool, SynthesisError> {
    let input_size = ext_vk.ic.len() - 1;

    if !(input_size > ct.len() - 2) {
        return Err(SynthesisError::MalformedVerifyingKey);
    };
    if !(unencrypted_primary_input.len() + ct.len() - 2 == input_size) {
        return Err(SynthesisError::MalformedVerifyingKey);
    };
    if !(ct.len() - 2 == pubkey.delta_s_g1.len()) {
        // TODO: add new error code
        return Err(SynthesisError::MalformedVerifyingKey);
    };
    if !(ct.len() - 2 == pubkey.t_g1.len()) {
        // TODO: add new error code
        return Err(SynthesisError::MalformedVerifyingKey);
    };
    if !(ct.len() - 2 == pubkey.t_g2.len() - 1) {
        // TODO: add new error code
        return Err(SynthesisError::MalformedVerifyingKey);
    };

    let mut acc = ext_vk.ic[0].into_projective();
    let mut sum_cipher = E::Fqk::one();

    for i in 0..ct.len()-1 {
        acc.add_assign_mixed(&ct[i]);
        sum_cipher.mul_assign(&E::pairing(ct[i], pubkey.t_g2[i]));
    }

    for i in ct.len()-2..input_size {
        let mut G_i = ext_vk.ic[i + 1].into_projective();
        G_i.mul_assign(unencrypted_primary_input[i + 2 - ct.len()]);
        acc.add_assign(&G_i);
    }
    let presum_cipher = E::pairing(ct[ct.len()-1], E::G2Affine::one());
    let ans1: bool = (sum_cipher == presum_cipher);

    let QAPl = E::pairing(proof.a, proof.b);
    let mut QAPr = ext_vk.alpha_g1_beta_g2;
    QAPr.mul_assign(&E::pairing(acc, ext_vk.gamma_g2));
    QAPr.mul_assign(&E::pairing(proof.c, ext_vk.delta_g2));
    let ans2: bool = (QAPl == QAPr);

    Ok(ans1 && ans2)
}

/// Randomized batch verification - see Appendix B.2 in Zcash spec
pub fn verify_proofs_batch<'a, E: Engine, R: rand::RngCore>(
    pvk: &'a PreparedVerifyingKey<E>,
    rng: &mut R,
    proofs: &[&Proof<E>],
    primary_input: &[Vec<E::Fr>],
) -> Result<bool, SynthesisError>
where
    <<E as ff::ScalarEngine>::Fr as ff::PrimeField>::Repr: From<<E as ff::ScalarEngine>::Fr>,
{
    debug_assert_eq!(proofs.len(), primary_input.len());

    for primary_input_elem in primary_input {
        if (primary_input_elem.len() + 1) != pvk.ic.len() {
            return Err(SynthesisError::MalformedVerifyingKey);
        }
    }

    let num_inputs = primary_input[0].len();
    let num_proofs = proofs.len();

    if num_proofs < 2 {
        return verify_proof(pvk, proofs[0], &primary_input[0]);
    }

    let proof_num = proofs.len();

    // Choose random coefficients for combining the proofs.
    let mut rand_z_repr: Vec<_> = Vec::with_capacity(proof_num);
    let mut rand_z: Vec<_> = Vec::with_capacity(proof_num);
    let mut accum_y = E::Fr::zero();

    for _ in 0..proof_num {
        use rand::Rng;

        let t: u128 = rng.gen();
        let mut el = E::Fr::zero().into_repr();
        let el_ref: &mut [u64] = el.as_mut();
        assert!(el_ref.len() > 1);

        el_ref[0] = (t & (-1i64 as u128) >> 64) as u64;
        el_ref[1] = (t >> 64) as u64;

        let fr = E::Fr::from_repr(el).unwrap();

        // calculate sum
        accum_y.add_assign(&fr);
        // store FrRepr
        rand_z_repr.push(el);
        // store Fr
        rand_z.push(fr);
    }

    // MillerLoop(\sum Accum_Gamma)
    let mut ml_g = E::Fqk::zero();
    // MillerLoop(Accum_Delta)
    let mut ml_d = E::Fqk::zero();
    // MillerLoop(Accum_AB)
    let mut acc_ab = E::Fqk::zero();
    // Y^-Accum_Y
    let mut y = E::Fqk::zero();

    POOL.install(|| {
        let accum_y = &accum_y;
        let rand_z_repr = &rand_z_repr;

        rayon::scope(|s| {
            // - Thread 1: Calculate MillerLoop(\sum Accum_Gamma)
            let ml_g = &mut ml_g;
            s.spawn(move |_| {
                let scalar_getter = |idx: usize| -> <E::Fr as ff::PrimeField>::Repr {
                    if idx == 0 {
                        return accum_y.into_repr();
                    }
                    let idx = idx - 1;

                    // \sum(z_j * aj,i)
                    let mut cur_sum = rand_z[0];
                    cur_sum.mul_assign(&primary_input[0][idx]);

                    for (pi_mont, mut rand_mont) in
                        primary_input.iter().zip(rand_z.iter().copied()).skip(1)
                    {
                        // z_j * a_j,i
                        let pi_mont = &pi_mont[idx];
                        rand_mont.mul_assign(pi_mont);
                        cur_sum.add_assign(&rand_mont);
                    }

                    cur_sum.into_repr()
                };

                // \sum Accum_Gamma
                let acc_g_psi = multiscalar::par_multiscalar::<_, E>(
                    &multiscalar::ScalarList::Getter(scalar_getter, num_inputs + 1),
                    &pvk.multiscalar,
                    256,
                );

                let mut gamma_g2 = pvk.gamma_g2.prepare();
                // MillerLoop(acc_g_psi, vk.gamma)
                *ml_g = E::miller_loop(&[(&acc_g_psi.into_affine().prepare(), &gamma_g2)]);
            });

            // - Thread 2: Calculate MillerLoop(Accum_Delta)
            let ml_d = &mut ml_d;
            s.spawn(move |_| {
                let points: Vec<_> = proofs.iter().map(|p| p.c).collect();

                // Accum_Delta
                let acc_d: E::G1 = {
                    let pre = multiscalar::precompute_fixed_window::<E>(&points, 1);
                    multiscalar::multiscalar::<E>(
                        &rand_z_repr,
                        &pre,
                        std::mem::size_of::<<E::Fr as PrimeField>::Repr>() * 8,
                    )
                };

                let mut delta_g2 = pvk.delta_g2.prepare();
                *ml_d = E::miller_loop(&[(&acc_d.into_affine().prepare(), &delta_g2)]);
            });

            // - Thread 3: Calculate MillerLoop(Accum_AB)
            let acc_ab = &mut acc_ab;
            s.spawn(move |_| {
                let accum_ab_mls: Vec<_> = proofs
                    .par_iter()
                    .zip(rand_z_repr.par_iter())
                    .map(|(proof, rand)| {
                        // [z_j] pi_j,A
                        let mul_a = proof.a.mul(*rand);

                        // -pi_j,B
                        let mut cur_neg_b = proof.b.into_projective();
                        cur_neg_b.negate();

                        E::miller_loop(&[(
                            &mul_a.into_affine().prepare(),
                            &cur_neg_b.into_affine().prepare(),
                        )])
                    })
                    .collect();

                // Accum_AB = mul_j(ml((zj*proof_aj), -proof_bj))
                *acc_ab = accum_ab_mls[0];
                for accum in accum_ab_mls.iter().skip(1).take(num_proofs) {
                    acc_ab.mul_assign(accum);
                }
            });

            // Thread 4: Calculate Y^-Accum_Y
            let y = &mut y;
            s.spawn(move |_| {
                // -Accum_Y
                let mut accum_y_neg = *accum_y;
                accum_y_neg.negate();

                // Y^-Accum_Y
                *y = pvk.alpha_g1_beta_g2.pow(&accum_y_neg.into_repr());
            });
        });
    });

    let mut ml_all = acc_ab;
    ml_all.mul_assign(&ml_d);
    ml_all.mul_assign(&ml_g);

    Ok(E::final_exponentiation(&ml_all).unwrap() == y)
}
