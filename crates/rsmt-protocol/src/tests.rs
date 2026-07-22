//! R3/M2 tests: canonical field/shape/envelope decoding, shape validation,
//! transcript domain separation, and malformed/allocation-limit rejection.

use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

use crate::codec::{BABYBEAR_ORDER, DecodeError, Reader, decode_base, encode_base};
use crate::envelope::{MAX_STARK_BYTES, ProofEnvelope, RoundPublicInputs, statement_bytes};
use crate::protocol::{MAX_LOG_HEIGHT, ProtocolId};
use crate::shape::RoundShape;

fn digest(seed: u32) -> [BabyBear; 8] {
    core::array::from_fn(|i| BabyBear::from_u32(seed.wrapping_add(i as u32)))
}

/// A valid genesis-of-2-leaves shape: L=2, one junction, no openings/opaques.
fn good_shape() -> RoundShape {
    RoundShape {
        n_ops: 3, // 2×L + 1×N
        n_leaf: 2,
        n_join: 1,
        n_open: 0,
        n_b11: 0,
        n_p2ff: 5,   // 2·2 + 1 + 0
        n_p2term: 3, // 2 + 1 + 0 + 0
    }
}

fn good_publics() -> RoundPublicInputs {
    RoundPublicInputs {
        old_root_is_none: true,
        old_root: digest(0),
        new_root: digest(100),
    }
}

// -- field codec ------------------------------------------------------------

#[test]
fn base_field_roundtrip_and_canonicality() {
    for v in [0u32, 1, 42, BABYBEAR_ORDER - 1] {
        let f = BabyBear::from_u32(v);
        assert_eq!(decode_base(&encode_base(f)).unwrap(), f);
    }
    // p and above are non-canonical.
    for bad in [BABYBEAR_ORDER, BABYBEAR_ORDER + 1, u32::MAX] {
        assert_eq!(
            decode_base(&bad.to_le_bytes()),
            Err(DecodeError::NonCanonicalFieldElement)
        );
    }
}

#[test]
fn reader_rejects_eof_and_bad_bool() {
    let mut r = Reader::new(&[]);
    assert_eq!(r.read_u64(), Err(DecodeError::UnexpectedEof));
    assert_eq!(
        Reader::new(&[2]).read_bool(),
        Err(DecodeError::NonCanonicalBool)
    );
    assert_eq!(Reader::new(&[0]).read_bool(), Ok(false));
    assert_eq!(Reader::new(&[1]).read_bool(), Ok(true));
}

// -- protocol id ------------------------------------------------------------

#[test]
fn protocol_tag_roundtrip_and_rejects_unknown() {
    assert_eq!(
        ProtocolId::from_tag(&ProtocolId::R3Poseidon2.tag()),
        Some(ProtocolId::R3Poseidon2)
    );
    assert_eq!(ProtocolId::from_tag(b"BENCHxxx"), None);
    assert_eq!(ProtocolId::from_tag(b"R3P2v000"), None); // wrong version
}

// -- shape validation -------------------------------------------------------

#[test]
fn good_shape_validates_and_derives_heights() {
    let h = good_shape().validate().expect("valid");
    assert_eq!(h.a, 4); // pad(3)
    assert_eq!(h.l, 2); // pad(2)
    assert_eq!(h.j, 1);
    assert_eq!(h.r, 2048);
    assert_eq!(h.p, 32);
    // n_perm = 8 lanes / 8 = 1 → pad 1
    assert_eq!(h.b, 1);
}

#[test]
fn shape_rejects_broken_identities() {
    let base = good_shape();
    let mutants = [
        RoundShape { n_p2ff: 4, ..base }, // wrong feed-forward count
        RoundShape {
            n_p2term: 4,
            ..base
        }, // wrong terminal count
        RoundShape { n_b11: 2, ..base },  // n_b11 > n_join
        RoundShape { n_ops: 2, ..base },  // n_leaf+n_join+n_open > n_ops
        RoundShape {
            n_ops: 0,
            n_leaf: 0,
            n_join: 0,
            n_open: 0,
            n_b11: 0,
            n_p2ff: 0,
            n_p2term: 0,
        }, // empty round is not a RoundShape
    ];
    for m in mutants {
        assert_eq!(m.validate(), Err(DecodeError::InvalidShape), "{m:?}");
    }
}

#[test]
fn shape_rejects_over_max_height() {
    // n_leaf just over 2^MAX_LOG_HEIGHT forces L height over the cap.
    let n_leaf = (1usize << MAX_LOG_HEIGHT) + 1;
    let s = RoundShape {
        n_ops: n_leaf + 1,
        n_leaf,
        n_join: 1,
        n_open: 0,
        n_b11: 0,
        n_p2ff: 2 * n_leaf + 1,
        n_p2term: n_leaf + 1,
    };
    assert_eq!(s.validate(), Err(DecodeError::InvalidShape));
}

#[test]
fn shape_rejects_bus_multiplicity_wrap() {
    // n_leaf beyond p/52 wraps the range bus. (It also exceeds the height cap;
    // both surface as InvalidShape — this asserts the wrap gate exists.)
    let n_leaf = (BABYBEAR_ORDER as usize / 52) + 1;
    let s = RoundShape {
        n_ops: n_leaf + 1,
        n_leaf,
        n_join: 0,
        n_open: 0,
        n_b11: 0,
        n_p2ff: 2 * n_leaf,
        n_p2term: n_leaf,
    };
    assert_eq!(s.validate(), Err(DecodeError::InvalidShape));
}

#[test]
fn describe_rejection_none_when_valid() {
    assert_eq!(good_shape().describe_rejection(), None);
}

#[test]
fn describe_rejection_height_tells_soundness_story() {
    // n_ops just over 2^MAX_LOG_HEIGHT forces Table A's padded height over the cap.
    let n_ops = (1usize << MAX_LOG_HEIGHT) + 1;
    let s = RoundShape {
        n_ops,
        n_leaf: 1,
        n_join: 1,
        n_open: 0,
        n_b11: 0,
        n_p2ff: 3,
        n_p2term: 2,
    };
    let msg = s.describe_rejection().expect("rejected");
    // Names the binding table, the derived padded height, and the frozen cap.
    assert!(msg.contains("Table A"), "{msg}");
    assert!(msg.contains("131072") && msg.contains("2^17"), "{msg}");
    assert!(msg.contains("65536") && msg.contains("2^16"), "{msg}");
    // Carries the soundness rationale, not just a bare limit.
    assert!(msg.contains("soundness"), "{msg}");
    assert!(msg.contains("LogUp"), "{msg}");
    // The wire-level surface is still the opaque variant.
    assert_eq!(s.validate(), Err(DecodeError::InvalidShape));
}

#[test]
fn describe_rejection_reports_specific_identity() {
    // A broken feed-forward count names the p2ff bus, not a generic failure.
    let s = RoundShape {
        n_p2ff: 4,
        ..good_shape()
    };
    let msg = s.describe_rejection().expect("rejected");
    assert!(msg.contains("p2ff"), "{msg}");
}

// -- transcript domain separation -------------------------------------------

#[test]
fn statement_bytes_are_domain_separated() {
    let p = ProtocolId::R3Poseidon2;
    let pubs = good_publics();
    let shape = good_shape();
    let base = statement_bytes(p, &pubs, &shape);

    // Identical inputs → identical bytes.
    assert_eq!(base, statement_bytes(p, &pubs, &shape));

    // Flip the none flag.
    let p2 = RoundPublicInputs {
        old_root_is_none: !pubs.old_root_is_none,
        ..pubs
    };
    assert_ne!(base, statement_bytes(p, &p2, &shape));

    // Change old root.
    let p3 = RoundPublicInputs {
        old_root: digest(1),
        ..pubs
    };
    assert_ne!(base, statement_bytes(p, &p3, &shape));

    // Change new root.
    let p4 = RoundPublicInputs {
        new_root: digest(101),
        ..pubs
    };
    assert_ne!(base, statement_bytes(p, &p4, &shape));

    // Change any shape count.
    let s2 = RoundShape { n_b11: 1, ..shape };
    assert_ne!(base, statement_bytes(p, &pubs, &s2));
}

// -- envelope round trip + malformed rejection ------------------------------

#[test]
fn envelope_roundtrip() {
    let stark = vec![0xEFu8; 1000];
    let bytes = ProofEnvelope::encode(
        ProtocolId::R3Poseidon2,
        &good_publics(),
        &good_shape(),
        &stark,
    );
    let env = ProofEnvelope::decode(&bytes).expect("decode");
    assert_eq!(env.protocol, ProtocolId::R3Poseidon2);
    assert_eq!(env.publics, good_publics());
    assert_eq!(env.shape, good_shape());
    assert_eq!(env.stark, &stark[..]);
    // The statement preimage equals the front of the envelope.
    let stmt = statement_bytes(env.protocol, &env.publics, &env.shape);
    assert_eq!(&bytes[..stmt.len()], &stmt[..]);
}

#[test]
fn envelope_rejects_wrong_protocol() {
    let mut bytes = ProofEnvelope::encode(
        ProtocolId::R3Poseidon2,
        &good_publics(),
        &good_shape(),
        &[1, 2, 3],
    );
    bytes[0] = b'X'; // corrupt the tag
    assert_eq!(
        ProofEnvelope::decode(&bytes),
        Err(DecodeError::WrongProtocol)
    );
}

#[test]
fn envelope_rejects_trailing_bytes() {
    let mut bytes = ProofEnvelope::encode(
        ProtocolId::R3Poseidon2,
        &good_publics(),
        &good_shape(),
        &[1, 2, 3],
    );
    bytes.push(0x00); // one extra byte
    assert_eq!(
        ProofEnvelope::decode(&bytes),
        Err(DecodeError::TrailingBytes)
    );
}

#[test]
fn envelope_rejects_truncation() {
    let bytes = ProofEnvelope::encode(
        ProtocolId::R3Poseidon2,
        &good_publics(),
        &good_shape(),
        &[1, 2, 3, 4],
    );
    for cut in 0..bytes.len() {
        assert!(
            ProofEnvelope::decode(&bytes[..cut]).is_err(),
            "prefix of len {cut} must not decode"
        );
    }
}

#[test]
fn envelope_rejects_noncanonical_root() {
    let bytes = ProofEnvelope::encode(
        ProtocolId::R3Poseidon2,
        &good_publics(),
        &good_shape(),
        &[9, 9],
    );
    // The old_root's first base limb sits at offset 8 (tag) + 1 (bool) = 9.
    let mut bad = bytes.clone();
    bad[9..13].copy_from_slice(&BABYBEAR_ORDER.to_le_bytes());
    assert_eq!(
        ProofEnvelope::decode(&bad),
        Err(DecodeError::NonCanonicalFieldElement)
    );
}

#[test]
fn envelope_rejects_oversized_blob_before_alloc() {
    // Declared STARK length exceeds the cap but the payload is absent — the
    // decoder rejects on the length prefix (LengthLimitExceeded), never
    // attempting to read/allocate the huge size.
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&ProtocolId::R3Poseidon2.tag());
    bytes.push(1); // old_root_is_none
    bytes.extend_from_slice(&[0u8; 32]); // old_root
    bytes.extend_from_slice(&[0u8; 32]); // new_root
    good_shape().encode(&mut bytes);
    bytes.extend_from_slice(&(MAX_STARK_BYTES + 1).to_le_bytes()); // oversized len
    assert_eq!(
        ProofEnvelope::decode(&bytes),
        Err(DecodeError::LengthLimitExceeded)
    );
}
