/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
import ProofLib.SepLogic.WPp
public meta import Lean
public meta import ProofLib.GenDecodes
public meta import ProofLib.ProgramReflection
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 2d Header & Jump-Table Dispatch (`+1740 .. +1896`, `0x6d6dc .. 0x6d778`)

Proves `Option` niche-cap / remainder splits for `V1State` variants, symbolic execution of the
`st.inner` / `v1.innerState` header checks (`+1740 .. +1880`), and the `.rodata` half-word
jump-table dispatch macro (`+1880 .. +1896`).
-/

public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Self-Contained `Option` Cap / Rest Splits for `V1State` Variants -/

theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  have h1 : cap < 0x8000000000000000#64 := (BitVec.lt_def).2 h
  clear h; bv_bits

theorem cap_add_two_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 != 0#64) = true := by
  rw [bne_iff_ne, ne_eq, ← beq_iff_eq, cap_add_two_beq_zero_false h]
  decide

theorem cap_xor_top_ult_11_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ((cap ^^^ 0x8000000000000000#64).ult 11#64) = false := by
  have hlt : cap < 0x8000000000000000#64 := (BitVec.lt_def).2 h
  clear h; bv_bits

theorem optCt1SentRest_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentRest A g p opt ∗ R) :
    (optCt1SentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optCt1SentCap, arm64_norm]
  | some u =>
    simp only [optCt1SentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.es ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

theorem optCt1SentRest_disc_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentRest A g p opt ∗ R) :
    (optCt1SentCap g opt + 2#64 == 0#64) = false ∧
      (optCt1SentCap g opt + 2#64 != 0#64) = true ∧
      ((optCt1SentCap g opt ^^^ 0x8000000000000000#64).ult 11#64) = false := by
  cases opt with
  | none => simp [optCt1SentCap, noneCap, arm64_norm]
  | some u =>
    simp only [optCt1SentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.es ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_two_beq_zero_false hcap, cap_add_two_bne_zero_true hcap,
      cap_xor_top_ult_11_false hcap⟩

@[expose] def optEkSentCap (g : Unchunked3PBGhost) : Option V1State.Unchunked.EkSent → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

@[expose] def optEkSentRest (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.EkSent → SepProp
  | none => memRegion (p + 8#64) 72
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
      ((p + 0x48#64) ↦₆₄ u.epoch)

theorem optEkSentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.EkSent) :
    optEkSentPBPinnedAt A g p opt =
      (p ↦₆₄ optEkSentCap g opt) ∗ optEkSentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt,
      optEkSentCap, optEkSentRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optEkSentRest_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentRest A g p opt ∗ R) :
    (optEkSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optEkSentCap, arm64_norm]
  | some u =>
    simp only [optEkSentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
         ((p + 0x48#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

@[expose] def optPolyEncCap (g : PolynomialEncoderPBGhost) : Option PolynomialEncoder → BitVec 64
  | none => noneCap
  | some _ => g.pts.cap

@[expose] def optPolyEncRest (A : RustAlloc) (g : PolynomialEncoderPBGhost) (p : BitVec 64) :
    Option PolynomialEncoder → SepProp
  | none => memRegion (p + 8#64) 48
  | some pb =>
    ((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
      vecVecU8PinnedAt A g.polys (p + 24#64) pb.polys ∗
      ((p + 48#64) ↦₃₂ pb.idx) ∗
      memRegion (p + 52#64) 4

theorem optPolynomialEncoderPBPinnedAt_eq (A : RustAlloc) (g : PolynomialEncoderPBGhost) (p : BitVec 64)
    (opt : Option PolynomialEncoder) :
    optPolynomialEncoderPBPinnedAt A g p opt =
      (p ↦₆₄ optPolyEncCap g opt) ∗ optPolyEncRest A g p opt := by
  cases opt with
  | none => rfl
  | some pb =>
    simp only [optPolynomialEncoderPBPinnedAt, polynomialEncoderPBPinnedAt,
      optPolyEncCap, optPolyEncRest, vecVecU8PinnedAt_eq_header_buf A g.pts p, sepConj_assoc]

theorem optPolyEncRest_cap_bounds {A : RustAlloc} {g : PolynomialEncoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialEncoder} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolyEncRest A g p opt ∗ R) :
    (optPolyEncCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyEncCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optPolyEncCap, arm64_norm]
  | some pb =>
    simp only [optPolyEncRest] at hm
    have hbuf : m ⊨ vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
        (((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         vecVecU8PinnedAt A g.polys (p + 24#64) pb.polys ∗
         ((p + 48#64) ↦₃₂ pb.idx) ∗ memRegion (p + 52#64) 4 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap24⟩ := vecVecU8Buf_bounds hbuf
    have hcap : g.pts.cap.toNat < 2 ^ 63 := by omega
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

@[expose] def optPolyDecCap (g : PolynomialDecoderPBGhost) : Option PolynomialDecoder → BitVec 64
  | none => noneCap
  | some _ => g.pts.cap

@[expose] def optPolyDecRest (A : RustAlloc) (g : PolynomialDecoderPBGhost) (p : BitVec 64) :
    Option PolynomialDecoder → SepProp
  | none => memRegion (p + 8#64) 32
  | some pb =>
    ((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
      ((p + 24#64) ↦₃₂ pb.ptsNeeded) ∗
      ((p + 28#64) ↦₃₂ pb.polys) ∗
      ((p + 32#64) ↦₈ boolByte pb.isComplete) ∗
      memRegion (p + 33#64) 7

theorem optPolynomialDecoderPBPinnedAt_eq (A : RustAlloc) (g : PolynomialDecoderPBGhost) (p : BitVec 64)
    (opt : Option PolynomialDecoder) :
    optPolynomialDecoderPBPinnedAt A g p opt =
      (p ↦₆₄ optPolyDecCap g opt) ∗ optPolyDecRest A g p opt := by
  cases opt with
  | none => rfl
  | some pb =>
    simp only [optPolynomialDecoderPBPinnedAt, polynomialDecoderPBPinnedAt,
      optPolyDecCap, optPolyDecRest, vecVecU8PinnedAt_eq_header_buf A g.pts p, sepConj_assoc]

theorem optPolyDecRest_cap_bounds {A : RustAlloc} {g : PolynomialDecoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialDecoder} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolyDecRest A g p opt ∗ R) :
    (optPolyDecCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyDecCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optPolyDecCap, arm64_norm]
  | some pb =>
    simp only [optPolyDecRest] at hm
    have hbuf : m ⊨ vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
        (((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         ((p + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((p + 28#64) ↦₃₂ pb.polys) ∗
         ((p + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (p + 33#64) 7 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap24⟩ := vecVecU8Buf_bounds hbuf
    have hcap : g.pts.cap.toNat < 2 ^ 63 := by omega
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

@[expose] def optUnchunked2Cap (g : Unchunked2PBGhost) : Option (Option AuthenticatorPB) → BitVec 64
  | none => noneCap2
  | some auth => optAuthCap g auth

@[expose] def optUnchunked2Rest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64) :
    Option (BitVec 64 × Option AuthenticatorPB) → SepProp
  | none => memRegion (p + 8#64) 48
  | some (epoch, auth) =>
    optAuthPayload A g p auth ∗ ((p + 48#64) ↦₆₄ epoch)

theorem optUnchunked2Rest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option (BitVec 64 × Option AuthenticatorPB)} {R : SepProp} {m : Memory}
    (hm : m ⊨ optUnchunked2Rest A g p opt ∗ R) :
    (optUnchunked2Cap g (opt.map Prod.snd) + 2#64 == 0#64) = !opt.isSome ∧
      (optUnchunked2Cap g (opt.map Prod.snd) + 2#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optUnchunked2Cap, noneCap2, arm64_norm]
  | some pair =>
    rcases pair with ⟨epoch, auth⟩
    cases auth with
    | none =>
      simp only [Option.map_some, Option.isSome_some, Bool.not_true, optUnchunked2Cap, optAuthCap]
      exact ⟨by decide, by decide⟩
    | some a =>
      simp only [optUnchunked2Rest, optAuthPayload] at hm
      have hbuf : m ⊨ vecU8Buf A g.rootKey.cap g.rootKey.ptr a.rootKey ∗
          (((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 a.rootKey.length) ∗
           ((p + 24#64) ↦₆₄ g.macKey.cap) ∗ ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗
           ((p + 40#64) ↦₆₄ BitVec.ofNat 64 a.macKey.length) ∗
           vecU8Buf A g.macKey.cap g.macKey.ptr a.macKey ∗
           ((p + 48#64) ↦₆₄ epoch) ∗ R) := by
        convert hm using 1; ac_rfl
      have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
      simp only [Option.map_some, Option.isSome_some, Bool.not_true, optUnchunked2Cap, optAuthCap]
      exact ⟨cap_add_two_beq_zero_false hcap, cap_add_two_bne_zero_true hcap⟩

@[expose] def optKeysUnsampledCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.KeysUnsampled) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

@[expose] def optKeysUnsampledRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optKeysUnsampledPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) :
    optKeysUnsampledPBPinnedAt A g p opt =
      (p ↦₆₄ optKeysUnsampledCap g opt) ∗ optKeysUnsampledRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optKeysUnsampledPBPinnedAt, keysUnsampledPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optKeysUnsampledCap, optKeysUnsampledRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optKeysUnsampledRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.KeysUnsampled} {R : SepProp} {m : Memory}
    (hm : m ⊨ optKeysUnsampledRest A g p opt ∗ R) :
    (optKeysUnsampledCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optKeysUnsampledCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optKeysUnsampledCap] using h

@[expose] def optNoHeaderReceivedCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.NoHeaderReceived) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

@[expose] def optNoHeaderReceivedRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optNoHeaderReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optNoHeaderReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optNoHeaderReceivedCap g opt) ∗ optNoHeaderReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optNoHeaderReceivedCap, optNoHeaderReceivedRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optNoHeaderReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.NoHeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optNoHeaderReceivedRest A g p opt ∗ R) :
    (optNoHeaderReceivedCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optNoHeaderReceivedCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optNoHeaderReceivedCap] using h

@[expose] def optCt2SentCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.Ct2Sent) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

@[expose] def optCt2SentRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optCt2SentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) :
    optCt2SentPBPinnedAt A g p opt =
      (p ↦₆₄ optCt2SentCap g opt) ∗ optCt2SentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optCt2SentPBPinnedAt, ct2SentPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optCt2SentCap, optCt2SentRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optCt2SentRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct2Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt2SentRest A g p opt ∗ R) :
    (optCt2SentCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optCt2SentCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optCt2SentCap] using h

@[expose] def optHeaderReceivedCap (g : Unchunked3PBGhost) : Option V1State.Unchunked.HeaderReceived → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

@[expose] def optHeaderReceivedRest (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.HeaderReceived → SepProp
  | none => memRegion (p + 8#64) 72
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
      ((p + 0x48#64) ↦₆₄ u.epoch)

theorem optHeaderReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderReceived) :
    optHeaderReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optHeaderReceivedCap g opt) ∗ optHeaderReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optHeaderReceivedPBPinnedAt, headerReceivedPBPinnedAt, unchunked3PinnedAt,
      optHeaderReceivedCap, optHeaderReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optHeaderReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderReceivedRest A g p opt ∗ R) :
    (optHeaderReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optHeaderReceivedCap, arm64_norm]
  | some u =>
    simp only [optHeaderReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
         ((p + 0x48#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

@[expose] def optHeaderSentCap (g : Unchunked4PBGhost) : Option V1State.Unchunked.HeaderSent → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

@[expose] def optHeaderSentRest (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.HeaderSent → SepProp
  | none => memRegion (p + 8#64) 96
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.ek.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.ek ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.dk ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
      ((p + 0x60#64) ↦₆₄ u.epoch)

theorem optHeaderSentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderSent) :
    optHeaderSentPBPinnedAt A g p opt =
      (p ↦₆₄ optHeaderSentCap g opt) ∗ optHeaderSentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optHeaderSentPBPinnedAt, headerSentPBPinnedAt, unchunked4PinnedAt,
      optHeaderSentCap, optHeaderSentRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optHeaderSentRest_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderSentRest A g p opt ∗ R) :
    (optHeaderSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optHeaderSentCap, arm64_norm]
  | some u =>
    simp only [optHeaderSentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.ek ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.ek.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.dk ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
         ((p + 0x60#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

@[expose] def optEkSentCt1ReceivedCap (g : Unchunked4PBGhost) : Option V1State.Unchunked.EkSentCt1Received → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

@[expose] def optEkSentCt1ReceivedRest (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.EkSentCt1Received → SepProp
  | none => memRegion (p + 8#64) 96
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ct1 ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
      ((p + 0x60#64) ↦₆₄ u.epoch)

theorem optEkSentCt1ReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optEkSentCt1ReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optEkSentCt1ReceivedCap g opt) ∗ optEkSentCt1ReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optEkSentCt1ReceivedPBPinnedAt, ekSentCt1ReceivedPBPinnedAt, unchunked4PinnedAt,
      optEkSentCt1ReceivedCap, optEkSentCt1ReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optEkSentCt1ReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSentCt1Received} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentCt1ReceivedRest A g p opt ∗ R) :
    (optEkSentCt1ReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCt1ReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optEkSentCt1ReceivedCap, arm64_norm]
  | some u =>
    simp only [optEkSentCt1ReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
         ((p + 0x60#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

@[expose] def optCt1SentEkReceivedCap (g : Unchunked5PBGhost) : Option V1State.Unchunked.Ct1SentEkReceived → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

@[expose] def optCt1SentEkReceivedRest (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.Ct1SentEkReceived → SepProp
  | none => memRegion (p + 8#64) 120
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.es.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.es ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ek ∗
      vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
      ((p + 0x78#64) ↦₆₄ u.epoch)

theorem optCt1SentEkReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optCt1SentEkReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optCt1SentEkReceivedCap g opt) ∗ optCt1SentEkReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optCt1SentEkReceivedPBPinnedAt, ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt,
      optCt1SentEkReceivedCap, optCt1SentEkReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optCt1SentEkReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1SentEkReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentEkReceivedRest A g p opt ∗ R) :
    (optCt1SentEkReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentEkReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optCt1SentEkReceivedCap, arm64_norm]
  | some u =>
    simp only [optCt1SentEkReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.es ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.es.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ek ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

theorem optKeysUnsampledPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.KeysUnsampled} {R : SepProp} {m : Memory}
    (hm : m ⊨ optKeysUnsampledPBPinnedAt A g p opt ∗ R) :
    (optKeysUnsampledCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optKeysUnsampledCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optKeysUnsampledPBPinnedAt_eq, sepConj_assoc] at hm
  exact optKeysUnsampledRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optNoHeaderReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.NoHeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optNoHeaderReceivedPBPinnedAt A g p opt ∗ R) :
    (optNoHeaderReceivedCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optNoHeaderReceivedCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optNoHeaderReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optNoHeaderReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt2SentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct2Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt2SentPBPinnedAt A g p opt ∗ R) :
    (optCt2SentCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optCt2SentCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optCt2SentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt2SentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optHeaderReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderReceivedPBPinnedAt A g p opt ∗ R) :
    (optHeaderReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optHeaderReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optHeaderReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optHeaderSentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderSentPBPinnedAt A g p opt ∗ R) :
    (optHeaderSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optHeaderSentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optHeaderSentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optEkSentCt1ReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSentCt1Received} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentCt1ReceivedPBPinnedAt A g p opt ∗ R) :
    (optEkSentCt1ReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCt1ReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optEkSentCt1ReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optEkSentCt1ReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt1SentEkReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1SentEkReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentEkReceivedPBPinnedAt A g p opt ∗ R) :
    (optCt1SentEkReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentEkReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optCt1SentEkReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt1SentEkReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt1SentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentPBPinnedAt A g p opt ∗ R) :
    (optCt1SentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optCt1SentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt1SentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optPolynomialEncoderPBPinnedAt_cap_bounds {A : RustAlloc} {g : PolynomialEncoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialEncoderPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolynomialEncoderPBPinnedAt A g p opt ∗ R) :
    (optPolyEncCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyEncCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optPolynomialEncoderPBPinnedAt_eq, sepConj_assoc] at hm
  exact optPolyEncRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optPolynomialDecoderPBPinnedAt_cap_bounds {A : RustAlloc} {g : PolynomialDecoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialDecoderPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolynomialDecoderPBPinnedAt A g p opt ∗ R) :
    (optPolyDecCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyDecCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optPolynomialDecoderPBPinnedAt_eq, sepConj_assoc] at hm
  exact optPolyDecRest_cap_bounds (Satisfies.of_sep_right hm)

theorem encodeInner_v1_eq (v1 : V1State) :
    PqRatchetState.Inner.encode (.v1 v1) =
      ([0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))) ++
        V1State.encodeRaw v1 := by
  dsimp only [PqRatchetState.Inner.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] from rfl,
    ← v1StatePBEncodedLen_eq_proto, V1State.encodedLen, List.append_assoc]

theorem v1StateInnerCap_add_two_bounds {A : RustAlloc} {g : V1StatePBGhost} {p : BitVec 64}
    {is : V1State.InnerState} {R : SepProp} {m : Memory}
    (hm : m ⊨ v1StateInnerPBPinnedAt A g p is ∗ R) :
    (v1StateInnerCap g is + 2#64 == 0#64) = false ∧
      (v1StateInnerCap g is + 2#64 != 0#64) = true := by
  cases is with
  | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _
  | ekSentCt1Received _ | noHeaderReceived _ | headerReceived _
  | ekReceivedCt1Sampled _ | ct1Acknowledged _ | ct2Sampled _ =>
    dsimp only [v1StateInnerCap]
    exact ⟨by decide, by decide⟩
  | ct1Sampled v =>
    cases huc : v.uc with
    | none =>
      dsimp only [v1StateInnerCap]
      rw [huc]
      dsimp only [optCt1SentCap]
      exact ⟨by decide, by decide⟩
    | some u =>
      rw [v1StateInnerPBPinnedAt_eq, sepConj_assoc] at hm
      have hrest := Satisfies.of_sep_right hm
      simp only [v1StateInnerRest, huc, optCt1SentRest] at hrest
      have hbuf : m ⊨ EncodedLen.vecU8Buf A g.b.gCt1Sampled.uc.f3.cap g.b.gCt1Sampled.uc.f3.ptr u.hdr ∗
          (((p + 8#64) ↦₆₄ g.b.gCt1Sampled.uc.f3.ptr) ∗
           ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
           vecU8At A (p + 0x18#64) g.b.gCt1Sampled.uc.f4.cap g.b.gCt1Sampled.uc.f4.ptr u.es ∗
           vecU8At A (p + 0x30#64) g.b.gCt1Sampled.uc.f5.cap g.b.gCt1Sampled.uc.f5.ptr u.ct1 ∗
           optAuthenticatorPBPinnedAt A g.b.gCt1Sampled.uc.auth (p + 0x48#64) u.auth ∗
           ((p + 0x78#64) ↦₆₄ u.epoch) ∗
           optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (p + 128#64) v.sendingCt1 ∗
           optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (p + 184#64) v.receivingEk ∗ R) := by
        convert hrest using 1; ac_rfl
      have ⟨_, hcap⟩ := EncodedLen.vecU8Buf_bounds hbuf
      simp only [v1StateInnerCap, huc, optCt1SentCap]
      have hne : g.b.gCt1Sampled.uc.f3.cap + 2#64 ≠ 0#64 := by bv_omega
      exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Execute the `.rodata` half-word jump table dispatch at `+1880 .. +1896` (`0x6d768 .. 0x6d778`)
from `entry + 1880#64` to `entry + off`. -/
macro "step_etv_jump_to " entry:term:max off:num s1:term:max idx:term:max hx8:term:max : tactic =>
  `(tactic| (
    have _hx8 : ($s1).readReg64 .x8 = $idx := $hx8
    dsimp only [encodeToVecJumpTableBytes8At]
    apply SepWPp.of_sepWP_cs (mid := $entry + BitVec.ofNat 64 $off)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])))

end CryptoVerification.SpqrV1.Prost.EncodeToVec
