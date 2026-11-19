/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendDispatch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge1 -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived2
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# Phase 4 Finish, Output Size Bounds, and `.headerReceived` Panic Path for `spqr::send`

Proves the alignment-free Phase 4 result builder (`step_send_finish_320a4'`), the
`pqRatchetStatePBEncodedLen` output size bound, `PolyEncoder.nextChunk` infallibility on
well-formed encoders, and the `.headerReceived` panic path when `K.encaps1` returns `none`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local simp, local arm64_norm, local wp_norm] ite_zero32_self ite_zero64_self

/-! ## Alignment-Free Phase 4 Finish (`0x320a4 -> 0x31a54`) -/

open CryptoVerification.SpqrV1.Top.StateSize in
theorem pqRatchetStatePBEncodedLen_lt_of_send (F : ShaCompress) (K : MlKem)
    {stateBytes tape tape' : Bytes} {statePb : PqRatchetStatePB V1State} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    {chainPb : Option ChainPB}
    (hs : stateBytes.length < 2 ^ 32)
    (hdec : decodeState (spqrDeps F K) stateBytes = .ok statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hsend0 : st0.send K tape = .ok (sOut, tape'))
    (hch_le : optRaw rawChain chainPb ≤ optRaw rawChain statePb.chain + 624) :
    Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := statePb.versionNegotiation
        chain := chainPb
        inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63 := by
  rw [← Prost.EncodeToVec.pqRatchetStatePBEncodedLen_eq_proto]
  have hraw := decodeState_spqrDeps_raw_le hdec
  rcases States.from_pb_raw_le hfrom with ⟨hst0_raw, hst0_pts⟩
  have hst1_raw := (States.send_raw_le hst0_pts hsend0).1
  have hraw' : optRaw rawVN statePb.versionNegotiation + optRaw rawChain statePb.chain +
      rawV1State pb ≤ 201 * stateBytes.length := by
    simpa only [pbToPqRatchetState, rawPqState, rawPqInner, hinner, Option.map, optRaw_some] using hraw
  have hle : rawPqState {
      versionNegotiation := statePb.versionNegotiation
      chain := chainPb
      inner := some (.v1 sOut.state.into_pb) } ≤ 356 * 2 ^ 32 + 2000000 := by
    show optRaw rawVN statePb.versionNegotiation + optRaw rawChain chainPb +
      rawV1State sOut.state.into_pb ≤ 356 * 2 ^ 32 + 2000000
    omega
  exact (encodeState_length_lt_of_rawPqState_le hle).2.2.1

/-! ## `PolyEncoder.nextChunk` Infallibility on Well-Formed Encoders -/

@[expose] def PolyEncoderValid (enc : PolyEncoder) : Prop :=
  match enc.s with
  | .points pts => pts.length = NUM_POLYS ∧ ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555
  | .polys polys => polys.length = NUM_POLYS

private def firstSlowIdxAux (idx : Nat) (pts : List Point) : Nat → Nat → Nat
  | 0, _ => 16
  | rem + 1, i =>
    if idx < (pts[i]?.getD ⟨[]⟩).value.length then
      firstSlowIdxAux idx pts rem (i + 1)
    else i

private theorem firstSlowIdxAux_le_16 (idx : Nat) (pts : List Point) :
    ∀ (rem i : Nat), i + rem = 16 → firstSlowIdxAux idx pts rem i ≤ 16
  | 0, _, _ => by simp [firstSlowIdxAux]
  | rem + 1, i, h => by
    unfold firstSlowIdxAux; split_ifs
    · exact firstSlowIdxAux_le_16 idx pts rem (i + 1) (by omega)
    · omega

private theorem firstSlowIdxAux_fast (idx : Nat) (pts : List Point) :
    ∀ (rem i j : Nat), i + rem = 16 → i ≤ j → j < firstSlowIdxAux idx pts rem i →
      idx < (pts[j]?.getD ⟨[]⟩).value.length
  | 0, _, _, _, _, hj => by simp [firstSlowIdxAux] at hj; omega
  | rem + 1, i, j, h, hij, hj => by
    unfold firstSlowIdxAux at hj; split_ifs at hj with hlt
    · rcases Nat.eq_or_lt_of_le hij with rfl | hgt
      · exact hlt
      · exact firstSlowIdxAux_fast idx pts rem (i + 1) j (by omega) hgt hj
    · omega

private theorem firstSlowIdxAux_slow (idx : Nat) (pts : List Point) :
    ∀ (rem i : Nat), i + rem = 16 → firstSlowIdxAux idx pts rem i < 16 →
      (pts[firstSlowIdxAux idx pts rem i]?.getD ⟨[]⟩).value.length ≤ idx
  | 0, _, _, hlt16 => by simp [firstSlowIdxAux] at hlt16
  | rem + 1, i, h, hlt16 => by
    unfold firstSlowIdxAux at hlt16 ⊢; split_ifs at hlt16 ⊢
    · exact firstSlowIdxAux_slow idx pts rem (i + 1) (by omega) hlt16
    · omega

private theorem chunkPointsPolysBytes_length (idx : BitVec 16) (pts : List Point)
    (polys : List LibsignalSpqrV1.Poly) (i k rem total : Nat)
    (htot : total = k + rem) :
    (chunkPointsBytes idx pts i k ++ chunkPolysBytes idx polys (i + k) rem).length = 2 * total := by
  rw [List.length_append, chunkPointsBytes_length, chunkPolysBytes_length, htot, Nat.mul_add]

private theorem chunkAtLoop_points_prefix_ge_eq (idx : BitVec 32) (pts : List Point)
    (polys : List LibsignalSpqrV1.Poly)
    (hlen_pts : pts.length = 16)
    (hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok polys) :
    ∀ (total k i rem : Nat)
      (_hle : (i + k) + (rem + 1) ≤ 16)
      (htot : total = k + (rem + 1)),
      (∀ j (hj : j < pts.length), i ≤ j → j < i + k →
        (idx.setWidth 16).toNat < (pts[j]'hj).value.length) →
      (pts[i + k]'(by omega)).value.length ≤ (idx.setWidth 16).toNat →
      PolyEncoder.chunkAtLoop (idx.setWidth 16) i total { idx := idx, s := .points pts } =
        .ok ({ idx := idx, s := .polys polys },
          ⟨chunkPointsBytes (idx.setWidth 16) pts i k ++
            chunkPolysBytes (idx.setWidth 16) polys (i + k) (rem + 1),
            chunkPointsPolysBytes_length (idx.setWidth 16) pts polys i k (rem + 1) total htot⟩)
  | 0, k, i, rem, _, htot, _, _ => by omega
  | t + 1, 0, i, rem, hle, htot, _hfast, hslow => by
    have ht : t = rem := by omega
    subst ht
    simp only [Nat.add_zero, chunkPointsBytes, List.nil_append] at hle hslow ⊢
    exact chunkAtLoop_points_ge_eq idx pts polys t i hle hlen_pts hslow hloop
  | t + 1, k + 1, i, rem, hle, htot, hfast, hslow => by
    have hi16 : i < 16 := by omega
    have hi_len : i < pts.length := by omega
    have hlt_i : (idx.setWidth 16).toNat < (pts[i]'hi_len).value.length :=
      hfast i hi_len (Nat.le_refl i) (by omega)
    have hpt_opt : pts[i]? = some (pts[i]'hi_len) := List.getElem?_eq_getElem hi_len
    have hval_opt : (pts[i]'hi_len).value[(idx.setWidth 16).toNat]? =
        some ((pts[i]'hi_len).value[(idx.setWidth 16).toNat]'hlt_i) :=
      List.getElem?_eq_getElem hlt_i
    have hmod : ((idx.setWidth 16).toNat * 16 + i) % 16 = i := totalIdx_mod_16 (idx.setWidth 16) hi16
    have hdiv : ((idx.setWidth 16).toNat * 16 + i) / 16 = (idx.setWidth 16).toNat :=
      totalIdx_div_16 (idx.setWidth 16) hi16
    have hpt := pointAt_points_lt_eq (idx := idx) hi_len hlt_i
    have hadd_assoc : (i + 1) + k = i + (k + 1) := by omega
    have ih := chunkAtLoop_points_prefix_ge_eq idx pts polys hlen_pts hloop t k (i + 1) rem
      (by omega) (by omega)
      (fun j hj hij hjk => hfast j hj (by omega) (by omega))
      (by simpa [hadd_assoc] using hslow)
    unfold PolyEncoder.chunkAtLoop chunkPointsBytes
    simp only [hmod, hdiv, hpt, ih, hpt_opt, hval_opt, Option.getD_some,
      hadd_assoc, List.cons_append, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

private def pointToPolyPure (pt : Point) : Poly :=
  if pt.value.length = 0 then
    Poly.zero
  else
    let pts := PolyEncoder.enumeratePts 0 pt.value
    Poly.lagrangeSum pts (completePointsBasisPure pts)

private theorem fromCompletePoints_enumeratePts_eq (pt : Point)
    (hbound : pt.value.length ≤ 0x0555555555555555) :
    Poly.fromCompletePoints (PolyEncoder.enumeratePts 0 pt.value) =
      .ok (.ok (pointToPolyPure pt)) := by
  have hlen : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
    enumeratePts_length 0 pt.value
  by_cases hn0 : pt.value.length = 0
  · have hnil : pt.value = [] := List.eq_nil_of_length_eq_zero hn0
    unfold pointToPolyPure
    simp only [hn0, ↓reduceIte]
    rw [hnil]
    rfl
  · have hcomp : Poly.checkCompletePoints 0 (PolyEncoder.enumeratePts 0 pt.value) = true :=
      checkCompletePoints_enumeratePts 0 pt.value
    have hbound' : (PolyEncoder.enumeratePts 0 pt.value).length ≤ 0x0555555555555555 := by
      omega
    rw [fromCompletePoints_eq_ok (PolyEncoder.enumeratePts 0 pt.value) hcomp hbound']
    unfold pointToPolyPure
    simp [hn0]

private theorem pointsToPolysLoop_eq_map (pts : List Point)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555) :
    ∀ (rem i : Nat) (acc : List Poly),
      i + rem = pts.length →
      PolyEncoder.pointsToPolysLoop pts i rem acc =
        .ok (acc ++ (pts.drop i).map pointToPolyPure)
  | 0, i, acc, hlen => by
    have hi : i = pts.length := by omega
    subst hi
    simp [PolyEncoder.pointsToPolysLoop]
  | rem + 1, i, acc, hlen => by
    have hi : i < pts.length := by omega
    have hpt : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
    have hbound_i : (pts[i]'hi).value.length ≤ 0x0555555555555555 :=
      hbounds (pts[i]'hi) (List.getElem_mem hi)
    have hfc := fromCompletePoints_enumeratePts_eq (pts[i]'hi) hbound_i
    have ih := pointsToPolysLoop_eq_map pts hbounds rem (i + 1)
      (acc ++ [pointToPolyPure (pts[i]'hi)]) (by omega)
    have hdrop : pts.drop i = (pts[i]'hi) :: pts.drop (i + 1) :=
      List.drop_eq_getElem_cons hi
    unfold PolyEncoder.pointsToPolysLoop
    simp only [hpt, hfc, ih, hdrop, List.map_cons, List.append_assoc, List.singleton_append,
      Bind.bind, Except.bind]

private theorem nextChunk_points_slow_eq {idx : BitVec 32} {pts : List Point}
    (hlen_pts : pts.length = 16)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (i0 : Nat) (hi0 : i0 < 16)
    (hfast : ∀ j (hj : j < pts.length), j < i0 →
      (idx.setWidth 16).toNat < (pts[j]'hj).value.length)
    (hslow : (pts[i0]'(by omega)).value.length ≤ (idx.setWidth 16).toNat) :
    PolyEncoder.nextChunk { idx := idx, s := .points pts } =
      .ok ({ idx := idx + 1#32, s := .polys (pts.map pointToPolyPure) },
        { index := idx.setWidth 16,
          data := ⟨chunkPointsBytes (idx.setWidth 16) pts 0 i0 ++
            chunkPolysBytes (idx.setWidth 16) (pts.map pointToPolyPure) i0 (15 - i0 + 1),
            by simpa using chunkPointsPolysBytes_length (idx.setWidth 16) pts
                 (pts.map pointToPolyPure) 0 i0 (15 - i0 + 1) 16 (by omega)⟩ }) := by
  have hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] = .ok (pts.map pointToPolyPure) := by
    have h := pointsToPolysLoop_eq_map pts hbounds 16 0 [] (by omega)
    simp only [List.nil_append, List.drop_zero] at h
    exact h
  unfold PolyEncoder.nextChunk PolyEncoder.chunkAt
  have hchunk := chunkAtLoop_points_prefix_ge_eq idx pts (pts.map pointToPolyPure) hlen_pts hloop
    16 i0 0 (15 - i0) (by omega) (by omega)
    (fun j hj _ hjlt => hfast j hj (by omega)) (by simpa using hslow)
  simp only [Nat.zero_add] at hchunk
  rw [hchunk]
  rfl

open CryptoVerification.SpqrV1.Poly.NextChunk in
theorem nextChunk_ok_of_valid {enc : PolyEncoder} (hv : PolyEncoderValid enc) :
    ∃ enc' chunk, enc.nextChunk = .ok (enc', chunk) := by
  rcases enc with ⟨idx, s⟩
  cases s with
  | polys polys =>
    have hlen : polys.length = 16 := hv
    exact ⟨_, _, nextChunk_polys_eq hlen⟩
  | points pts =>
    rcases hv with ⟨hlen_pts, hbounds⟩
    have hlen16 : pts.length = 16 := hlen_pts
    let i0 := firstSlowIdxAux (idx.setWidth 16).toNat pts 16 0
    have hi0_le : i0 ≤ 16 := firstSlowIdxAux_le_16 (idx.setWidth 16).toNat pts 16 0 (by omega)
    by_cases hi0 : i0 < 16
    · have hi0_len : i0 < pts.length := by omega
      have hslow : (pts[i0]'hi0_len).value.length ≤ (idx.setWidth 16).toNat := by
        have h := firstSlowIdxAux_slow (idx.setWidth 16).toNat pts 16 0 (by omega) hi0
        change (pts[i0]?.getD ⟨[]⟩).value.length ≤ (idx.setWidth 16).toNat at h
        simpa [List.getElem?_eq_getElem hi0_len] using h
      have hfast : ∀ j (hj : j < pts.length), j < i0 →
          (idx.setWidth 16).toNat < (pts[j]'hj).value.length := by
        intro j hj hjlt
        have h := firstSlowIdxAux_fast (idx.setWidth 16).toNat pts 16 0 j (by omega) (by omega) hjlt
        simpa [List.getElem?_eq_getElem hj] using h
      exact ⟨_, _, nextChunk_points_slow_eq hlen16 hbounds i0 hi0 hfast hslow⟩
    · have hi0_16 : i0 = 16 := by omega
      have hall : ∀ k (hk : k < pts.length),
          (idx.setWidth 16).toNat < (pts[k]'hk).value.length := by
        intro k hk
        have hk_i0 : k < i0 := by omega
        have h := firstSlowIdxAux_fast (idx.setWidth 16).toNat pts 16 0 k (by omega) (by omega) hk_i0
        simpa [List.getElem?_eq_getElem hk] using h
      exact ⟨_, _, nextChunk_points_all_lt_eq hlen16 hall⟩

theorem polyEncoderAt_entails_valid (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    Poly.polyEncoderAt A a enc ⊢ ⌜PolyEncoderValid enc⌝ ∗ Poly.polyEncoderAt A a enc := by
  rcases enc with ⟨idx, s⟩
  unfold Poly.polyEncoderAt Poly.encoderStateAt PolyEncoderValid
  dsimp only
  cases s with
  | points pts =>
    dsimp only
    have hpull :
        ((⌜pts.length = NUM_POLYS ∧ ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555⌝ ∗
          (a ↦₆₄ Poly.polyEncoderPointsTag) ∗ Poly.pointListOf A (a + Poly.polyEncoderVecsOff) pts) ∗
         ((a + Poly.polyEncoderIdxOff) ↦₃₂ idx) ∗
         memRegion (a + Poly.polyEncoderPadOff) Poly.polyEncoderPadSize) =
        ⌜pts.length = NUM_POLYS ∧ ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555⌝ ∗
        (((a ↦₆₄ Poly.polyEncoderPointsTag) ∗ Poly.pointListOf A (a + Poly.polyEncoderVecsOff) pts) ∗
         ((a + Poly.polyEncoderIdxOff) ↦₃₂ idx) ∗
         memRegion (a + Poly.polyEncoderPadOff) Poly.polyEncoderPadSize) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))
  | polys polys =>
    dsimp only
    have hpull :
        ((⌜polys.length = NUM_POLYS⌝ ∗
          (a ↦₆₄ Poly.polyEncoderPolysTag) ∗ Poly.polyListOf A (a + Poly.polyEncoderVecsOff) polys) ∗
         ((a + Poly.polyEncoderIdxOff) ↦₃₂ idx) ∗
         memRegion (a + Poly.polyEncoderPadOff) Poly.polyEncoderPadSize) =
        ⌜polys.length = NUM_POLYS⌝ ∗
        (((a ↦₆₄ Poly.polyEncoderPolysTag) ∗ Poly.polyListOf A (a + Poly.polyEncoderVecsOff) polys) ∗
         ((a + Poly.polyEncoderIdxOff) ↦₃₂ idx) ∗
         memRegion (a + Poly.polyEncoderPadOff) Poly.polyEncoderPadSize) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))

theorem encodeBytesResult_valid {msg : Bytes} {enc : PolyEncoder}
    (heven : msg.length % 2 = 0) (hle : msg.length ≤ 1048576)
    (henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:63" msg = .ok enc ∨
            expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" msg = .ok enc) :
    PolyEncoderValid enc := by
  obtain ⟨enc0, he0, he1, he2⟩ := encodeBytesResult_of_len_even_le heven hle
  have h_eq : enc0 = enc := by
    rcases henc with h | h
    · exact Except.ok.inj (he1.symm.trans h)
    · exact Except.ok.inj (he2.symm.trans h)
  subst h_eq
  have h1 : (msg.length % 2 != 0) = false := by simp [heven]
  have h2 : ¬ (65536 * NUM_POLYS < msg.length) := by
    change ¬ (65536 * 16 < msg.length); omega
  have he0' :
      encodeBytesResult msg =
        .ok { idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate NUM_POLYS { value := [] })) } := by
    unfold encodeBytesResult; simp [h1, h2]
  cases he0.symm.trans he0'
  unfold PolyEncoderValid
  dsimp only
  have hinit_len : (List.replicate NUM_POLYS ({ value := [] } : Point)).length = 16 := by decide
  refine ⟨(distributeMsgChunks_eq_ok msg 0 (List.replicate NUM_POLYS { value := [] }) heven hinit_len).2, ?_⟩
  intro pt hpt
  have hlen_pt := distributeMsgChunksTotal_value_length_le msg 0 (List.replicate NUM_POLYS { value := [] })
    heven hinit_len (by intro p hp; rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; decide) pt hpt
  omega

theorem send_keysSampled_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (hv : PolyEncoderValid st.sending_hdr) :
    ∃ sOut tape', (States.keysSampled st).send K tape = .ok (sOut, tape') := by
  obtain ⟨enc', chunk, hnc⟩ := nextChunk_ok_of_valid hv
  have hnc' : spqrPolyApi.next_chunk st.sending_hdr = .ok (enc', chunk) := by
    change st.sending_hdr.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (enc', chunk)
    rw [hnc]; rfl
  unfold States.send Chunked.SendEk.KeysSampled.send_hdr_chunk
  simp only [hnc', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_headerSent_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hv_ek : PolyEncoderValid st.sending_ek) :
    ∃ sOut tape', (States.headerSent st).send K tape = .ok (sOut, tape') := by
  obtain ⟨ek', chunk_ek, hnc_ek⟩ := nextChunk_ok_of_valid hv_ek
  have hnc_ek' : spqrPolyApi.next_chunk st.sending_ek = .ok (ek', chunk_ek) := by
    change st.sending_ek.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (ek', chunk_ek)
    rw [hnc_ek]; rfl
  unfold States.send Chunked.SendEk.HeaderSent.send_ek_chunk
  simp only [hnc_ek', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_ct1Received_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (hv_ek : PolyEncoderValid st.sending_ek) :
    ∃ sOut tape', (States.ct1Received st).send K tape = .ok (sOut, tape') := by
  obtain ⟨ek', chunk_ek, hnc_ek⟩ := nextChunk_ok_of_valid hv_ek
  have hnc_ek' : spqrPolyApi.next_chunk st.sending_ek = .ok (ek', chunk_ek) := by
    change st.sending_ek.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (ek', chunk_ek)
    rw [hnc_ek]; rfl
  unfold States.send Chunked.SendEk.Ct1Received.send_ek_chunk
  simp only [hnc_ek', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_ct1Sampled_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (hv : PolyEncoderValid st.sending_ct1) :
    ∃ sOut tape', (States.ct1Sampled st).send K tape = .ok (sOut, tape') := by
  obtain ⟨enc', chunk, hnc⟩ := nextChunk_ok_of_valid hv
  have hnc' : spqrPolyApi.next_chunk st.sending_ct1 = .ok (enc', chunk) := by
    change st.sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (enc', chunk)
    rw [hnc]; rfl
  unfold States.send Chunked.SendCt.Ct1Sampled.send_ct1_chunk
  simp only [hnc', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_ekReceivedCt1Sampled_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hv : PolyEncoderValid st.sending_ct1) :
    ∃ sOut tape', (States.ekReceivedCt1Sampled st).send K tape = .ok (sOut, tape') := by
  obtain ⟨enc', chunk, hnc⟩ := nextChunk_ok_of_valid hv
  have hnc' : spqrPolyApi.next_chunk st.sending_ct1 = .ok (enc', chunk) := by
    change st.sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (enc', chunk)
    rw [hnc]; rfl
  unfold States.send Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk
  simp only [hnc', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_ct2Sampled_ok_of_valid {F : ShaCompress} (K : MlKem) (tape : Bytes)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hv : PolyEncoderValid st.sending_ct2) :
    ∃ sOut tape', (States.ct2Sampled st).send K tape = .ok (sOut, tape') := by
  obtain ⟨enc', chunk, hnc⟩ := nextChunk_ok_of_valid hv
  have hnc' : spqrPolyApi.next_chunk st.sending_ct2 = .ok (enc', chunk) := by
    change st.sending_ct2.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (enc', chunk)
    rw [hnc]; rfl
  unfold States.send Chunked.SendCt.Ct2Sampled.send_ct2_chunk
  simp only [hnc', StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem keysUnsampled_macKey_le_rawV1State {F : ShaCompress}
    (s : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    s.uc.auth.macKey.length ≤ rawV1State (States.keysUnsampled (P := spqrPolyApi) s).into_pb := by
  unfold States.into_pb Chunked.SendEk.KeysUnsampled.into_pb
    Unchunked.SendEk.KeysUnsampled.into_pb spqrAuthApi Authenticator.intoPb
    rawV1State rawInnerState rawChKeysUnsampled rawUcKeysUnsampled rawAuth optRaw
  dsimp only
  omega

theorem send_keysUnsampled_ok_of_le_64 {F : ShaCompress} (K : MlKem) {tape : Bytes}
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    (hk : st.uc.auth.macKey.length < 2 ^ 32)
    (h64 : 64 ≤ tape.length) :
    ∃ (sOut : V1Send spqrPolyApi (spqrAuthApi F)) (tape' : Bytes),
      (States.keysUnsampled (P := spqrPolyApi) st).send K tape = .ok (sOut, tape') := by
  let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, by rw [List.length_take]; omega⟩
  let hdr := (K.fromSeed seed).1.toList
  have hhdr_len : hdr.length = 64 := fromSeed_hdr_len K seed
  have hmac_ok : st.uc.auth.macHdr F st.uc.epoch hdr = .ok (st.uc.auth.macHdrUnchecked F st.uc.epoch hdr) := by
    apply Authenticator.macHdr_of_lt F st.uc.auth st.uc.epoch hdr hk
    have hlbl : Authenticator.hdrLabel.length = 33 := by rfl
    have hep : (CryptoGames.HMAC.toBEBytes 8 st.uc.epoch).length = 8 := by rfl
    rw [List.length_append, List.length_append, hlbl, hep, hhdr_len]
    omega
  let mac := st.uc.auth.macHdrUnchecked F st.uc.epoch hdr
  have hmsg_len : (hdr ++ mac).length = 96 := by
    rw [List.length_append]
    have h2 : mac.length = 32 := macHdrUnchecked_length F st.uc.auth st.uc.epoch hdr
    omega
  obtain ⟨sending_hdr, _, henc, _⟩ := encodeBytesResult_of_len_even_le (msg := hdr ++ mac)
    (by rw [hmsg_len]) (by rw [hmsg_len]; decide)
  have hv_hdr : PolyEncoderValid sending_hdr :=
    encodeBytesResult_valid (by rw [hmsg_len]) (by rw [hmsg_len]; decide) (Or.inl henc)
  obtain ⟨sending_hdr', chunk, hnc⟩ := nextChunk_ok_of_valid hv_hdr
  have hsend := send_hdr_chunk_of_ok K st h64 hmac_ok henc hnc
  unfold States.send
  simp only [hsend, StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  exact ⟨_, _, rfl⟩

theorem send_headerReceived_ok_or_encaps1_of_le_32 {F : ShaCompress} (K : MlKem) {tape : Bytes}
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (h32 : 32 ≤ tape.length) :
    (∃ sOut tape', (States.headerReceived st).send K tape = .ok (sOut, tape')) ∨
    (K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none ∧
     (States.headerReceived st).send K tape = .error (.panic .encaps1Failed)) := by
  cases hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ with
  | none =>
    right
    have herr := send_ct1_chunk_of_encaps1_none K st h32 hencaps
    refine ⟨rfl, ?_⟩
    dsimp only [States.send]
    rw [herr]
    rfl
  | some triple =>
    left
    rcases triple with ⟨ct1, es, ss⟩
    obtain ⟨sending_ct1, _, henc⟩ := encodeBytesResult_ct1 ct1
    have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length ct1
    have hv_ct1 : PolyEncoderValid sending_ct1 :=
      encodeBytesResult_valid (by rw [hct1_len]) (by rw [hct1_len]; decide) (Or.inr henc)
    obtain ⟨sending_ct1', chunk, hnc⟩ := nextChunk_ok_of_valid hv_ct1
    have hsend_ct1 := send_ct1_chunk_of_ok K st h32 hencaps henc hnc
    unfold States.send
    simp only [hsend_ct1, StatesResult.ofPanic, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    exact ⟨_, _, rfl⟩

@[expose] def statesPolyEncoderValid {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysSampled st => PolyEncoderValid st.sending_hdr
  | .headerSent st => PolyEncoderValid st.sending_ek
  | .ct1Received st => PolyEncoderValid st.sending_ek
  | .ct1Sampled st => PolyEncoderValid st.sending_ct1
  | .ekReceivedCt1Sampled st => PolyEncoderValid st.sending_ct1
  | .ct2Sampled st => PolyEncoderValid st.sending_ct2
  | _ => True

private theorem pull_pure_2 (P : Prop) (A B C : SepProp) :
    A ∗ (⌜P⌝ ∗ B) ∗ C ⊢ ⌜P⌝ ∗ (A ∗ B ∗ C) := by
  apply Entails.of_eq; ac_rfl

private theorem pull_pure_ct1Sampled (P : Prop) (A B : SepProp) :
    (⌜P⌝ ∗ A) ∗ B ⊢ ⌜P⌝ ∗ (A ∗ B) := by
  apply Entails.of_eq; ac_rfl

theorem chunkedStatesAt_entails_polyEncoderValid (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st0 : States spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a st0 ⊢ ⌜statesPolyEncoderValid st0⌝ ∗ chunkedStatesAt A a st0 := by
  cases st0 with
  | keysSampled s =>
    dsimp only [chunkedStatesAt, chunkedKeysSampledAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_hdr)))) ?_
    apply Entails.of_eq; ac_rfl
  | headerSent s =>
    dsimp only [chunkedStatesAt, chunkedHeaderSentAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_ek)))) ?_
    apply Entails.of_eq; ac_rfl
  | ct1Received s =>
    dsimp only [chunkedStatesAt, chunkedCt1ReceivedAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_ek)))) ?_
    apply Entails.of_eq; ac_rfl
  | ct1Sampled s =>
    dsimp only [chunkedStatesAt, chunkedCt1SampledAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_left (polyEncoderAt_entails_valid A a s.sending_ct1)) ?_
    apply Entails.of_eq; ac_rfl
  | ekReceivedCt1Sampled s =>
    dsimp only [chunkedStatesAt, chunkedEkReceivedCt1SampledAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_ct1)))) ?_
    apply Entails.of_eq; ac_rfl
  | ct2Sampled s =>
    dsimp only [chunkedStatesAt, chunkedCt2SampledAt, statesPolyEncoderValid]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
      (polyEncoderAt_entails_valid A (a + 8#64) s.sending_ct2)))) ?_
    apply Entails.of_eq; ac_rfl
  | _ =>
    exact Entails.pure_right trivial (Entails.refl _)

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp Qp' : State → SepProp → Prop}
    (hq : ∀ sf P_f, Q sf P_f → Q' sf P_f)
    (hqp : ∀ sf P_f, Qp sf P_f → Qp' sf P_f)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q' Qp' := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, hq_f⟩ | ⟨hpan, P_f, hmf, hqp_f⟩ | hoom
  · exact Or.inl ⟨hpc, hrun, P_f, hmf, hq sf P_f hq_f⟩
  · exact Or.inr (Or.inl ⟨hpan, P_f, hmf, hqp sf P_f hqp_f⟩)
  · exact Or.inr (Or.inr hoom)

theorem sepWPp_lift_allowPanic {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P R : SepProp} {P_panic : Prop} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P
      (fun sf P_f => Q sf P_f)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine sepWPp_mono_post (fun _ _ hq => hq) (fun sf P_f hqp hm => ?_) h
  have hm' := hqp hm
  refine Satisfies.mono (sepConj_mono_left ?_) hm'
  apply Entails.pure_left; intro ⟨ha, htr⟩
  exact Entails.pure_right ⟨Or.inr ha, htr⟩ (Entails.refl _)

theorem finish_model_panic {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp} {P_panic : Prop}
    {post : State → SepProp → Prop}
    (hp : P_panic)
    (hextern : prog.externAt? s.pc = some Rust.panicked)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine SepWPp.panic hrun hextern fun hm => ?_
  have htr_pref : s0.trace <+: (Rust.panicked s).trace := by
    simp only [Rust.panicked, htr]; exact List.prefix_refl _
  have hany : P ∗ R ⊢ (⌜(P_panic ∨ allocFailedIn s0 (Rust.panicked s)) ∧ s0.trace <+: (Rust.panicked s).trace⌝ ∗ anyHeap) ∗ R := by
    refine sepConj_mono_left (Entails.pure_right ⟨Or.inl hp, htr_pref⟩ (entails_anyHeap _))
  exact Satisfies.mono hany hm

theorem sepWPp_bind {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q sm Pm → SepWPp prog ret sm Pm Q' Qp) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps1, hout1⟩ := h1 R hm hL
  rcases hout1 with ⟨hpc, hrun, Pm, hmm, hq⟩ | hpan
  · obtain ⟨sf, hsteps2, hout2⟩ := h2 sm Pm hpc hrun hq R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩

section HeaderReceivedPanic

attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero



end HeaderReceivedPanic

/-! ## Phase 4 + Epilogue (`0x320a4 -> s0.readReg64 .x30`) -/

theorem message_serialize_len_lt_2_32 (msg : Message spqrPolyApi) (idx : BitVec 32) :
    (msg.serialize idx).length < 2 ^ 32 :=
  message_serialize_length_lt_2_32 msg idx

theorem memRegion_0_60_join (sp w0 w16 : BitVec 64) :
    (sp ↦₆₄ w0) ∗ memRegion (sp + 8#64) 8 ∗ ((sp + 16#64) ↦₆₄ w16) ∗
      memRegion (sp + 24#64) 24 ∗ memRegion (sp + 0x30#64) 48 ⊢
    memRegion sp 0x60 := by
  rw [ProofLib.memRegion_split' (b := sp) (n := 8) (k := 88) (b' := sp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := sp + 8#64) (n := 8) (k := 80) (b' := sp + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 72) (b' := sp + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 24#64) (n := 24) (k := 48) (b' := sp + 0x30#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))

@[expose] def stackRestA (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0xb0#64) 224 ∗ memRegion (sp + 0x548#64) 8 ∗
  memRegion (sp + 0x576#64) 10 ∗ memRegion (sp + 0x928#64) 40

theorem memRegion_b0_950_eq (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x950 - 0xb0) =
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗ stackRestA sp := by
  unfold stackRestA
  rw [ProofLib.memRegion_split' (b := sp + 0xb0#64) (n := 224) (k := 1984) (b' := sp + 0x190#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x190#64) (n := 928) (k := 1056) (b' := sp + 0x530#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x530#64) (n := 24) (k := 1032) (b' := sp + 0x548#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x548#64) (n := 8) (k := 1024) (b' := sp + 0x550#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x550#64) (n := 38) (k := 986) (b' := sp + 0x576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x576#64) (n := 10) (k := 976) (b' := sp + 0x580#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x580#64) (n := 16) (k := 960) (b' := sp + 0x590#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 920) (k := 40) (b' := sp + 0x928#64) rfl (by bv_omega) (by decide)]
  ac_rfl

@[expose] def stackRestC (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0xdd8#64) 8 ∗ memRegion (sp + 4184#64) 8 ∗
  memRegion (sp + 4696#64) 8 ∗ memRegion (sp + 7128#64) 8 ∗
  memRegion (sp + 7936#64) 32

theorem memRegion_cf0_1f20_eq (sp : BitVec 64) :
    memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗
      memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4056#64) 8 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 0x1260#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 ∗ stackRestC sp := by
  unfold stackRestC
  rw [ProofLib.memRegion_split' (b := sp + 0xcf0#64) (n := 80) (k := 4576) (b' := sp + 0xd40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xd40#64) (n := 80) (k := 4496) (b' := sp + 0xd90#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xd90#64) (n := 72) (k := 4424) (b' := sp + 0xdd8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xdd8#64) (n := 8) (k := 4416) (b' := sp + 3552#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 3552#64) (n := 504) (k := 3912) (b' := sp + 4056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4056#64) (n := 8) (k := 3904) (b' := sp + 4064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4064#64) (n := 16) (k := 3888) (b' := sp + 4080#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 104) (k := 3784) (b' := sp + 4184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4184#64) (n := 8) (k := 3776) (b' := sp + 4192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 504) (k := 3272) (b' := sp + 4696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4696#64) (n := 8) (k := 3264) (b' := sp + 0x1260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 2400) (k := 864) (b' := sp + 7104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7104#64) (n := 24) (k := 840) (b' := sp + 7128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7128#64) (n := 8) (k := 832) (b' := sp + 7136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 400) (k := 432) (b' := sp + 7536#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 400) (k := 32) (b' := sp + 7936#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_b0_1f20_eq (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) =
      memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
      memRegion (sp + 0x950#64) 928 ∗
      memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) := by
  rw [ProofLib.memRegion_split' (b := sp + 0xb0#64) (n := 0x950 - 0xb0) (k := 0x1f20 - 0x950) (b' := sp + 0x950#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x950#64) (n := 928) (k := 0x1f20 - 0xcf0) (b' := sp + 0xcf0#64) rfl (by bv_omega) (by decide)]

theorem sepWPp_drop_left {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem msgKey_slots_nil (A : RustAlloc) (sp : BitVec 64) :
    ((sp + 24#64) ↦₆₄ BitVec.ofNat 64 ([] : Bytes).length) ∗
      (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗
        DecodeState.vecU8Heap A mkCap mkPtr []) ⊢
    optMsgKeySlotsAt A sp none := by
  dsimp only [optMsgKeySlotsAt, List.length_nil, BitVec.ofNat_eq_ofNat]
  rw [sepExists_sepConj_right]; apply Arm64.Entails.sepExists_elim; intro mkCap
  rw [sepExists_sepConj_right]; apply Arm64.Entails.sepExists_elim; intro mkPtr
  exact Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr (Entails.of_eq (by ac_rfl)))

theorem msgKey_slots_len32 (A : RustAlloc) (sp : BitVec 64) (msgKey : Bytes)
    (h32 : msgKey.length = 32) :
    ((sp + 24#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
      (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗
        DecodeState.vecU8Heap A mkCap mkPtr msgKey) ⊢
    optMsgKeySlotsAt A sp (some ⟨msgKey, h32⟩) := by
  dsimp only [optMsgKeySlotsAt, List.Vector.toList]; rw [h32]
  rw [sepExists_sepConj_right]; apply Arm64.Entails.sepExists_elim; intro mkCap
  rw [sepExists_sepConj_right]; apply Arm64.Entails.sepExists_elim; intro mkPtr
  exact Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr (Entails.of_eq (by ac_rfl)))

theorem spqrHkdfWith_len_64 (F : ShaCompress) (salt ikm info : Bytes) :
    (spqrHkdfWith F salt ikm info 64).length = 64 := by
  change (CryptoGames.HKDF.hkdfExpand F (hkdfExtractBytes F salt ikm) info 64).length = 64
  rw [HkdfToSliceProof.hkdfExpand_64_eq]
  simp [Expand.t1_length, Expand.t2_length]

theorem nextKey_msgKey_len_32 (F : ShaCompress) (ced : ChainEpochDirection)
    {ced' : ChainEpochDirection} {idx : BitVec 32} {msgKey : Bytes}
    (h : ced.nextKey (spqrHkdfWith F) = .ok (ced', (idx, msgKey))) :
    msgKey.length = 32 := by
  unfold ChainEpochDirection.nextKey at h
  dsimp only [Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at h
  rcases hnk : ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) ced.next ced.ctr with _ | ⟨next', ctr', idx', mk'⟩ <;>
    rw [hnk] at h <;> dsimp only at h
  · contradiction
  · injection h with hpair; injection hpair with _ hout; injection hout with _ hmk
    unfold ChainEpochDirection.nextKeyInternal at hnk
    split at hnk <;> first | contradiction | skip
    split at hnk <;> first | contradiction | skip
    injection hnk with h1; injection h1 with _ h2; injection h2 with _ h3; injection h3 with _ hmk'
    rw [← hmk, ← hmk', List.length_take, List.length_drop, spqrHkdfWith_len_64]
    decide

theorem sendKey_msgKey_len_32 (F : ShaCompress) (c : Chain) (ep : Epoch)
    {c' : Chain} {idx : BitVec 32} {msgKey : Bytes}
    (h : c.sendKey (spqrHkdfWith F) ep = .ok (c', (idx, msgKey))) :
    msgKey.length = 32 := by
  unfold Chain.sendKey at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind, ChainResult.ofError] at h
    rcases hcidx : c.epochIdx ep with _ | idx0 <;> rw [hcidx] at h <;> dsimp only at h
    · contradiction
    · split at h
      · contradiction
      · rename_i link hlink
        rcases hnk : link.send.nextKey (spqrHkdfWith F) with _ | ⟨send', idx', mk'⟩ <;>
          rw [hnk] at h <;> dsimp only [ChainResult.ofPanic] at h
        · contradiction
        · injection h with hpair
          injection hpair with _ hout
          injection hout with _ hmk
          rw [← hmk]
          exact nextKey_msgKey_len_32 F link.send hnk

theorem sendKeyIntoPbChain_msgKey_len_32 (F : ShaCompress) (c : Chain) (epoch : Epoch)
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    (h : sendKeyIntoPbChain (spqrHkdfWith F) c epoch = .ok (idx, msgKey, chainPb)) :
    msgKey.length = 32 := by
  unfold sendKeyIntoPbChain at h
  split at h
  · contradiction
  · rcases hsk : c.sendKey (spqrHkdfWith F) (epoch - 1#64) with e | ⟨c2, idx', mk'⟩ <;>
      rw [hsk] at h <;> dsimp only [SpqrApiResult.ofChainResult] at h
    · rcases e with _ | _ <;> contradiction
    · injection h with h1; injection h1 with _ h2; injection h2 with hmk _
      rw [← hmk]
      exact sendKey_msgKey_len_32 F c (epoch - 1#64) hsk

theorem sendChainPhase_msgKey_cases (F : ShaCompress) (chain : Option ChainPB)
    (vn : Option VersionNegotiationPB) (key : Option EpochSecret) (epoch : Epoch)
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    (h : sendChainPhase (spqrHkdfWith F) chain vn key epoch = .ok (idx, msgKey, chainPb)) :
    msgKey = [] ∨ msgKey.length = 32 := by
  unfold sendChainPhase at h
  rcases hres : sendResolveChain (spqrHkdfWith F) chain vn with _ | (_ | c0) <;>
    rw [hres] at h <;> dsimp only [Bind.bind, Except.bind, sendStepChain] at h
  · contradiction
  · split at h
    · injection h with h1; injection h1 with _ h2; injection h2 with hmk _; exact Or.inl hmk.symm
    · contradiction
  · rcases key with _ | es <;> dsimp only at h
    · exact Or.inr (sendKeyIntoPbChain_msgKey_len_32 F c0 epoch h)
    · rcases hae : c0.addEpoch (spqrHkdfWith F) es with _ | c1 <;>
        rw [hae] at h <;> dsimp only [SpqrApiResult.ofChainPanic] at h
      · contradiction
      · exact Or.inr (sendKeyIntoPbChain_msgKey_len_32 F c1 epoch h)

theorem msgKey_to_optMsgKeySlotsAt (A : RustAlloc) (sp : BitVec 64) (msgKey : Bytes)
    (h : msgKey = [] ∨ msgKey.length = 32) :
    ∃ salt : CryptoGames.HKDF.Salt,
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt ∧
      (((sp + 24#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗
          DecodeState.vecU8Heap A mkCap mkPtr msgKey) ⊢
        optMsgKeySlotsAt A sp salt) := by
  rcases h with rfl | h32
  · refine ⟨none, rfl, msgKey_slots_nil A sp⟩
  · have hne : msgKey.isEmpty = false := by
      cases msgKey with
      | nil => simp at h32
      | cons _ _ => rfl
    refine ⟨some ⟨msgKey, h32⟩, ?_, msgKey_slots_len32 A sp msgKey h32⟩
    simp [hne, messageKeyToSalt?, h32]

theorem memRegion_1424_224_eq_24_200 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 224 =
      memRegion (sp + 1424#64) 24 ∗ memRegion (sp + 1448#64) 200 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 24) (k := 200) (b' := sp + 1448#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_590_224_eq_88_136 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 224 =
      memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 1512#64) 136 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 88) (k := 136) (b' := sp + 1512#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_1060_80_eq_48_32 (sp : BitVec 64) :
    memRegion (sp + 0x1060#64) 80 =
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 32 :=
  ProofLib.memRegion_split' (b := sp + 0x1060#64) (n := 48) (k := 32) (b' := sp + 4240#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_1260_928_eq_352_576 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 928 =
      memRegion (sp + 4704#64) 352 ∗ memRegion (sp + 5056#64) 576 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 352) (k := 576) (b' := sp + 5056#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_1260_928_eq_88_840 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 928 =
      memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 88) (k := 840) (b' := sp + 4792#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_7136_400_eq_16_384 (sp : BitVec 64) :
    memRegion (sp + 7136#64) 400 =
      memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 7152#64) 384 :=
  ProofLib.memRegion_split' (b := sp + 7136#64) (n := 16) (k := 384) (b' := sp + 7152#64)
    rfl (by bv_omega) (by decide)

theorem memRegion_0_30_eq (sp : BitVec 64) :
    memRegion sp 0x30 =
      memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗
      memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 8 ∗
      memRegion (sp + 32#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp) (n := 8) (k := 40) (b' := sp + 0x8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := sp + 0x8#64) (n := 8) (k := 32) (b' := sp + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 24) (b' := sp + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 24#64) (n := 8) (k := 16) (b' := sp + 32#64) rfl (by bv_omega) (by decide)]

theorem memRegion_32_16_eq_8_8 (sp : BitVec 64) :
    memRegion (sp + 32#64) 16 =
      memRegion (sp + 32#64) 8 ∗ memRegion (sp + 0x28#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 32#64) (n := 8) (k := 8) (b' := sp + 0x28#64)
    rfl (by bv_omega) (by decide)

@[expose] def stackRestB0_950 (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
  memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1648#64) 696 ∗ stackRestA sp

theorem memRegion_590_920_eq (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 920 =
      memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 1512#64) 136 ∗ memRegion (sp + 1648#64) 696 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 88) (k := 832) (b' := sp + 1512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 1512#64) (n := 136) (k := 696) (b' := sp + 1648#64) rfl (by bv_omega) (by decide)]

theorem memRegion_b0_950_eq_rest (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x950 - 0xb0) =
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x590#64) 88 ∗
      memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp := by
  rw [memRegion_b0_950_eq sp, memRegion_590_920_eq sp]
  unfold stackRestB0_950
  ac_rfl

@[expose] def stackRestCF0_1F20 (sp : BitVec 64) : SepProp :=
  memRegion (sp + 3632#64) 424 ∗ memRegion (sp + 4056#64) 8 ∗
  memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4104#64) 80 ∗
  memRegion (sp + 4272#64) 424 ∗ memRegion (sp + 5632#64) 1472 ∗
  memRegion (sp + 7120#64) 8 ∗ memRegion (sp + 7152#64) 384 ∗
  memRegion (sp + 7584#64) 352 ∗ stackRestC sp

theorem statesSendPostArmScratch_split (sp : BitVec 64) :
    statesSendPostArmScratch sp ∗ stackRestC sp =
      memRegion (sp + 32#64) 16 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 0x1060#64) 80 ∗
      memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 ∗
      memRegion (sp + 7136#64) 16 ∗ stackRestCF0_1F20 sp := by
  unfold statesSendPostArmScratch stackRestCF0_1F20
  rw [ProofLib.memRegion_split' (b := sp + 3552#64) (n := 80) (k := 424) (b' := sp + 3632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 24) (k := 80) (b' := sp + 4104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 80) (k := 424) (b' := sp + 4272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 88) (k := 2312) (b' := sp + 4792#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4792#64) (n := 840) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 16) (k := 384) (b' := sp + 7152#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_cf0_1f20_eq_rest (sp : BitVec 64) :
    memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 0x1060#64) 80 ∗
      memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
      memRegion (sp + 0x1d70#64) 48 ∗ stackRestCF0_1F20 sp := by
  rw [memRegion_cf0_1f20_eq sp]
  unfold stackRestCF0_1F20
  rw [ProofLib.memRegion_split' (b := sp + 3552#64) (n := 80) (k := 424) (b' := sp + 3632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 24) (k := 80) (b' := sp + 4104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 80) (k := 424) (b' := sp + 4272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 88) (k := 2312) (b' := sp + 4792#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4792#64) (n := 840) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7104#64) (n := 16) (k := 8) (b' := sp + 7120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 16) (k := 384) (b' := sp + 7152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 48) (k := 352) (b' := sp + 7584#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_b0_1f20_eq_finish (sp : BitVec 64) :
    memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) =
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1424#64) 24 ∗
      memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 4192#64) 48 ∗
      memRegion (sp + 4240#64) 32 ∗ memRegion (sp + 4704#64) 352 ∗
      memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
      memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
      stackRestCF0_1F20 sp := by
  have h590 : memRegion (sp + 0x590#64) 920 =
      memRegion (sp + 1424#64) 24 ∗ memRegion (sp + 1448#64) 200 ∗ memRegion (sp + 1648#64) 696 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 224) (k := 696) (b' := sp + 1648#64) rfl (by bv_omega) (by decide),
        memRegion_1424_224_eq_24_200 sp]
    ac_rfl
  have h1260 : memRegion (sp + 0x1260#64) 2400 =
      memRegion (sp + 4704#64) 352 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 5632#64) 1472 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 928) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
        memRegion_1260_928_eq_352_576 sp]
    ac_rfl
  rw [memRegion_b0_1f20_eq sp, memRegion_b0_950_eq sp, h590, memRegion_cf0_1f20_eq sp, h1260]
  unfold stackRestB0_950 stackRestCF0_1F20
  rw [ProofLib.memRegion_split' (b := sp + 3552#64) (n := 80) (k := 424) (b' := sp + 3632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 24) (k := 80) (b' := sp + 4104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 80) (k := 424) (b' := sp + 4272#64) rfl (by bv_omega) (by decide),
      memRegion_1060_80_eq_48_32 sp,
      ProofLib.memRegion_split' (b := sp + 7104#64) (n := 16) (k := 8) (b' := sp + 7120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 16) (k := 384) (b' := sp + 7152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 48) (k := 352) (b' := sp + 7584#64) rfl (by bv_omega) (by decide)]
  ac_rfl

end CryptoVerification.SpqrV1.Top.Send
