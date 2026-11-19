/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
public import LibsignalBinary.Proofs.ProtoCodecRoundTrip
public import Symbolic.Proofs.Refinement.EncodeWithCovered
public import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
public import Symbolic.Proofs.Tests.Shared.Composed.Runs
import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep

/-!
# Interpretation-Parametric Protobuf & Representation Helpers (`RecvNoCollision/Rep.lean`)

Provides:
1. Pure wire/varint cancellation lemmas (`append_inj_right_len`, `preKeyWire_msg_inj`,
   `trWireBytes_canonical_pq_inj`).
2. `gamma_randTerm_ne_zero`, `gamma_litOf`, `gamma_trHonestWireMsgE` for any `ExternInterpretation`.
3. `encMsg_tryFrom_inv`, `encMsg_mem_recvRepresentationsOn`, and `encMsg_faithfulInner`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Bytes ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg parseTrSignalMsg computeMac trMsgKeys kdfCk messageVersion trHonestWireMsg)
open DY.Libsignal.Refinement
  (WireFields canonicalVariation encodeWith paddedVarint WireTypeOk setField encodeField
   tryFrom_ok_inv deserialize_inv mergeBytes_inv mergeUint32_inv)
open DY.Libsignal.PQXDH.Refinement (PreKeyProto)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost PreKeyFields
   randTerm litOf ecKey kyberKey preKeyWire
   concretizeRandom gamma gamma' trWireBytes spqrHeaded recvRepresentationsOn FaithfulInner)
open CryptoGames.LibsignalSession (ProtoSignalMessage SignalMessage macLength)
open CryptoVerification.LibsignalProtoCodec
  (protoSignalCodec emptyProtoSignalMessage decodeKey decodeLoop mergeField mergeBytes mergeUint32
   encodeVarint encodeBytesField encodeUint32Field)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (encMsg encSig parse_encMsg)
open Symbolic.Swarm.CREF.TR (gamma_concat gamma_computeMac)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_random ms_pack_lit ms_pack_trWire)

/-! ## 1. List & Varint Length Injectivity (`< 2048` Bytes) -/

theorem append_inj_right_len {α : Type} {l₁ r₁ l₂ r₂ : List α}
    (h : l₁ ++ r₁ = l₂ ++ r₂) (hr : r₁.length = r₂.length) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have hlen : (l₁ ++ r₁).length = (l₂ ++ r₂).length := congrArg List.length h
  rw [List.length_append, List.length_append, hr] at hlen
  have hl : l₁.length = l₂.length := Nat.add_right_cancel hlen
  exact List.append_inj h hl

private theorem encodeVarint_len_check :
    ((List.range 2048).all fun n =>
      (encodeVarint (BitVec.ofNat 64 n)).length == (if n < 128 then 1 else 2)) = true := by
  decide +kernel

theorem encodeVarint_len_lt2048 {n : Nat} (hn : n < 2048) :
    (encodeVarint (BitVec.ofNat 64 n)).length = (if n < 128 then 1 else 2) := by
  have hall := List.all_eq_true.mp encodeVarint_len_check n (List.mem_range.mpr hn)
  exact beq_iff_eq.mp hall

private theorem paddedVarint_len_check :
    ((List.range 2048).all fun n =>
      (paddedVarint n 0).length == (if n < 128 then 1 else 2)) = true := by
  decide +kernel

theorem paddedVarint_len_lt2048 {n : Nat} (hn : n < 2048) :
    (paddedVarint n 0).length = (if n < 128 then 1 else 2) := by
  have hall := List.all_eq_true.mp paddedVarint_len_check n (List.mem_range.mpr hn)
  exact beq_iff_eq.mp hall

theorem encodeBytesField_some_inj {tag : Nat} {v v₀ : HwBytes}
    (hv : v.length < 2048) (hv₀ : v₀.length < 2048)
    (heq : encodeBytesField tag (some v) = encodeBytesField tag (some v₀)) :
    v = v₀ := by
  unfold encodeBytesField at heq
  dsimp only at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have hkv := List.append_cancel_left heq
  have hlen := congrArg List.length hkv
  rw [List.length_append, List.length_append,
      encodeVarint_len_lt2048 hv, encodeVarint_len_lt2048 hv₀] at hlen
  have hveq : v.length = v₀.length := by
    by_cases h1 : v.length < 128 <;> by_cases h2 : v₀.length < 128 <;>
      simp only [h1, h2, ↓reduceIte] at hlen <;> omega
  rw [hveq] at hkv
  exact List.append_cancel_left hkv

theorem preKeyWire_msg_inj
    {pkId : Option (BitVec 32)} {spkId kpkId regId : BitVec 32}
    {ik ek ct msg msg₀ : HwBytes}
    (hlen₀ : (preKeyWire pkId spkId kpkId regId ik ek ct msg₀).length < 2048)
    (heq : preKeyWire pkId spkId kpkId regId ik ek ct msg =
           preKeyWire pkId spkId kpkId regId ik ek ct msg₀) :
    msg = msg₀ := by
  have htot : (preKeyWire pkId spkId kpkId regId ik ek ct msg).length < 2048 := heq ▸ hlen₀
  unfold preKeyWire PreKeyProto.encode at heq htot hlen₀
  dsimp only at heq htot hlen₀
  have hm_lt : msg.length < 2048 := by
    simp only [List.length_cons, List.length_append, encodeBytesField] at htot
    omega
  have hm₀_lt : msg₀.length < 2048 := by
    simp only [List.length_cons, List.length_append, encodeBytesField] at hlen₀
    omega
  injection heq with _ hbody
  injection hbody with _ hproto
  let pre := encodeUint32Field 1 pkId ++ encodeBytesField 2 (some (ecKey ek)) ++
    encodeBytesField 3 (some ik)
  let suf := encodeUint32Field 5 (some regId) ++ encodeUint32Field 6 (some spkId) ++
    encodeUint32Field 7 (some kpkId) ++ encodeBytesField 8 (some (kyberKey ct))
  have hgrp : ∀ m : HwBytes,
      encodeUint32Field 1 pkId ++ encodeBytesField 2 (some (ecKey ek)) ++
      encodeBytesField 3 (some ik) ++ encodeBytesField 4 (some m) ++
      encodeUint32Field 5 (some regId) ++ encodeUint32Field 6 (some spkId) ++
      encodeUint32Field 7 (some kpkId) ++ encodeBytesField 8 (some (kyberKey ct)) =
      pre ++ (encodeBytesField 4 (some m) ++ suf) := by
    intro m; simp only [pre, suf, List.append_assoc]
  have hp1 := hgrp msg
  have hp2 := hgrp msg₀
  have hf4 : encodeBytesField 4 (some msg) ++ suf = encodeBytesField 4 (some msg₀) ++ suf :=
    List.append_cancel_left ((hp1.symm.trans hproto).trans hp2)
  exact encodeBytesField_some_inj hm_lt hm₀_lt (append_inj_right_len hf4 rfl).1

theorem trWireBytes_canonical_pq_inj {addr pq pq₀ : HwBytes} {f : WireFields}
    (hlen₀ : (trWireBytes addr canonicalVariation f pq₀).length < 2048)
    (heq : trWireBytes addr canonicalVariation f pq =
           trWireBytes addr canonicalVariation f pq₀) :
    pq = pq₀ := by
  have htot : (trWireBytes addr canonicalVariation f pq).length < 2048 := heq ▸ hlen₀
  rw [DY.Libsignal.Composed.Refinement.trWireBytes_canonical] at heq htot hlen₀
  rw [DY.Libsignal.Composed.Refinement.trWireBytes_canonical] at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have hmid_suf := List.append_cancel_left heq
  have hmid := (append_inj_right_len hmid_suf rfl).1
  have hpv42 : (paddedVarint 42 0).length = 1 := paddedVarint_len_lt2048 (by decide)
  by_cases hpq : pq = [] <;> by_cases hpq₀ : pq₀ = []
  · rw [hpq, hpq₀]
  · simp only [hpq, hpq₀, ↓reduceIte, encodeField] at hmid
    have h0 := congrArg List.length hmid
    simp only [List.length_nil, List.length_append, hpv42] at h0
    omega
  · simp only [hpq, hpq₀, ↓reduceIte, encodeField] at hmid
    have h0 := congrArg List.length hmid
    simp only [List.length_nil, List.length_append, hpv42] at h0
    omega
  · have hp_lt : pq.length < 2048 := by
      simp only [hpq, ↓reduceIte, List.length_append, encodeField] at htot
      omega
    have hp₀_lt : pq₀.length < 2048 := by
      simp only [hpq₀, ↓reduceIte, List.length_append, encodeField] at hlen₀
      omega
    simp only [hpq, hpq₀, ↓reduceIte, encodeField, List.append_assoc] at hmid
    have hvp := List.append_cancel_left hmid
    have hlen := congrArg List.length hvp
    rw [List.length_append, List.length_append,
        paddedVarint_len_lt2048 hp_lt, paddedVarint_len_lt2048 hp₀_lt] at hlen
    have hl_eq : pq.length = pq₀.length := by
      by_cases h1 : pq.length < 128 <;> by_cases h2 : pq₀.length < 128 <;>
        simp only [h1, h2, ↓reduceIte] at hlen <;> omega
    rw [hl_eq] at hvp
    exact List.append_cancel_left hvp

/-! ## 2. Basic `gamma` Unfoldings -/

theorem gamma_randTerm_ne_zero (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {ts sz : Nat} (hsz : sz ≠ 0) :
    gamma interp S g (randTerm ts sz) = g.σ ts sz := by
  have hg := ms_pack_random interp S g ⟨ts, sz⟩
  unfold gamma randTerm
  rw [hg]; dsimp only [DY.Libsignal.Composed.Refinement.gRandom, concretizeRandom]
  simp only [hsz, ↓reduceIte]; rfl

theorem gamma_litOf (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (b : HwBytes) :
    gamma interp S g (litOf b) = b := by
  have hv_aux : ∀ l : HwBytes, (l.map UInt8.ofBitVec).map UInt8.toBitVec = l := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => exact congrArg (x :: ·) ih
  let ba := ByteArray.mk (b.map UInt8.ofBitVec).toArray
  have hg := ms_pack_lit interp S g { lit := ba }
  change gamma' interp S g (litOf b) = _ at hg
  unfold gamma
  rw [hg]; dsimp only [DY.Libsignal.Composed.Refinement.gLit0,
    DY.Libsignal.Composed.Refinement.concretizeLit, DY.Libsignal.Composed.Refinement.node]
  exact hv_aux b

theorem gamma_trHonestWireMsgE (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk : Bytes) (ns pn : UInt32) (ct pq : Bytes) :
    let w := trHonestWireMsg rk ns pn ct pq
    gamma interp S g w =
      trWireBytes (g.addr w) canonicalVariation
        { version := 4, ratchetKey := gamma interp S g rk,
          counter := ns.toNat, previousCounter := pn.toNat,
          ciphertext := gamma interp S g ct }
        (gamma interp S g pq) := by
  intro w
  have hpack : w =
      (({ version := messageVersion, senderRatchetKey := rk, counter := ns,
          previousCounter := pn, ciphertext := ct, pqRatchet := pq,
          encodingVariation := canonicalVariation } : DY.TrWire.TrWireMsg.SubF Bytes).pack) := rfl
  unfold gamma
  rw [hpack, ms_pack_trWire interp S g ⟨messageVersion, rk, ns, pn, ct, pq, canonicalVariation⟩]
  rfl

/-! ## 3. Canonical `encMsg` Protobuf Inversion & Representation Helpers -/

theorem spqrHeaded_computeMac_false (mk ik1 ik2 w : Bytes) :
    spqrHeaded (computeMac mk ik1 ik2 w) = false := by
  have h := Symbolic.Swarm.CREF.TR.G1.notSpqrHeaded_computeMac mk ik1 ik2 w
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  unfold spqrHeaded
  rcases hv1 : (computeMac mk ik1 ik2 w).view? DY.Spqr.InitState.SubF with _ | _
  · rcases hv2 : (computeMac mk ik1 ik2 w).view? DY.Spqr.SendState.SubF with _ | _
    · rcases hv3 : (computeMac mk ik1 ik2 w).view? DY.Spqr.SendKey.SubF with _ | _
      · rcases hv4 : (computeMac mk ik1 ik2 w).view? DY.Spqr.SendMsg.SubF with _ | _
        · rcases hv5 : (computeMac mk ik1 ik2 w).view? DY.Spqr.RecvState.SubF with _ | _
          · rcases hv6 : (computeMac mk ik1 ik2 w).view? DY.Spqr.RecvKey.SubF with _ | _
            · rcases hv7 : (computeMac mk ik1 ik2 w).view? DY.Spqr.ChainKey.SubF with _ | _
              · rfl
              · rw [hv7] at h7; cases h7
            · rw [hv6] at h6; cases h6
          · rw [hv5] at h5; cases h5
        · rw [hv4] at h4; cases h4
      · rw [hv3] at h3; cases h3
    · rw [hv2] at h2; cases h2
  · rw [hv1] at h1; cases h1

theorem length_gamma_computeMac (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (mk ik1 ik2 w : Bytes) :
    (gamma interp S g (computeMac mk ik1 ik2 w)).length = 8 := by
  rw [gamma_computeMac]
  unfold Symbolic.Swarm.CREF.TR.computeMacBytes
  rw [List.length_take, Symbolic.Swarm.CREF.TR.length_hmacWith]
  decide

private theorem paddedVarint_zero_append_inj_aux :
    ∀ (s n m pad : Nat) (r1 r2 : HwBytes), n + m + pad < s →
      paddedVarint n 0 ++ r1 = paddedVarint m pad ++ r2 →
      n = m ∧ pad = 0 ∧ r1 = r2
  | 0, _, _, _, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | s + 1, n, m, pad, r1, r2, hs, heq => by
    by_cases hn : n < 128
    · have hl : paddedVarint n 0 = [BitVec.ofNat 8 n] := by
        rw [paddedVarint]; simp [hn]
      by_cases hm : m < 128 ∧ pad = 0
      · have hr : paddedVarint m pad = [BitVec.ofNat 8 m] := by
          rw [paddedVarint]; simp [hm]
        rw [hl, hr, List.singleton_append, List.singleton_append, List.cons.injEq] at heq
        have hnm : n = m := by
          have := congrArg BitVec.toNat heq.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
        exact ⟨hnm, hm.2, heq.2⟩
      · have hr : paddedVarint m pad =
            BitVec.ofNat 8 (m % 128 + 128) ::
              paddedVarint (m / 128) (if m < 128 then pad - 1 else pad) := by
          rw [paddedVarint]; simp [hm]
        rw [hl, hr, List.singleton_append, List.cons_append, List.cons.injEq] at heq
        have hbad := congrArg BitVec.toNat heq.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hbad; omega
    · have hl : paddedVarint n 0 =
          BitVec.ofNat 8 (n % 128 + 128) :: paddedVarint (n / 128) 0 := by
        rw [paddedVarint]; simp [hn]
      by_cases hm : m < 128 ∧ pad = 0
      · have hr : paddedVarint m pad = [BitVec.ofNat 8 m] := by
          rw [paddedVarint]; simp [hm]
        rw [hl, hr, List.cons_append, List.singleton_append, List.cons.injEq] at heq
        have hbad := congrArg BitVec.toNat heq.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hbad; omega
      · have hr : paddedVarint m pad =
            BitVec.ofNat 8 (m % 128 + 128) ::
              paddedVarint (m / 128) (if m < 128 then pad - 1 else pad) := by
          rw [paddedVarint]; simp [hm]
        rw [hl, hr, List.cons_append, List.cons_append, List.cons.injEq] at heq
        have hmod : n % 128 = m % 128 := by
          have := congrArg BitVec.toNat heq.1; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
        have hs' : n / 128 + m / 128 + (if m < 128 then pad - 1 else pad) < s := by split <;> omega
        obtain ⟨hdiv, hpad, hr_eq⟩ := paddedVarint_zero_append_inj_aux s (n / 128) (m / 128)
          (if m < 128 then pad - 1 else pad) r1 r2 hs' heq.2
        have hnm : n = m := by omega
        subst hnm; simp only [hn, ↓reduceIte] at hpad; exact ⟨rfl, hpad, hr_eq⟩

private theorem paddedVarint_zero_append_inj (n m pad : Nat) (r1 r2 : HwBytes)
    (heq : paddedVarint n 0 ++ r1 = paddedVarint m pad ++ r2) : n = m ∧ pad = 0 ∧ r1 = r2 :=
  paddedVarint_zero_append_inj_aux (n + m + pad + 1) n m pad r1 r2 (by omega) heq

private theorem decodeKey_encodeField_zero_inv {tag t' : Nat}
    {wt : CryptoVerification.LibsignalProtoCodec.WireType}
    {x : DY.Libsignal.Refinement.PbValue} {rest rest0 : HwBytes}
    (hwt : WireTypeOk tag x)
    (hkey : decodeKey (encodeField tag 0 0 x ++ rest) = some ((t', wt), rest0)) :
    t' = tag ∧ wt = x.wireType ∧ rest0 = x.body 0 ++ rest := by
  obtain ⟨kp, hbs, _, _, _⟩ := DY.Libsignal.Refinement.decodeKey_inv hkey
  rw [DY.Libsignal.Refinement.encodeField_eq, List.append_assoc] at hbs
  obtain ⟨hnum, _, hrest⟩ := paddedVarint_zero_append_inj _ _ _ _ _ hbs
  have hwn1 : x.wireType.toNat < 8 := by cases x.wireType <;> decide
  have hwn2 : wt.toNat < 8 := by cases wt <;> decide
  rw [← DY.TrWire.PbValue.wireType_toNat hwt] at hnum
  have htag : t' = tag := by omega
  have hwt_nat : wt.toNat = x.wireType.toNat := by omega
  have hwt_eq : wt = x.wireType := by
    have h1 := DY.Libsignal.Refinement.WireType.ofNat?_toNat wt
    have h2 := DY.Libsignal.Refinement.WireType.ofNat?_toNat x.wireType
    rw [hwt_nat, h2] at h1; exact Option.some.inj h1.symm
  exact ⟨htag, hwt_eq, hrest.symm⟩

private theorem mergeBytes_body_zero_inv {wt : CryptoVerification.LibsignalProtoCodec.WireType}
    {b v rest rest' : HwBytes}
    (hm : mergeBytes wt ((DY.TrWire.PbValue.bytes b).body 0 ++ rest) = some (v, rest')) :
    v = b ∧ rest' = rest := by
  obtain ⟨_, vp, hbs, _, _⟩ := mergeBytes_inv hm
  simp only [DY.TrWire.PbValue.body, List.append_assoc] at hbs
  obtain ⟨hlen, _, hbr⟩ := paddedVarint_zero_append_inj _ _ _ _ _ hbs
  obtain ⟨hvb, hrr⟩ := List.append_inj hbr hlen; exact ⟨hvb.symm, hrr.symm⟩

private theorem mergeUint32_body_zero_inv {wt : CryptoVerification.LibsignalProtoCodec.WireType}
    {n : Nat} {v : BitVec 32} {rest rest' : HwBytes}
    (hm : mergeUint32 wt ((DY.TrWire.PbValue.varint n).body 0 ++ rest) = some (v, rest')) :
    v = BitVec.ofNat 32 n ∧ rest' = rest := by
  obtain ⟨_, m, vp, hbs, rfl, _, _⟩ := mergeUint32_inv hm
  simp only [DY.TrWire.PbValue.body] at hbs
  obtain ⟨hnm, _, hrr⟩ := paddedVarint_zero_append_inj _ _ _ _ _ hbs
  rcases hnm with rfl; exact ⟨rfl, hrr.symm⟩

private theorem mergeField_body_zero_inv {m m' : ProtoSignalMessage} {tag : Nat}
    {x : DY.Libsignal.Refinement.PbValue} {rest rest' : HwBytes}
    (htag1 : 1 ≤ tag) (htag6 : tag ≤ 6) (hwt : WireTypeOk tag x)
    (hm : mergeField m tag x.wireType (x.body 0 ++ rest) = some (m', rest')) :
    m' = setField m tag x ∧ rest' = rest := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | t
  · omega
  · cases x with
    | bytes b =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmb, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeBytes_body_zero_inv hmb; exact ⟨rfl, rfl⟩
    | varint _ | unknown _ _ => simp [WireTypeOk] at hwt
  · cases x with
    | varint n =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmu, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeUint32_body_zero_inv hmu; exact ⟨rfl, rfl⟩
    | bytes _ | unknown _ _ => simp [WireTypeOk] at hwt
  · cases x with
    | varint n =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmu, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeUint32_body_zero_inv hmu; exact ⟨rfl, rfl⟩
    | bytes _ | unknown _ _ => simp [WireTypeOk] at hwt
  · cases x with
    | bytes b =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmb, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeBytes_body_zero_inv hmb; exact ⟨rfl, rfl⟩
    | varint _ | unknown _ _ => simp [WireTypeOk] at hwt
  · cases x with
    | bytes b =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmb, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeBytes_body_zero_inv hmb; exact ⟨rfl, rfl⟩
    | varint _ | unknown _ _ => simp [WireTypeOk] at hwt
  · cases x with
    | bytes b =>
      simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at hm
      obtain ⟨⟨v, r⟩, hmb, rfl, rfl⟩ := hm; obtain ⟨rfl, rfl⟩ := mergeBytes_body_zero_inv hmb; exact ⟨rfl, rfl⟩
    | varint _ | unknown _ _ => simp [WireTypeOk] at hwt
  · omega

private theorem decodeLoop_encodeField_zero_inv {fuel : Nat} {m r : ProtoSignalMessage}
    {tag : Nat} {x : DY.Libsignal.Refinement.PbValue} {rest : HwBytes}
    (htag1 : 1 ≤ tag) (htag6 : tag ≤ 6) (hwt : WireTypeOk tag x)
    (hd : decodeLoop fuel m (encodeField tag 0 0 x ++ rest) = some r) :
    ∃ fuel', fuel = fuel' + 1 ∧ decodeLoop fuel' (setField m tag x) rest = some r := by
  have hne : encodeField tag 0 0 x ++ rest ≠ [] := by
    rw [DY.Libsignal.Refinement.encodeField_eq, List.append_assoc]
    exact List.append_ne_nil_of_left_ne_nil (DY.Libsignal.Refinement.paddedVarint_ne_nil _ _) _
  obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
  cases fuel with
  | zero => rw [hbs] at hd; simp [decodeLoop] at hd
  | succ fuel' =>
    rw [hbs] at hd; simp only [decodeLoop] at hd; split at hd
    · cases hd
    · next t' wt rest0 hkey =>
      split at hd
      · cases hd
      · next m' rest' hmerge =>
        rw [← hbs] at hkey; obtain ⟨rfl, rfl, rfl⟩ := decodeKey_encodeField_zero_inv hwt hkey
        obtain ⟨rfl, rfl⟩ := mergeField_body_zero_inv htag1 htag6 hwt hmerge; exact ⟨fuel', rfl, hd⟩

private theorem trWireBytes_canonical_drop_one (addr pq : HwBytes) (f : WireFields) :
    (trWireBytes addr canonicalVariation f pq).drop 1 =
      encodeField 1 0 0 (.bytes (0x05#8 :: f.ratchetKey)) ++
      (encodeField 2 0 0 (.varint f.counter) ++
      (encodeField 3 0 0 (.varint f.previousCounter) ++
      (encodeField 4 0 0 (.bytes f.ciphertext) ++
      ((if pq = [] then [] else encodeField 5 0 0 (.bytes pq)) ++
       (if addr = [] then [] else encodeField 6 0 0 (.bytes addr)))))) := by
  rw [DY.Libsignal.Composed.Refinement.trWireBytes_canonical]
  simp [encodeWith, canonicalVariation, DY.TrWire.FieldItem.encode,
    DY.Libsignal.Refinement.knownValue?, List.append_assoc]

private theorem decode_trWireBytes_canonical_inv {addr pq : HwBytes} {f : WireFields}
    {p : ProtoSignalMessage}
    (hd : protoSignalCodec.decode ((trWireBytes addr canonicalVariation f pq).drop 1) = some p) :
    p.ratchetKey = some (0x05#8 :: f.ratchetKey) ∧
    p.counter = some (BitVec.ofNat 32 f.counter) ∧
    p.previousCounter = some (BitVec.ofNat 32 f.previousCounter) ∧
    p.ciphertext = some f.ciphertext ∧
    p.pqRatchet.getD [] = pq := by
  change decodeLoop ((trWireBytes addr canonicalVariation f pq).drop 1).length emptyProtoSignalMessage
    ((trWireBytes addr canonicalVariation f pq).drop 1) = some p at hd
  generalize ((trWireBytes addr canonicalVariation f pq).drop 1).length = fuel at hd
  rw [trWireBytes_canonical_drop_one] at hd
  obtain ⟨fuel1, _, hd1⟩ := decodeLoop_encodeField_zero_inv (by omega) (by omega)
    (by simp [WireTypeOk]) hd
  obtain ⟨fuel2, _, hd2⟩ := decodeLoop_encodeField_zero_inv (by omega) (by omega)
    (by simp [WireTypeOk]) hd1
  obtain ⟨fuel3, _, hd3⟩ := decodeLoop_encodeField_zero_inv (by omega) (by omega)
    (by simp [WireTypeOk]) hd2
  obtain ⟨fuel4, _, hd4⟩ := decodeLoop_encodeField_zero_inv (by omega) (by omega)
    (by simp [WireTypeOk]) hd3
  by_cases hpq : pq = [] <;> by_cases ha : addr = []
  · simp only [hpq, ha, ↓reduceIte, List.append_nil, decodeLoop, Option.some.injEq] at hd4
    subst hd4; exact ⟨rfl, rfl, rfl, rfl, hpq.symm⟩
  · simp only [hpq, ha, ↓reduceIte, List.nil_append] at hd4
    rw [← List.append_nil (encodeField 6 0 0 (.bytes addr))] at hd4
    obtain ⟨fuel6, _, hd6⟩ := decodeLoop_encodeField_zero_inv (by omega) (by omega)
      (by simp [WireTypeOk]) hd4
    simp only [decodeLoop, Option.some.injEq] at hd6; subst hd6; exact ⟨rfl, rfl, rfl, rfl, hpq.symm⟩
  · simp only [hpq, ha, ↓reduceIte, List.append_nil] at hd4
    rw [← List.append_nil (encodeField 5 0 0 (.bytes pq))] at hd4
    obtain ⟨fuel5, _, hd5⟩ := decodeLoop_encodeField_zero_inv (by omega) (by omega)
      (by simp [WireTypeOk]) hd4
    simp only [decodeLoop, Option.some.injEq] at hd5; subst hd5; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hpq, ha, ↓reduceIte] at hd4
    obtain ⟨fuel5, _, hd5⟩ := decodeLoop_encodeField_zero_inv (by omega) (by omega)
      (by simp [WireTypeOk]) hd4
    rw [← List.append_nil (encodeField 6 0 0 (.bytes addr))] at hd5
    obtain ⟨fuel6, _, hd6⟩ := decodeLoop_encodeField_zero_inv (by omega) (by omega)
      (by simp [WireTypeOk]) hd5
    simp only [decodeLoop, Option.some.injEq] at hd6; subst hd6; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem tryFrom_ok_pqRatchet {b : HwBytes} {m : SignalMessage}
    (h : SignalMessage.tryFrom protoSignalCodec b = .ok m) :
    ∃ p, protoSignalCodec.decode ((b.take (b.length - macLength)).drop 1) = some p ∧
      m.pqRatchet = p.pqRatchet.getD [] := by
  unfold SignalMessage.tryFrom at h; dsimp only at h; generalize b.headD 0 >>> 4 = ver at h
  by_cases h1 : b.length < macLength + 1
  · simp only [h1, ↓reduceIte] at h; cases h
  by_cases h2 : ver < CryptoGames.LibsignalSession.preKyberVersion
  · simp only [h1, h2, ↓reduceIte] at h; cases h
  by_cases h3 : CryptoGames.LibsignalSession.currentVersion < ver
  · simp only [h1, h2, h3, ↓reduceIte] at h; cases h
  simp only [h1, h2, h3, ↓reduceIte] at h
  rcases hd : protoSignalCodec.decode ((b.take (b.length - macLength)).drop 1) with _ | p
  · rw [hd] at h; simp at h
  · rw [hd] at h
    cases hrk : p.ratchetKey with
    | none => simp [hrk] at h
    | some rk =>
      cases hk : CryptoGames.LibsignalSession.PublicKey.deserialize rk with
      | error e => simp [hrk, hk, bind, Except.bind] at h
      | ok k =>
        cases hc : p.counter with
        | none => simp [hrk, hk, hc, bind, Except.bind] at h
        | some c =>
          cases hct : p.ciphertext with
          | none => simp [hrk, hk, hc, hct, bind, Except.bind] at h
          | some ct => simp [hrk, hk, hc, hct] at h; subst h; exact ⟨p, rfl, rfl⟩

theorem encMsg_tryFrom_inv {interp : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {coins pq pt : Bytes} {b : HwBytes} {m : SignalMessage}
    (hb : gamma interp S g (encMsg st coins pq pt) = b)
    (hrk_len : (gamma interp S g (dhPk st.dhs)).length = 32)
    (htry : SignalMessage.tryFrom protoSignalCodec b = .ok m) :
    let msg := encSig st coins pq pt
    gamma interp S g msg.wire = b.take (b.length - 8) ∧
    gamma interp S g msg.mac = b.drop (b.length - 8) ∧
    gamma interp S g msg.ciphertext = m.ciphertext ∧
    gamma interp S g msg.ratchetKey = m.senderRatchetKey.bytes.toList ∧
    gamma interp S g msg.pqRatchet = m.pqRatchet ∧
    msg.counter.toNat = m.counter.toNat ∧
    msg.version.toNat = m.messageVersion.toNat := by
  intro msg
  have hcat : b = gamma interp S g msg.wire ++ gamma interp S g msg.mac := by
    rw [← hb]; unfold encMsg; exact gamma_concat interp S g msg.wire msg.mac
  have hmac_len : (gamma interp S g msg.mac).length = 8 := by
    dsimp only [msg, encSig]
    exact length_gamma_computeMac interp S g _ _ _ _
  have htake : b.take (b.length - 8) = gamma interp S g msg.wire := by
    rw [hcat, List.length_append, hmac_len, Nat.add_sub_cancel, List.take_left' rfl]
  have hdrop : b.drop (b.length - 8) = gamma interp S g msg.mac := by
    rw [hcat, List.length_append, hmac_len, Nat.add_sub_cancel, List.drop_left' rfl]
  let f : WireFields :=
    { version := 4, ratchetKey := gamma interp S g (dhPk st.dhs),
      counter := st.ns.toNat, previousCounter := st.pn.toNat,
      ciphertext := gamma interp S g msg.ciphertext }
  have hwire : gamma interp S g msg.wire =
      trWireBytes (g.addr msg.wire) canonicalVariation f (gamma interp S g msg.pqRatchet) := by
    dsimp only [msg, encSig, f]
    exact gamma_trHonestWireMsgE interp S g (dhPk st.dhs) st.ns st.pn msg.ciphertext msg.pqRatchet
  obtain ⟨_, hver_b, _, _, p, rk, hdec, hrk_p, hdeser, hctr_p, hct_p, _⟩ := tryFrom_ok_inv htry
  obtain ⟨p', hdec', hpq_m⟩ := tryFrom_ok_pqRatchet htry
  have hml : macLength = 8 := rfl
  rw [hml, htake, hwire] at hdec hdec'
  have hp_eq : p' = p := Option.some.inj (hdec'.symm.trans hdec)
  subst hp_eq
  obtain ⟨hrk_f, hctr_f, _, hct_f, hpq_f⟩ := decode_trWireBytes_canonical_inv hdec
  have hrk_val : rk = 0x05#8 :: f.ratchetKey := Option.some.inj (hrk_p.symm.trans hrk_f)
  rw [hrk_val] at hdeser
  obtain ⟨rest, hcons, _, hbytes_eq⟩ := deserialize_inv hdeser
  injection hcons with _ hrest
  subst hrest
  have hrk_res : gamma interp S g msg.ratchetKey = m.senderRatchetKey.bytes.toList := by
    rw [hbytes_eq]
    dsimp only [msg, encSig, f]
    exact (List.take_of_length_le (Nat.le_of_eq hrk_len)).symm
  have hct_res : gamma interp S g msg.ciphertext = m.ciphertext :=
    (Option.some.inj (hct_p.symm.trans hct_f)).symm
  have hpq_res : gamma interp S g msg.pqRatchet = m.pqRatchet :=
    (hpq_m.trans hpq_f).symm
  have hctr_res : msg.counter.toNat = m.counter.toNat := by
    have hc_eq : m.counter = BitVec.ofNat 32 st.ns.toNat :=
      Option.some.inj (hctr_p.symm.trans hctr_f)
    dsimp only [msg, encSig]
    rw [hc_eq, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt st.ns.toBitVec.isLt).symm
  have hver_res : msg.version.toNat = m.messageVersion.toNat := by
    have hhead : b.headD 0 = BitVec.ofNat 8 (4 * 16 + canonicalVariation.versionLowNibble % 16) := by
      rw [hcat, hwire, DY.Libsignal.Composed.Refinement.trWireBytes_canonical]
      simp [encodeWith, f]
    rw [hver_b, hhead]
    dsimp only [msg, encSig, messageVersion, canonicalVariation]
    decide
  exact ⟨htake.symm, hdrop.symm, hct_res, hrk_res, hpq_res, hctr_res, hver_res⟩

theorem encMsg_mem_recvRepresentationsOn {interp : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {st : TRState} {coins pq pt : Bytes} {b : HwBytes}
    (hak : (encMsg st coins pq pt).AttackerKnows tr)
    (hb : gamma interp S g (encMsg st coins pq pt) = b)
    (hrk_len : (gamma interp S g (dhPk st.dhs)).length = 32) :
    encMsg st coins pq pt ∈ recvRepresentationsOn interp S g tr b := by
  have hparse := parse_encMsg st coins pq pt
  let msg := encSig st coins pq pt
  have hcat : b = gamma interp S g msg.wire ++ gamma interp S g msg.mac := by
    rw [← hb]; unfold encMsg; exact gamma_concat interp S g msg.wire msg.mac
  have hmac_len : (gamma interp S g msg.mac).length = 8 :=
    length_gamma_computeMac interp S g _ _ _ _
  have htake : gamma interp S g msg.wire = b.take (b.length - 8) := by
    rw [hcat, List.length_append, hmac_len, Nat.add_sub_cancel, List.take_left' rfl]
  have hdrop : gamma interp S g msg.mac = b.drop (b.length - 8) := by
    rw [hcat, List.length_append, hmac_len, Nat.add_sub_cancel, List.drop_left' rfl]
  refine ⟨hak, hb, by rw [hparse]; rfl, ?_⟩
  intro msg' hparse'
  rw [hparse] at hparse'
  injection hparse' with hmsg'
  subst hmsg'
  refine ⟨htake, hdrop, spqrHeaded_computeMac_false _ _ _ _, ?_⟩
  intro m htry
  obtain ⟨_, _, hct, hrk, hpq, hctr, hver⟩ := encMsg_tryFrom_inv hb hrk_len htry
  exact ⟨hct, hrk, hpq, hctr, hver⟩

theorem encMsg_faithfulInner {interp : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {coins pq pt : Bytes} {p : PreKeyFields}
    (hb : gamma interp S g (encMsg st coins pq pt) = p.message)
    (hrk_len : (gamma interp S g (dhPk st.dhs)).length = 32)
    (htry : SignalMessage.tryFrom protoSignalCodec p.message = .ok p.inner) :
    FaithfulInner interp S g (encMsg st coins pq pt) p := by
  obtain ⟨hw, hm, hct, hrk, hpq, hctr, hver⟩ := encMsg_tryFrom_inv hb hrk_len htry
  exact ⟨encSig st coins pq pt, parse_encMsg st coins pq pt,
    hw, hm, spqrHeaded_computeMac_false _ _ _ _, hct, hrk, hpq, hctr, hver⟩

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep
