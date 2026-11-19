/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerDispatch
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Prost.EncodeToVec

/-! ## 1. Relocation and Decomposition Helpers for `0x317fc..0x31918` -/

/-- Framed `memcpy` call rule for an explicit byte slice `src ↦ₛ bs`. -/
private theorem call_memcpy_bytes_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {bs : List (BitVec 8)} {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs)) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VRegsAt s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      SepWP prog target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionSpec]; rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace)
      ⟨hcs_sf.2.2.2.2.2.2.2.2.2.2.2⟩
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1

/-- Framed `memcpy` call rule for any `States.Leaves.Relocatable n F` predicate family. -/
private theorem call_memcpy_relocate_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {n : Nat} {F : BitVec 64 → SepProp}
    (hrel : States.Leaves.Relocatable n F)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VRegsAt s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (hrel src))) ?_
  wp_pull_exists; rename_i bs
  wp_focus_pure; intro hlen
  refine call_memcpy_bytes_bridge2 hcall dst src hlen hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
    (Frame := States.Leaves.relocatedHeap F bs ∗ Frame) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28
  have hrecomp := States.Leaves.relocatedHeap_recompose F bs dst
  have hsrc : (src ↦ₛ bs) ⊢ memRegion src n := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion src bs
  refine SepWP.weaken_pre ?_
    (hnext sf hpc_sf hrun_sf hsp_sf htr_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28)
  refine Entails.trans (Entails.of_eq (show
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (States.Leaves.relocatedHeap F bs ∗ Frame) =
    (((dst ↦ₛ bs) ∗ States.Leaves.relocatedHeap F bs) ∗ (src ↦ₛ bs)) ∗ Frame by ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono hrecomp hsrc)

/-! ## 2. `chunkedStatesAt` Relocation (`0x31810..0x3184c`) -/

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedKeysUnsampledAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    Relocatable 56 (fun a => chunkedKeysUnsampledAt A a st) := by
  refine Relocatable.congr rfl (fun a => ?_)
    (Relocatable.of_unchunkedCt2SentAt A { epoch := st.uc.epoch, auth := st.uc.auth })
  rfl

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedKeysSampledAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedKeysSampledAt A a st) := by
  refine Relocatable.congr rfl (fun a => (chunkedKeysSampledAt_eq_ct1ReceivedAt A a st).symm)
    (Relocatable.of_chunkedCt1ReceivedAt A (chunkedKeysSampledToCt1Received st))

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedEkSentCt1ReceivedAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedEkSentCt1ReceivedAt A a st) :=
  Relocatable.sepConj (off := 104#64) (m := 504) rfl rfl
    (Relocatable.of_unchunkedEkSentCt1ReceivedAt A st.uc)
    (Relocatable.of_polyDecoderAt A st.receiving_ct2)

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedNoHeaderReceivedAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Relocatable 456 (fun a => chunkedNoHeaderReceivedAt A a st) :=
  Relocatable.sepConj (off := 56#64) (m := 456) rfl rfl
    (Relocatable.of_unchunkedCt2SentAt A { epoch := st.uc.epoch, auth := st.uc.auth })
    (Relocatable.of_polyDecoderAt A st.receiving_hdr)

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedHeaderReceivedAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Relocatable 480 (fun a => chunkedHeaderReceivedAt A a st) :=
  Relocatable.sepConj (off := 80#64) (m := 480) rfl rfl
    (Relocatable.of_unchunkedEkSentAt A { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.hdr })
    (Relocatable.of_polyDecoderAt A st.receiving_ek)

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedCt1AcknowledgedAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    Relocatable 528 (fun a => chunkedCt1AcknowledgedAt A a st) :=
  Relocatable.sepConj (off := 128#64) (m := 528) rfl rfl
    (Relocatable.of_unchunkedCt1SentAt A st.uc)
    (Relocatable.of_polyDecoderAt A st.receiving_ek)

open CryptoVerification.SpqrV1.States.Leaves in
theorem Relocatable.of_chunkedStatesAt (A : RustAlloc) {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) :
    Relocatable 928 (fun a => chunkedStatesAt A a st) := by
  cases st with
  | keysUnsampled s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 56#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 2#64)
        (Relocatable.sepConj (off := 56#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedKeysUnsampledAt_b2 A s) (Relocatable.of_memRegion 864)))
  | keysSampled s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 504#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 3#64)
        (Relocatable.sepConj (off := 504#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedKeysSampledAt_b2 A s) (Relocatable.of_memRegion 416)))
  | headerSent s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 880#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 4#64)
        (Relocatable.sepConj (off := 880#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedHeaderSentAt A s) (Relocatable.of_memRegion 40)))
  | ct1Received s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 504#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 5#64)
        (Relocatable.sepConj (off := 504#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedCt1ReceivedAt A s) (Relocatable.of_memRegion 416)))
  | ekSentCt1Received s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 504#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 6#64)
        (Relocatable.sepConj (off := 504#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedEkSentCt1ReceivedAt_b2 A s) (Relocatable.of_memRegion 416)))
  | noHeaderReceived s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 456#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 7#64)
        (Relocatable.sepConj (off := 456#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedNoHeaderReceivedAt_b2 A s) (Relocatable.of_memRegion 464)))
  | headerReceived s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 480#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 8#64)
        (Relocatable.sepConj (off := 480#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedHeaderReceivedAt_b2 A s) (Relocatable.of_memRegion 440)))
  | ct1Sampled s => exact Relocatable.of_chunkedCt1SampledAt A s
  | ekReceivedCt1Sampled s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 528#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 10#64)
        (Relocatable.sepConj (off := 528#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedEkReceivedCt1SampledAt A s) (Relocatable.of_memRegion 392)))
  | ct1Acknowledged s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 528#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 11#64)
        (Relocatable.sepConj (off := 528#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedCt1AcknowledgedAt_b2 A s) (Relocatable.of_memRegion 392)))
  | ct2Sampled s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 456#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 12#64)
        (Relocatable.sepConj (off := 456#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedCt2SampledAt A s) (Relocatable.of_memRegion 464)))

/-! ## 3. `outWords28` Relocation Bridge for `optProtoInnerStateAt` / `v1StatePBPinnedAt` (`0x3185c`) -/

theorem states_into_pb_innerState_isSome {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) :
    ∃ is : V1State.InnerState, st.into_pb.innerState = some is := by
  cases st <;> exact ⟨_, rfl⟩

theorem quads28At_eq_outWords28 (a : BitVec 64)
    (i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 : BitVec 64) :
    DecodeState.quads28At a
      (((i0, i8, i16, i24, i32, i40, i48), (i56, i64, i72, i80, i88, i96, i104)),
       ((i112, i120, i128, i136, i144, i152, i160), (i168, i176, i184, i192, i200, i208, i216))) =
    outWords28 a i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 := by
  dsimp only [DecodeState.quads28At, DecodeState.quads14At, DecodeState.quads7At, outWords28]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

/-- Address-independent heap resource for `V1State.InnerState` while its 28 stack words are
    unpacked as `outWords28 a i0 ... i216`. -/
@[expose] def protoInnerWordsHeap (A : RustAlloc) (is : V1State.InnerState)
    (i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 : BitVec 64) : SepProp :=
  let q : DecodeState.Quads28 :=
    (((i0, i8, i16, i24, i32, i40, i48), (i56, i64, i72, i80, i88, i96, i104)),
     ((i112, i120, i128, i136, i144, i152, i160), (i168, i176, i184, i192, i200, i208, i216)))
  ⌜q.head ≠ DecodeState.none3Cap⌝ ∗ DecodeState.canonicalV1InnerHeap A q is

theorem optProtoInnerStateAt_some_entails_outWords28 (A : RustAlloc) (a : BitVec 64)
    (is : V1State.InnerState) :
    optProtoInnerStateAt A a (some is) ⊢
      ∃∗ i0 : BitVec 64, ∃∗ i8 : BitVec 64, ∃∗ i16 : BitVec 64, ∃∗ i24 : BitVec 64,
      ∃∗ i32 : BitVec 64, ∃∗ i40 : BitVec 64, ∃∗ i48 : BitVec 64, ∃∗ i56 : BitVec 64,
      ∃∗ i64 : BitVec 64, ∃∗ i72 : BitVec 64, ∃∗ i80 : BitVec 64, ∃∗ i88 : BitVec 64,
      ∃∗ i96 : BitVec 64, ∃∗ i104 : BitVec 64, ∃∗ i112 : BitVec 64, ∃∗ i120 : BitVec 64,
      ∃∗ i128 : BitVec 64, ∃∗ i136 : BitVec 64, ∃∗ i144 : BitVec 64, ∃∗ i152 : BitVec 64,
      ∃∗ i160 : BitVec 64, ∃∗ i168 : BitVec 64, ∃∗ i176 : BitVec 64, ∃∗ i184 : BitVec 64,
      ∃∗ i192 : BitVec 64, ∃∗ i200 : BitVec 64, ∃∗ i208 : BitVec 64, ∃∗ i216 : BitVec 64,
        outWords28 a i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
          i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ∗
        protoInnerWordsHeap A is i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
          i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 := by
  refine Entails.trans (DecodeState.of_drop_inner_canonical A a (some is)) ?_
  unfold DecodeState.optProtoInnerStateAt; apply Entails.sepExists_elim
  rintro ⟨⟨⟨i0, i8, i16, i24, i32, i40, i48⟩, ⟨i56, i64, i72, i80, i88, i96, i104⟩⟩,
          ⟨⟨i112, i120, i128, i136, i144, i152, i160⟩, ⟨i168, i176, i184, i192, i200, i208, i216⟩⟩⟩
  refine Entails.sepExists_right i0 (Entails.sepExists_right i8 (Entails.sepExists_right i16
    (Entails.sepExists_right i24 (Entails.sepExists_right i32 (Entails.sepExists_right i40
    (Entails.sepExists_right i48 (Entails.sepExists_right i56 (Entails.sepExists_right i64
    (Entails.sepExists_right i72 (Entails.sepExists_right i80 (Entails.sepExists_right i88
    (Entails.sepExists_right i96 (Entails.sepExists_right i104 (Entails.sepExists_right i112
    (Entails.sepExists_right i120 (Entails.sepExists_right i128 (Entails.sepExists_right i136
    (Entails.sepExists_right i144 (Entails.sepExists_right i152 (Entails.sepExists_right i160
    (Entails.sepExists_right i168 (Entails.sepExists_right i176 (Entails.sepExists_right i184
    (Entails.sepExists_right i192 (Entails.sepExists_right i200 (Entails.sepExists_right i208
    (Entails.sepExists_right i216 ?_)))))))))))))))))))))))))))
  rw [quads28At_eq_outWords28]; dsimp only [protoInnerWordsHeap]; exact Entails.of_eq (by ac_rfl)

theorem outWords28_entails_v1StatePBPinnedAt (A : RustAlloc) (a : BitVec 64)
    (v1 : V1State) (is : V1State.InnerState) (his : v1.innerState = some is)
    (i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 : BitVec 64) :
    outWords28 a i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ∗
    protoInnerWordsHeap A is i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ⊢
    ∃∗ g_v1 : CryptoVerification.SpqrV1.ProtoRepr.V1StatePBGhost,
      Prost.EncodeToVec.optPqRatchetInnerPBPinnedAt A g_v1 a (some (.v1 v1)) := by
  change _ ⊢ ∃∗ g_v1 : CryptoVerification.SpqrV1.ProtoRepr.V1StatePBGhost,
    CryptoVerification.SpqrV1.ProtoRepr.v1StatePBPinnedAt A g_v1 a v1
  rw [← CryptoVerification.SpqrV1.ProtoRepr.v1StatePBAt_eq_exists_pinned,
      v1StatePBAt_eq_optProtoInnerStateAt, his]
  refine Entails.trans ?_ (DecodeState.optProtoInnerStateAt_canonical_entails_drop A a (some is))
  unfold DecodeState.optProtoInnerStateAt; dsimp only [protoInnerWordsHeap]
  refine Entails.sepExists_right
    (((i0, i8, i16, i24, i32, i40, i48), (i56, i64, i72, i80, i88, i96, i104)),
     ((i112, i120, i128, i136, i144, i152, i160), (i168, i176, i184, i192, i200, i208, i216))) ?_
  rw [quads28At_eq_outWords28]; exact Entails.of_eq (by ac_rfl)

/-! ## 4. Relocating `VersionNegotiationPB`, `ChainPB`, and `V1State` into `PqRatchetState` -/

@[expose] def optVersionNegWordsHeap (A : RustAlloc)
    (g : CryptoVerification.SpqrV1.ProtoRepr.VersionNegotiationPBGhost)
    (opt : Option VersionNegotiationPB) (w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  match opt with
  | none => emp
  | some vn =>
    ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
      vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
    ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey

theorem optVersionNegotiationPBPinnedAt_entails_vnWords6 (A : RustAlloc)
    (g : CryptoVerification.SpqrV1.ProtoRepr.VersionNegotiationPBGhost) (a : BitVec 64)
    (opt : Option VersionNegotiationPB) :
    CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBPinnedAt A g a opt ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        vnWords6At a (Prost.EncodeToVec.optVersionNegCap g opt) w1 w2 w3 w4 w5 ∗
        optVersionNegWordsHeap A g opt w1 w2 w3 w4 w5 := by
  rw [Prost.EncodeToVec.optVersionNegotiationPBPinnedAt_eq]
  refine Entails.trans (sepConj_mono_right (optVersionNegRest_entails_words5 A g a opt)) ?_
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w4
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w5
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5 ?_))))
  unfold vnWords6At optVersionNegWordsHeap; exact Entails.of_eq (by ac_rfl)

theorem vnWords6_entails_optVersionNegotiationPBPinnedAt (A : RustAlloc)
    (g : CryptoVerification.SpqrV1.ProtoRepr.VersionNegotiationPBGhost) (a : BitVec 64)
    (opt : Option VersionNegotiationPB) (w1 w2 w3 w4 w5 : BitVec 64) :
    vnWords6At a (Prost.EncodeToVec.optVersionNegCap g opt) w1 w2 w3 w4 w5 ∗
      optVersionNegWordsHeap A g opt w1 w2 w3 w4 w5 ⊢
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBPinnedAt A g a opt := by
  rw [Prost.EncodeToVec.optVersionNegotiationPBPinnedAt_eq]; unfold vnWords6At optVersionNegWordsHeap
  refine Entails.trans (Entails.of_eq (show
    ((a ↦₆₄ Prost.EncodeToVec.optVersionNegCap g opt) ∗
      ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
      (match opt with
       | none => emp
       | some vn =>
         ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
           vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
         ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) =
    (a ↦₆₄ Prost.EncodeToVec.optVersionNegCap g opt) ∗
      (((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
       (match opt with
        | none => emp
        | some vn =>
          ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
            vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey)) by ac_rfl)) ?_
  exact sepConj_mono_right (words5_entails_optVersionNegRest A g a opt w1 w2 w3 w4 w5)

@[expose] def optChainWordsHeap (A : RustAlloc) (g : ChainFrom.ChainPBGhost) (x25 : BitVec 64)
    (opt : Option ChainPB) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) : SepProp :=
  match opt with
  | none => ⌜x25 = noneCap⌝
  | some pb =>
    ⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap ∧ c1 = g.linksPtr ∧
      c2 = BitVec.ofNat 64 (g.epochs.zip pb.links).length ∧ c3 = g.nextRoot.cap ∧
      c4 = g.nextRoot.ptr ∧ c5 = BitVec.ofNat 64 pb.nextRoot.length ∧
      c6 = pb.currentEpoch ∧ c7 = pb.sendEpoch ∧ chainPBParamsDirWords pb c8 c9⌝ ∗
    chainPBHeapAt A g pb

theorem optChainPBRegSlotAt_entails_chainWords9 (A : RustAlloc) (a_slot : BitVec 64)
    (x25 : BitVec 64) (opt : Option ChainPB) :
    optChainPBRegSlotAt A a_slot x25 opt ⊢
      ∃∗ g : ChainFrom.ChainPBGhost,
      ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64,
      ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        chainWords9At a_slot c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
        optChainWordsHeap A g x25 opt c1 c2 c3 c4 c5 c6 c7 c8 c9 := by
  cases opt with
  | none =>
    unfold optChainPBRegSlotAt optChainWordsHeap
    apply Entails.pure_left; intro hx25; rw [memRegion_72_words9 a_slot]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro c9; apply Entails.sepExists_elim; intro c8
    apply Entails.sepExists_elim; intro c7; apply Entails.sepExists_elim; intro c6
    apply Entails.sepExists_elim; intro c5; apply Entails.sepExists_elim; intro c4
    apply Entails.sepExists_elim; intro c3; apply Entails.sepExists_elim; intro c2
    apply Entails.sepExists_elim; intro c1
    refine Entails.sepExists_right
      ({ linksCap := 0#64, linksPtr := 0#64, epochs := [], nextRoot := ⟨0#64, 0#64⟩ } :
        ChainFrom.ChainPBGhost)
      (Entails.sepExists_right c1 (Entails.sepExists_right c2 (Entails.sepExists_right c3
      (Entails.sepExists_right c4 (Entails.sepExists_right c5 (Entails.sepExists_right c6
      (Entails.sepExists_right c7 (Entails.sepExists_right c8 (Entails.sepExists_right c9 ?_)))))))))
    unfold chainWords9At
    exact Entails.trans (Entails.pure_right hx25 (Entails.of_eq (by ac_rfl))) (Entails.of_eq (by ac_rfl))
  | some pb =>
    unfold optChainPBRegSlotAt optChainWordsHeap
    apply Entails.sepExists_elim; intro g; apply Entails.pure_left; rintro ⟨hx25, hne⟩
    refine Entails.trans (chainPBRestAt_entails_words9 A g (a_slot - 8#64) pb) ?_
    apply Entails.sepExists_elim; intro c8; apply Entails.sepExists_elim; intro c9
    apply Entails.pure_left; intro hparams
    refine Entails.sepExists_right g (Entails.sepExists_right g.linksPtr
      (Entails.sepExists_right (BitVec.ofNat 64 (g.epochs.zip pb.links).length)
      (Entails.sepExists_right g.nextRoot.cap (Entails.sepExists_right g.nextRoot.ptr
      (Entails.sepExists_right (BitVec.ofNat 64 pb.nextRoot.length)
      (Entails.sepExists_right pb.currentEpoch (Entails.sepExists_right pb.sendEpoch
      (Entails.sepExists_right c8 (Entails.sepExists_right c9 ?_)))))))))
    unfold chainWords9At
    have ha0 : a_slot - 8#64 + 8#64 = a_slot := by bv_omega
    have ha8 : a_slot - 8#64 + 16#64 = a_slot + 8#64 := by bv_omega
    have ha16 : a_slot - 8#64 + 24#64 = a_slot + 16#64 := by bv_omega
    have ha24 : a_slot - 8#64 + 32#64 = a_slot + 24#64 := by bv_omega
    have ha32 : a_slot - 8#64 + 40#64 = a_slot + 32#64 := by bv_omega
    have ha40 : a_slot - 8#64 + 48#64 = a_slot + 40#64 := by bv_omega
    have ha48 : a_slot - 8#64 + 56#64 = a_slot + 48#64 := by bv_omega
    have ha56 : a_slot - 8#64 + 64#64 = a_slot + 56#64 := by bv_omega
    have ha64 : a_slot - 8#64 + 72#64 = a_slot + 64#64 := by bv_omega
    rw [ha0, ha8, ha16, ha24, ha32, ha40, ha48, ha56, ha64]
    refine Entails.trans (Entails.of_eq (show
      (a_slot ↦₆₄ g.linksPtr) ∗ ((a_slot + 8#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        ((a_slot + 16#64) ↦₆₄ g.nextRoot.cap) ∗ ((a_slot + 24#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a_slot + 32#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        ((a_slot + 40#64) ↦₆₄ pb.currentEpoch) ∗ ((a_slot + 48#64) ↦₆₄ pb.sendEpoch) ∗
        ((a_slot + 56#64) ↦₆₄ c8) ∗ ((a_slot + 64#64) ↦₆₄ c9) ∗ chainPBHeapAt A g pb =
      chainWords9At a_slot g.linksPtr (BitVec.ofNat 64 (g.epochs.zip pb.links).length)
        g.nextRoot.cap g.nextRoot.ptr (BitVec.ofNat 64 pb.nextRoot.length)
        pb.currentEpoch pb.sendEpoch c8 c9 ∗ chainPBHeapAt A g pb by unfold chainWords9At; ac_rfl)) ?_
    exact sepConj_mono_right
      (Entails.pure_right ⟨hx25, hne, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hparams⟩ (Entails.refl _))

theorem chainWords9_entails_optChainPBPinnedAt (A : RustAlloc)
    (g : ChainFrom.ChainPBGhost) (a x25 : BitVec 64)
    (opt : Option ChainPB) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) :
    (a ↦₆₄ x25) ∗
      chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
      optChainWordsHeap A g x25 opt c1 c2 c3 c4 c5 c6 c7 c8 c9 ⊢
      CryptoVerification.SpqrV1.ProtoRepr.optChainPBPinnedAt A g.toProtoRepr a opt := by
  refine Entails.trans ?_ (ChainFrom.optChainPBAt_entails_protoRepr_pinned A g a opt)
  cases opt with
  | none =>
    unfold optChainWordsHeap ChainFrom.optChainPBAt
    refine Entails.trans (Entails.of_eq (show
      (a ↦₆₄ x25) ∗ chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗ ⌜x25 = noneCap⌝ =
      ⌜x25 = noneCap⌝ ∗ ((a ↦₆₄ x25) ∗ chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9) by ac_rfl)) ?_
    apply Entails.pure_left; rintro rfl
    exact sepConj_mono_right (chainWords9_to_memRegion_72 (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9)
  | some pb =>
    unfold optChainWordsHeap ChainFrom.optChainPBAt
    refine Entails.trans (Entails.of_eq (show
      (a ↦₆₄ x25) ∗ chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
        (⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap ∧ c1 = g.linksPtr ∧
          c2 = BitVec.ofNat 64 (g.epochs.zip pb.links).length ∧ c3 = g.nextRoot.cap ∧
          c4 = g.nextRoot.ptr ∧ c5 = BitVec.ofNat 64 pb.nextRoot.length ∧
          c6 = pb.currentEpoch ∧ c7 = pb.sendEpoch ∧ chainPBParamsDirWords pb c8 c9⌝ ∗ chainPBHeapAt A g pb) =
      ⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap ∧ c1 = g.linksPtr ∧
        c2 = BitVec.ofNat 64 (g.epochs.zip pb.links).length ∧ c3 = g.nextRoot.cap ∧
        c4 = g.nextRoot.ptr ∧ c5 = BitVec.ofNat 64 pb.nextRoot.length ∧
        c6 = pb.currentEpoch ∧ c7 = pb.sendEpoch ∧ chainPBParamsDirWords pb c8 c9⌝ ∗
        ((a ↦₆₄ x25) ∗ (chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗ chainPBHeapAt A g pb)) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hparams⟩
    refine Entails.trans ?_ (ChainFrom.ChainFromNorm.chainPBAt_unexpose_cap A g a pb)
    refine sepConj_mono_right ?_; unfold chainWords9At
    have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
    have ha24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
    have ha32 : a + 8#64 + 24#64 = a + 32#64 := by bv_omega
    have ha40 : a + 8#64 + 32#64 = a + 40#64 := by bv_omega
    have ha48 : a + 8#64 + 40#64 = a + 48#64 := by bv_omega
    have ha56 : a + 8#64 + 48#64 = a + 56#64 := by bv_omega
    have ha64 : a + 8#64 + 56#64 = a + 64#64 := by bv_omega
    have ha72 : a + 8#64 + 64#64 = a + 72#64 := by bv_omega
    rw [ha16, ha24, ha32, ha40, ha48, ha56, ha64, ha72]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (words9_entails_chainPBRestAt A g a pb c8 c9 hparams)

theorem memRegion_928_split_352_576 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 928 =
      memRegion (sp + 0x1260#64) 352 ∗ memRegion (sp + 5056#64) 576 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 352) (k := 576)
    (b' := sp + 5056#64) rfl (by bv_omega) (by decide)

theorem memRegion_224_split_24_200 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 224 =
      memRegion (sp + 1424#64) 24 ∗ memRegion (sp + 1448#64) 200 := by
  have h1424 : sp + 0x590#64 = sp + 1424#64 := rfl
  rw [h1424]
  exact ProofLib.memRegion_split' (b := sp + 1424#64) (n := 24) (k := 200)
    (b' := sp + 1448#64) rfl (by bv_omega) (by decide)

theorem chunkAt_entails_memRegion_34 (a : BitVec 64) (c : Chunk) :
    Poly.chunkAt a c ⊢ memRegion a 34 := by
  unfold Poly.chunkAt
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 2) (b' := a + 32#64)
        rfl (by bv_omega) (by decide)]
  have hdata : (a ↦ₛ c.data.toList) ⊢ memRegion a 32 := by
    have h := ProofLib.pointsToBytes_entails_memRegion a c.data.1
    rwa [c.data.2] at h
  exact sepConj_mono hdata (ProofLib.pointsTo16_entails_memRegion (a + 32#64) c.index)

theorem messagePayloadAt_entails_memRegion_40 (a : BitVec 64) (p : MessagePayload spqrPolyApi) :
    messagePayloadAt spqrPolyApi a p ⊢ memRegion (a + 8#64) 40 := by
  have h1_39 : ∀ tag : BitVec 8,
      ((a + 0x08#64) ↦₈ tag) ∗ memRegion (a + 0x09#64) 39 ⊢ memRegion (a + 8#64) 40 := by
    intro tag
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 39) (b' := a + 0x09#64)
          rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (a + 8#64) tag)
  have hchunk_case : ∀ (tag : BitVec 8) (c : Chunk),
      ((a + 0x08#64) ↦₈ tag) ∗ memRegion (a + 0x09#64) 1 ∗
        Poly.chunkAt (a + 0x0a#64) c ∗ memRegion (a + 0x2c#64) 4 ⊢ memRegion (a + 8#64) 40 := by
    intro tag c
    refine Entails.trans ?_ (h1_39 tag)
    refine sepConj_mono_right ?_
    rw [ProofLib.memRegion_split' (b := a + 0x09#64) (n := 1) (k := 38) (b' := a + 0x0a#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 0x0a#64) (n := 34) (k := 4) (b' := a + 0x2c#64)
          rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (chunkAt_entails_memRegion_34 (a + 0x0a#64) c))
  cases p with
  | none =>
    dsimp only [messagePayloadAt]
    exact h1_39 0#8
  | hdr c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 1#8 _
  | ek c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 2#8 _
  | ekCt1Ack c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 3#8 _
  | ct1Ack b =>
    dsimp only [messagePayloadAt]
    refine Entails.trans ?_ (h1_39 4#8)
    refine sepConj_mono_right ?_
    rw [ProofLib.memRegion_split' (b := a + 0x09#64) (n := 1) (k := 38) (b' := a + 0x0a#64)
          rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (a + 0x09#64) _)
  | ct1 c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 5#8 _
  | ct2 c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 6#8 _

theorem messageAt_entails_memRegion_48 (a : BitVec 64) (m : Message spqrPolyApi) :
    messageAt spqrPolyApi a m ⊢ memRegion a 48 := by
  unfold messageAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a m.epoch)
    (messagePayloadAt_entails_memRegion_40 a m.payload)

theorem vecU8At_entails_vecU8 (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ vecU8 A v bs := by
  unfold vecU8
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem optVersionNegWordsHeap_some_cap_ne (A : RustAlloc)
    (g : ProtoRepr.VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (w1 w2 w3 w4 w5 : BitVec 64) :
    optVersionNegWordsHeap A g (some vn) w1 w2 w3 w4 w5 ⊢
      ⌜(Prost.EncodeToVec.optVersionNegCap g (some vn) + 1#64 == 0#64) = false⌝ ∗
      optVersionNegWordsHeap A g (some vn) w1 w2 w3 w4 w5 := by
  unfold optVersionNegWordsHeap ProtoRepr.EncodedLen.vecU8Buf
  rw [← sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hw1, hw2, hw345⟩
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  have hne : (Prost.EncodeToVec.optVersionNegCap g (some vn) + 1#64 == 0#64) = false :=
    ProtoRepr.EncodedLen.cap_add_one_beq_zero_false h2
  rw [sepConj_assoc, ← sepConj_assoc]
  exact Entails.pure_right hne
    (Entails.pure_right ⟨hw1, hw2, hw345⟩
      (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _)))

theorem optChainWordsHeap_x25_eq (A : RustAlloc) (g : ChainFrom.ChainPBGhost) (x25 : BitVec 64)
    (opt : Option ChainPB) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) :
    optChainWordsHeap A g x25 opt c1 c2 c3 c4 c5 c6 c7 c8 c9 ⊢
      ⌜x25 = Prost.EncodeToVec.optChainCap g.toProtoRepr opt ∧
        (x25 + 1#64 == 0#64) = !opt.isSome⌝ ∗
      optChainWordsHeap A g x25 opt c1 c2 c3 c4 c5 c6 c7 c8 c9 := by
  cases opt with
  | none =>
    unfold optChainWordsHeap
    exact Entails.trans (Entails.of_eq (sepConj_emp _).symm)
      (Entails.pure_left fun hx25 => Entails.pure_right ⟨hx25, by rw [hx25]; decide⟩
        (Entails.trans (Entails.pure_right hx25 (Entails.refl _)) (Entails.of_eq (sepConj_emp _))))
  | some pb =>
    unfold optChainWordsHeap
    apply Entails.pure_left
    rintro ⟨hx25, hne, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hparams⟩
    have h1 : x25 = Prost.EncodeToVec.optChainCap g.toProtoRepr (some pb) := hx25
    have h2 : (x25 + 1#64 == 0#64) = !(some pb).isSome := by
      rw [hx25]; exact ChainFrom.ChainFromNorm.add_one_beq_zero_of_ne_noneCap hne
    exact Entails.pure_right ⟨h1, h2⟩
      (Entails.pure_right ⟨hx25, hne, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hparams⟩ (Entails.refl _))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 5. Bridge 2 Composition (`0x317fc -> 0x320a4`) -/

theorem memRegion_24_words3_1424 (sp : BitVec 64) :
    memRegion (sp + 1424#64) 24 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp + 1424#64) ↦₆₄ w0) ∗ ((sp + 1432#64) ↦₆₄ w1) ∗ ((sp + 1440#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split' (b := sp + 1424#64) (n := 8) (k := 16) (b' := sp + 1432#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 1432#64) (n := 8) (k := 8) (b' := sp + 1440#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 1424#64), ProofLib.memRegion_eight (sp + 1432#64),
      ProofLib.memRegion_eight (sp + 1440#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.refl _)))

theorem stackAt_spqrSendCallee_split_b2 (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ stackAt sp n := by
  have hle' : n ≤ 123008 := hle
  have hbd : n + (spqrSendCalleeStack - n) ≤ 2 ^ 64 := by change n + (123008 - n) ≤ 2 ^ 64; omega
  have h := ProofLib.stackAt_split_bottom sp n (spqrSendCalleeStack - n) hbd
  rwa [Nat.add_sub_of_le hle] at h

theorem stackAt_spqrSendCallee_eq_allocHook_b2 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_spqrSendCallee_split_b2 sp allocHookStack (by decide)

theorem pqRatchetStatePBEncodedLen_some_v1_pos
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB) (v1s : V1State) :
    0 < Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 v1s) } := by
  unfold Prost.EncodeToVec.pqRatchetStatePBEncodedLen
  dsimp only
  have hp := Prost.EncodeToVec.optPqRatchetInnerPBFieldEncodedLen_pos (.v1 v1s)
  omega

end CryptoVerification.SpqrV1.Top.Send
