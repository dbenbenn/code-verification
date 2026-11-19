/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Tag 7 (`receiver_chains`) Arm of Inlined `SessionStructure::decode`

Proves the tag-7 (`receiver_chains`, `+0x22e0 → +0x2160`) decode arm in
`message_decrypt_prekey::<Coins>::{closure#0}`, invoking `message::merge<Chain> [local#5]` on
`q + 0xbf0` and composing with Segment B (`OverDecRecvSegBStmt`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG prostChainGAt GenField ChainMergeGenGhost)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ExtraGQ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] State.readReg32

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem allowPanic_oom_of_trace_eq {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    unfold allocFailedIn at ha ⊢
    rw [← htr]
    exact ⟨ha, hp⟩
  exact allowPanic_frame himp hm

private theorem SepWPp_weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

set_option maxHeartbeats 400000 in
theorem stackAt_overDecStackX_eq_chainMerge3StackX (q : BitVec 64) :
    stackAt q overDecStackX =
      memRegion (q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX) ∗
        stackAt q chainMerge3StackX :=
  ProofLib.stackAt_split_bottom q chainMerge3StackX
    (overDecStackX - chainMerge3StackX) (by decide)

set_option maxHeartbeats 400000 in
theorem suffix_payload_of_suffix_enc_recv {fl : GenFieldQ} {rest enc : List (BitVec 8)}
    (hsuf : (fl.enc ++ rest) <:+ enc) :
    (fl.payload ++ rest) <:+ enc := by
  rcases hsuf with ⟨pre, hpre⟩
  refine ⟨pre ++ encodeKey fl.tag fl.wt, ?_⟩
  rw [List.append_assoc, ← List.append_assoc (encodeKey fl.tag fl.wt), ← GenFieldQ.enc, hpre]

set_option maxHeartbeats 400000 in
theorem payload_append_length_lt62_of_suffix {pfx rest enc : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ enc) (hlen : enc.length < 2 ^ 62) :
    (pfx ++ rest).length < 2 ^ 62 := by
  rcases hsuf with ⟨pre, hpre⟩
  have hle : (pfx ++ rest).length ≤ enc.length := by
    simp only [← hpre, List.length_append]; omega
  omega

set_option maxHeartbeats 400000 in
theorem sliceCursorAfter_split_of_suffix_recv (slot ptr : BitVec 64) {bs pfx rest : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ bs) :
    sliceCursorAfter slot ptr bs (pfx ++ rest) =
      sliceCursorAt slot (ptr + BitVec.ofNat 64 (bs.length - (pfx ++ rest).length)) (pfx ++ rest) ∗
        (ptr ↦ₛ bs.take (bs.length - (pfx ++ rest).length)) := by
  rcases hsuf with ⟨pre, hpre⟩
  have hsub : bs.length - (pfx ++ rest).length = pre.length := by
    rw [← hpre, List.length_append]; omega
  have htake : bs.take (bs.length - (pfx ++ rest).length) = pre := by
    rw [hsub, ← hpre, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hpts : (ptr ↦ₛ bs) =
      (ptr ↦ₛ pre) ∗ ((ptr + BitVec.ofNat 64 pre.length) ↦ₛ (pfx ++ rest)) := by
    conv_lhs => rw [← hpre]
    exact pointsToBytes_append ptr pre (pfx ++ rest)
  unfold sliceCursorAfter sliceCursorAt
  rw [htake, hsub, hpts]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem sliceCursorAfter_unsplit_of_suffix_recv (slot ptr : BitVec 64) {bs pfx rest : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ bs) :
    sliceCursorAfter slot (ptr + BitVec.ofNat 64 (bs.length - (pfx ++ rest).length)) (pfx ++ rest) rest ∗
      (ptr ↦ₛ bs.take (bs.length - (pfx ++ rest).length)) =
      sliceCursorAfter slot ptr bs rest := by
  rcases hsuf with ⟨pre, hpre⟩
  have hsub : bs.length - (pfx ++ rest).length = pre.length := by
    rw [← hpre, List.length_append]; omega
  have htake : bs.take (bs.length - (pfx ++ rest).length) = pre := by
    rw [hsub, ← hpre, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hpay_sub : (pfx ++ rest).length - rest.length = pfx.length := by
    rw [List.length_append]; omega
  have hbs_sub : bs.length - rest.length = pre.length + pfx.length := by
    rw [← hpre, List.length_append, List.length_append]; omega
  have hptr : ptr + BitVec.ofNat 64 pre.length + BitVec.ofNat 64 pfx.length =
      ptr + BitVec.ofNat 64 (pre.length + pfx.length) := by
    rw [BitVec.ofNat_add]; bv_omega
  have hpts : (ptr ↦ₛ bs) =
      (ptr ↦ₛ pre) ∗ ((ptr + BitVec.ofNat 64 pre.length) ↦ₛ (pfx ++ rest)) := by
    conv_lhs => rw [← hpre]
    exact pointsToBytes_append ptr pre (pfx ++ rest)
  unfold sliceCursorAfter
  rw [htake, hsub, hpay_sub, hbs_sub, hptr, hpts]
  ac_rfl

set_option maxHeartbeats 400000 in
private theorem memRegion_succ8_recv (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (8 + n) =
      (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [ProofLib.memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

set_option maxHeartbeats 400000 in
theorem memRegion128_bf0_split_80_24_24 (q : BitVec 64) :
    memRegion (q + 0xbf0#64) 128 =
      memRegion (q + 0xbf0#64) 80 ∗
      memRegion (q + 0xc40#64) 24 ∗
      memRegion (q + 0xc58#64) 24 := by
  have s1 := ProofLib.memRegion_split (q + 0xbf0#64) 80 48 (by omega)
  have s2 := ProofLib.memRegion_split (q + 0xc40#64) 24 24 (by omega)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at s1 s2
  rw [s1, s2]

set_option maxHeartbeats 400000 in
theorem memRegion80_bf0_eq_cells10 (q : BitVec 64) :
    memRegion (q + 0xbf0#64) 80 =
      ∃∗ u9 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64,
      ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((q + 0xbf0#64) ↦₆₄ u0) ∗
        ((q + 0xbf8#64) ↦₆₄ u1) ∗ ((q + 0xc00#64) ↦₆₄ u2) ∗ ((q + 0xc08#64) ↦₆₄ u3) ∗
        ((q + 0xc10#64) ↦₆₄ u4) ∗ ((q + 0xc18#64) ↦₆₄ u5) ∗ ((q + 0xc20#64) ↦₆₄ u6) ∗
        ((q + 0xc28#64) ↦₆₄ u7) ∗ ((q + 0xc30#64) ↦₆₄ u8) ∗ ((q + 0xc38#64) ↦₆₄ u9) := by
  have s0 := memRegion_succ8_recv (q + 0xbf0#64) 72 (by omega)
  have s1 := memRegion_succ8_recv (q + 0xbf8#64) 64 (by omega)
  have s2 := memRegion_succ8_recv (q + 0xc00#64) 56 (by omega)
  have s3 := memRegion_succ8_recv (q + 0xc08#64) 48 (by omega)
  have s4 := memRegion_succ8_recv (q + 0xc10#64) 40 (by omega)
  have s5 := memRegion_succ8_recv (q + 0xc18#64) 32 (by omega)
  have s6 := memRegion_succ8_recv (q + 0xc20#64) 24 (by omega)
  have s7 := memRegion_succ8_recv (q + 0xc28#64) 16 (by omega)
  have s8 := memRegion_succ8_recv (q + 0xc30#64) 8 (by omega)
  have s9 := ProofLib.memRegion_eight (q + 0xc38#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at s0 s1 s2 s3 s4 s5 s6 s7 s8
  rw [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

set_option maxHeartbeats 400000 in
theorem default_cells_bf0_entail_chain3GAt_ext (A : RustAlloc) (q : BitVec 64) :
    (((q + 0xbf0#64) ↦₆₄ 0#64) ∗
    ((q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((q + 0xc00#64) ↦₆₄ 0#64) ∗ ((q + 0xc08#64) ↦₆₄ 0#64) ∗
    ((q + 0xc10#64) ↦₆₄ 1#64) ∗ ((q + 0xc18#64) ↦₆₄ 0#64) ∗ ((q + 0xc20#64) ↦₆₄ 0#64) ∗
    ((q + 0xc28#64) ↦₆₄ 8#64) ∗ ((q + 0xc30#64) ↦₆₄ 0#64) ∗
    ((q + 0xc38#64) ↦₆₄ noneCap)) ∗ memRegion (q + 0xc40#64) 24 ⊢
      chain3GAt A (q + 0xbf0#64) ChainG.empty := by
  have h := default_cells_entail_chain3GAt A (q + 0xbf0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h ⊢
  exact h

theorem default_cells_bf0_entail_chain3GAt (q : BitVec 64) :
    (((q + 0xbf0#64) ↦₆₄ 0#64) ∗
    ((q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((q + 0xc00#64) ↦₆₄ 0#64) ∗ ((q + 0xc08#64) ↦₆₄ 0#64) ∗
    ((q + 0xc10#64) ↦₆₄ 1#64) ∗ ((q + 0xc18#64) ↦₆₄ 0#64) ∗ ((q + 0xc20#64) ↦₆₄ 0#64) ∗
    ((q + 0xc28#64) ↦₆₄ 8#64) ∗ ((q + 0xc30#64) ↦₆₄ 0#64) ∗
    ((q + 0xc38#64) ↦₆₄ noneCap)) ∗ memRegion (q + 0xc40#64) 24 ⊢
      chain3GAt CryptoVerification.E2E.Record.A0 (q + 0xbf0#64) ChainG.empty :=
  default_cells_bf0_entail_chain3GAt_ext CryptoVerification.E2E.Record.A0 q

@[expose] def OverDecSavedRegs (g : OverDecG) (s : State) : Prop :=
  s.readReg64 .x19 = g.r19 ∧ s.readReg64 .x20 = g.r20 ∧ s.readReg64 .x26 = g.r26 ∧
  s.readReg64 .x21 = g.q + 0x930#64 ∧ s.readReg64 .x24 = 1#64 ∧
  s.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s.readReg64 .x27 = g.prevPtr ∧
  s.readReg64 .x28 = g.q + 0xa90#64 ∧ s.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs s = calleeSavedVRegs g.sv

set_option maxHeartbeats 400000 in
theorem overDecSavedRegs_of_calleeSaved {g : OverDecG} {s1 s2 : State}
    (hs1 : OverDecSavedRegs g s1) (hcs : CalleeSavedPreserved s1 s2) :
    OverDecSavedRegs g s2 := by
  rcases hs1 with ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  rcases hcs with ⟨c19, c20, c21, _, _, c24, c25, c26, c27, c28, c29, cv⟩
  exact ⟨c19.trans h19, c20.trans h20, c26.trans h26, c21.trans h21, c24.trans h24,
    c25.trans h25, c27.trans h27, c28.trans h28, c29.trans h29, cv.trans hv⟩

@[expose] def overDecRecvFrameRest (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overPrevElemRest g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    prostSSGQAt CryptoVerification.E2E.Record.A0 (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX) ∗
    CryptoVerification.E2E.Record.A0.pool

set_option maxHeartbeats 400000 in
theorem overDecHeap_eq_recv_split (g : OverDecG) (v : SSGQ) {c : ChainG} {rest : List (BitVec 8)}
    (hsuf : (c.payload ++ rest) <:+ g.enc) :
    overDecHeap g (c.payload ++ rest) v =
      memRegion (g.q + 0xbf0#64) 80 ∗
      (memRegion (g.q + 0xc40#64) 24 ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) ∗
        stackAt g.q chainMerge3StackX ∗
        overDecRecvFrameRest g v (c.payload ++ rest).length) := by
  unfold overDecHeap overDecHeapExt overDecRecvFrameRest
  rw [sliceCursorAfter_split_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      memRegion128_bf0_split_80_24_24 g.q,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem overDecRecvPostMergeHeap_eq_unsplit (g : OverDecG) (v : SSGQ) {c : ChainG}
    {rest : List (BitVec 8)} (hsuf : (c.payload ++ rest) <:+ g.enc) :
    prostChainGAt CryptoVerification.E2E.Record.A0 (g.q + 0xbf0#64) c ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) rest ∗
      stackAt g.q chainMerge3StackX ∗
      overDecRecvFrameRest g v (c.payload ++ rest).length =
      overDecRecvPostMergeHeap g rest v c := by
  unfold overDecRecvPostMergeHeap overDecRecvPostMergeHeapExt overDecRecvFrameRest
  rw [← sliceCursorAfter_unsplit_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  ac_rfl

@[expose] def overDecRecvFrameRestExt (A : RustAlloc) (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    prostSSGQAt A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX)

set_option maxHeartbeats 400000 in
theorem overDecHeap_eq_recv_split_ext (A : RustAlloc) (g : OverDecG) (v : SSGQ) {c : ChainG}
    {rest : List (BitVec 8)} (hsuf : (c.payload ++ rest) <:+ g.enc) :
    overDecHeapExt A g (c.payload ++ rest) v =
      memRegion (g.q + 0xbf0#64) 80 ∗
      (memRegion (g.q + 0xc40#64) 24 ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) ∗
        A.pool ∗
        stackAt g.q chainMerge3StackX ∗
        overDecRecvFrameRestExt A g v (c.payload ++ rest).length) := by
  unfold overDecHeapExt overDecRecvFrameRestExt
  rw [sliceCursorAfter_split_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      memRegion128_bf0_split_80_24_24 g.q,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem overDecRecvPostMergeHeap_eq_unsplit_ext (A : RustAlloc) (g : OverDecG) (v : SSGQ)
    {c : ChainG} {rest : List (BitVec 8)} (hsuf : (c.payload ++ rest) <:+ g.enc) :
    prostChainGAt A (g.q + 0xbf0#64) c ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) rest ∗
      A.pool ∗
      stackAt g.q chainMerge3StackX ∗
      overDecRecvFrameRestExt A g v (c.payload ++ rest).length =
      overDecRecvPostMergeHeapExt A g rest v c := by
  unfold overDecRecvPostMergeHeapExt overDecRecvFrameRestExt
  rw [← sliceCursorAfter_unsplit_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  ac_rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
