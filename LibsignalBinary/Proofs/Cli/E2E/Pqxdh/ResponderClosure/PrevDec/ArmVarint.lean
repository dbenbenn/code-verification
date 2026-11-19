/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Leaf
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2 -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5

/-!
# Varint Arms (Tags 1, 5, 10, 11) of Inlined `SessionStructure::decode`

Verifies the varint field arms (`overDecArm_varint` and `overDecArm_varint_cli_okTR`) of the
inlined `SessionStructure::decode` loop in `message_decrypt_prekey::<Coins>::{closure#0}`:
tag 1 (`session_version` at `[sp, #0xa78]`), tag 5 (`previous_counter` at `[sp, #0xa7c]`),
tag 10 (`remote_registration_id` at `[sp, #0xa80]`), and tag 11 (`local_registration_id` at
`[sp, #0xa84]`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField SSG)
open CryptoVerification.E2E.Record.L1GX (kyberAt)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.SpqrV1.Varint hiding decodeVarint2StackX
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (decodeVarint2StackX)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Stack, Cursor, and `prostSSGQAt` Split Helpers -/

theorem stackAt_overDecStackX_eq_decodeVarint2StackX (q : BitVec 64) :
    stackAt q overDecStackX =
      memRegion (q - BitVec.ofNat 64 overDecStackX) (overDecStackX - decodeVarint2StackX) ∗
        stackAt q decodeVarint2StackX :=
  ProofLib.stackAt_split_bottom q decodeVarint2StackX
    (overDecStackX - decodeVarint2StackX) (by decide)

theorem suffix_payload_of_suffix_enc {fl : GenFieldQ} {rest enc : List (BitVec 8)}
    (hsuf : (fl.enc ++ rest) <:+ enc) :
    (fl.payload ++ rest) <:+ enc := by
  rcases hsuf with ⟨pre, hpre⟩
  refine ⟨pre ++ encodeKey fl.tag fl.wt, ?_⟩
  rw [List.append_assoc, ← List.append_assoc (encodeKey fl.tag fl.wt), ← GenFieldQ.enc, hpre]

theorem payload_append_length_lt_of_suffix {pfx rest enc : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ enc) (hlen : enc.length < 2 ^ 62) :
    (pfx ++ rest).length < 2 ^ 63 := by
  rcases hsuf with ⟨pre, hpre⟩
  have hle : (pfx ++ rest).length ≤ enc.length := by
    simp only [← hpre, List.length_append]; omega
  omega

theorem sliceCursorAfter_split_of_suffix (slot ptr : BitVec 64) {bs pfx rest : List (BitVec 8)}
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

theorem sliceCursorAfter_unsplit_of_suffix (slot ptr : BitVec 64) {bs pfx rest : List (BitVec 8)}
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

@[expose] def kyberPre (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) : SepProp :=
  match kyber with
  | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24
  | some (i, ct) => vecU8 A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
      memRegion (ss + 0x144#64) 4

theorem kyberAt_eq_sep (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (R : SepProp) :
    kyberAt A ss kyber R = kyberPre A ss kyber ∗ R := by
  cases kyber with
  | none => simp only [kyberAt, kyberPre, sepConj_assoc]
  | some p => rcases p with ⟨i, ct⟩; simp only [kyberAt, kyberPre, sepConj_assoc]

@[expose] def prostSSGQHead (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => CryptoVerification.E2E.Record.DeserializeGeneral.prostChainGAt A a c)
      (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => CryptoVerification.E2E.Record.DeserializeGeneral.prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         CryptoVerification.E2E.Record.L1GX.pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberPre A ss v.ext.kyber

theorem prostSSGQAt_eq_head_tail (A : RustAlloc) (q : BitVec 64) (v : SSGQ) :
    prostSSGQAt A (q + 0x930#64) v =
      prostSSGQHead A (q + 0x930#64) v ∗
        ((q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
        ((q + 0xa84#64) ↦₃₂ v.ext.locReg) := by
  unfold prostSSGQAt prostSSGQHead
  rw [kyberAt_eq_sep]
  have h148 : (q + 0x930#64) + 0x148#64 = q + 0xa78#64 := by bv_omega
  have h14c : (q + 0x930#64) + 0x14c#64 = q + 0xa7c#64 := by bv_omega
  have h150 : (q + 0x930#64) + 0x150#64 = q + 0xa80#64 := by bv_omega
  have h154 : (q + 0x930#64) + 0x154#64 = q + 0xa84#64 := by bv_omega
  rw [h148, h14c, h150, h154]
  ac_rfl

@[expose] def overDecVarintRestExt (A : RustAlloc) (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    prostSSGQHead A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - decodeVarint2StackX)

abbrev overDecVarintRest (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overDecVarintRestExt CryptoVerification.E2E.Record.A0 g v curLen

theorem overDecHeap_eq_varint_split_ext {A : RustAlloc} (g : OverDecG) (v : SSGQ)
    {pfx rest : List (BitVec 8)} (hsuf : (pfx ++ rest) <:+ g.enc) :
    overDecHeapExt A g (pfx ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (pfx ++ rest).length)) (pfx ++ rest) ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
      ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
      ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
      ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
      overDecVarintRestExt A g v (pfx ++ rest).length := by
  unfold overDecHeapExt overDecVarintRestExt
  rw [sliceCursorAfter_split_of_suffix (g.q + 0x920#64) g.encPtr hsuf,
      prostSSGQAt_eq_head_tail A g.q v,
      stackAt_overDecStackX_eq_decodeVarint2StackX g.q]
  ac_rfl

theorem overDecHeap_eq_varint_split (g : OverDecG) (v : SSGQ) {pfx rest : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ g.enc) :
    overDecHeap g (pfx ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (pfx ++ rest).length)) (pfx ++ rest) ∗
      CryptoVerification.E2E.Record.A0.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
      ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
      ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
      ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
      overDecVarintRest g v (pfx ++ rest).length :=
  overDecHeap_eq_varint_split_ext g v hsuf

theorem overDecHeap_eq_varint_unsplit_ext {A : RustAlloc} (g : OverDecG) (v' : SSGQ)
    {pfx rest : List (BitVec 8)} (hsuf : (pfx ++ rest) <:+ g.enc) :
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (pfx ++ rest).length)) (pfx ++ rest) rest ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + 0xa78#64) ↦₃₂ v'.base.version) ∗
      ((g.q + 0xa7c#64) ↦₃₂ v'.base.prevCounter) ∗
      ((g.q + 0xa80#64) ↦₃₂ v'.ext.remReg) ∗
      ((g.q + 0xa84#64) ↦₃₂ v'.ext.locReg) ∗
      overDecVarintRestExt A g v' (pfx ++ rest).length =
      overDecHeapExt A g rest v' := by
  unfold overDecHeapExt overDecVarintRestExt
  rw [← sliceCursorAfter_unsplit_of_suffix (g.q + 0x920#64) g.encPtr hsuf,
      prostSSGQAt_eq_head_tail A g.q v',
      stackAt_overDecStackX_eq_decodeVarint2StackX g.q]
  ac_rfl

theorem overDecHeap_eq_varint_unsplit (g : OverDecG) (v' : SSGQ) {pfx rest : List (BitVec 8)}
    (hsuf : (pfx ++ rest) <:+ g.enc) :
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (pfx ++ rest).length)) (pfx ++ rest) rest ∗
      CryptoVerification.E2E.Record.A0.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + 0xa78#64) ↦₃₂ v'.base.version) ∗
      ((g.q + 0xa7c#64) ↦₃₂ v'.base.prevCounter) ∗
      ((g.q + 0xa80#64) ↦₃₂ v'.ext.remReg) ∗
      ((g.q + 0xa84#64) ↦₃₂ v'.ext.locReg) ∗
      overDecVarintRest g v' (pfx ++ rest).length =
      overDecHeap g rest v' :=
  overDecHeap_eq_varint_unsplit_ext g v' hsuf

private def OverDecSavedRegs (g : OverDecG) (s : State) : Prop :=
  s.readReg64 .x19 = g.r19 ∧ s.readReg64 .x20 = g.r20 ∧ s.readReg64 .x26 = g.r26 ∧
  s.readReg64 .x21 = g.q + 0x930#64 ∧ s.readReg64 .x24 = 1#64 ∧
  s.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s.readReg64 .x27 = g.prevPtr ∧
  s.readReg64 .x28 = g.q + 0xa90#64 ∧ s.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs s = calleeSavedVRegs g.sv

private theorem overDecSavedRegs_of_calleeSaved {g : OverDecG} {s1 s2 : State}
    (hs1 : OverDecSavedRegs g s1) (hcs : CalleeSavedPreserved s1 s2) :
    OverDecSavedRegs g s2 := by
  rcases hs1 with ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  rcases hcs with ⟨c19, c20, c21, _, _, c24, c25, c26, c27, c28, c29, cv⟩
  exact ⟨c19.trans h19, c20.trans h20, c26.trans h26, c21.trans h21, c24.trans h24,
    c25.trans h25, c27.trans h27, c28.trans h28, c29.trans h29, cv.trans hv⟩

attribute [local simp, local arm64_norm, local wp_norm] State.readReg32

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).trace = s.trace := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local simp, local arm64_norm, local wp_norm]
theorem truncate_32_setWidth_64 (v : BitVec 32) : BitVec.truncate 32 (v.setWidth 64) = v := by
  bv_robdd

@[local simp, local arm64_norm, local wp_norm]
theorem setWidth_32_setWidth_64 (v : BitVec 32) : BitVec.setWidth 32 (v.setWidth 64) = v := by
  bv_robdd

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
