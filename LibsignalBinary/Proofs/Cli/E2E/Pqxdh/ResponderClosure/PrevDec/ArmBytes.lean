/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10

/-!
# Bytes Arms (Tags 2, 3, 4, 13, 15) of Inlined `SessionStructure::decode`

Proves per-tag and combined `OverDecBytesField` decode-arm theorems (`+0x22cc`, `+0x22b8`, `+0x2290`,
`+0x21d4`, `+0x2200 → +0x2160`) in `message_decrypt_prekey::<Coins>::{closure#0}`, invoking
`bytes::merge [local#6]` (`BytesMerge6OkExtW`) on `local_identity_public`, `remote_identity_public`,
`root_key`, `alice_base_key`, and `pq_ratchet_state`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.LibsignalTripleRatchet.Prost

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

private theorem SepWPp_weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

theorem stackAt_overDec_to_bytesMerge3 (sp : BitVec 64) :
    stackAt sp overDecStackX =
      memRegion (sp - 65536#64) (65536 - bytesMerge3Stack) ∗ stackAt sp bytesMerge3Stack := by
  have hN : overDecStackX = bytesMerge3Stack + (65536 - bytesMerge3Stack) := by decide
  have hb : BitVec.ofNat 64 (bytesMerge3Stack + (65536 - bytesMerge3Stack)) = 65536#64 := by decide
  rw [hN, ProofLib.stackAt_split_bottom sp bytesMerge3Stack (65536 - bytesMerge3Stack) (by decide), hb]

/-- `prostSSGQAt` without `local_identity_public` (`ss`). -/
@[expose] def prostSSGQRest2 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_lik_sep_rest2 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A ss v.base.lik ∗ prostSSGQRest2 A ss v := by
  unfold prostSSGQAt prostSSGQRest2
  cases v.base.sender <;> cases v.base.pending <;> dsimp only

/-- `prostSSGQAt` without `remote_identity_public` (`ss + 0x18`). -/
@[expose] def prostSSGQRest3 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_rik_sep_rest3 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x18#64) v.base.rik ∗ prostSSGQRest3 A ss v := by
  unfold prostSSGQAt prostSSGQRest3
  cases v.base.sender <;> cases v.base.pending <;> dsimp only <;> ac_rfl

/-- `prostSSGQAt` without `root_key` (`ss + 0x30`). -/
@[expose] def prostSSGQRest4 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_root_sep_rest4 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x30#64) v.base.root ∗ prostSSGQRest4 A ss v := by
  unfold prostSSGQAt prostSSGQRest4
  cases v.base.sender <;> cases v.base.pending <;> dsimp only <;> ac_rfl

/-- `prostSSGQAt` without `alice_base_key` (`ss + 0x60`). -/
@[expose] def prostSSGQRest13 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_abk_sep_rest13 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x60#64) v.ext.abk ∗ prostSSGQRest13 A ss v := by
  unfold prostSSGQAt prostSSGQRest13
  cases v.base.sender <;> cases v.base.pending <;> dsimp only <;> ac_rfl

/-- `prostSSGQAt` without `pq_ratchet_state` (`ss + 0x78`). -/
@[expose] def prostSSGQRest15 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGQAt_eq_pq_sep_rest15 (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v = vecU8 A (ss + 0x78#64) v.ext.pq ∗ prostSSGQRest15 A ss v := by
  unfold prostSSGQAt prostSSGQRest15
  cases v.base.sender <;> cases v.base.pending <;> dsimp only <;> ac_rfl

/-! ## Slice Cursor Split and Recombination -/

theorem sliceCursorAfter_split_sub (slot ptr : BitVec 64) (pfx sfx : List (BitVec 8)) :
    Prost.sliceCursorAfter slot ptr (pfx ++ sfx) sfx =
      (ptr ↦ₛ pfx) ∗ Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 pfx.length) sfx :=
  sliceCursorAfter_append_eq_seedChain slot ptr pfx sfx

theorem sliceCursorAfter_unsplit_sub (slot ptr : BitVec 64) (pfx payload rest : List (BitVec 8)) :
    (ptr ↦ₛ pfx) ∗
        Prost.sliceCursorAfter slot (ptr + BitVec.ofNat 64 pfx.length) (payload ++ rest) rest =
      Prost.sliceCursorAfter slot ptr (pfx ++ (payload ++ rest)) rest := by
  unfold Prost.sliceCursorAfter
  have hlen : (pfx ++ (payload ++ rest)).length - rest.length = pfx.length + payload.length := by
    simp only [List.length_append]; omega
  have hlen2 : (payload ++ rest).length - rest.length = payload.length := by
    simp only [List.length_append]; omega
  rw [hlen, hlen2, BitVec.ofNat_add, ← BitVec.add_assoc, pointsToBytes_append ptr pfx (payload ++ rest)]
  ac_rfl

/-! ## Call Offset for `bytes::merge [local#6]` -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Shared Call and Post-Call `cbz` Helpers -/

theorem overDec_payload_suffix_and_len {fl : GenFieldQ} {rest enc : List (BitVec 8)}
    (hsuf : (fl.enc ++ rest) <:+ enc) (hlen : enc.length < 2 ^ 62) :
    ∃ pfx : List (BitVec 8),
      enc = pfx ++ (fl.payload ++ rest) ∧ (fl.payload ++ rest).length < 2 ^ 62 := by
  rcases hsuf with ⟨t, ht⟩
  unfold GenFieldQ.enc at ht
  refine ⟨t ++ encodeKey fl.tag fl.wt, ?_, ?_⟩
  · rw [← ht, List.append_assoc, List.append_assoc]
  · have hle : (fl.payload ++ rest).length ≤ enc.length := by
      simp only [← ht, List.length_append]
      omega
    omega

theorem overDec_mergeBytes_eq (b rest : List (BitVec 8)) (hb : b.length < 2 ^ 64) :
    mergeBytes .lengthDelimited ((encodeVarint (BitVec.ofNat 64 b.length) ++ b) ++ rest) =
      some (b, rest) := by
  rw [List.append_assoc]
  exact mergeBytes_encode b rest hb

abbrev OverDecCbzPost (s : State) (g : OverDecG) (sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ emp) ∧
  sf.sp = g.q ∧
  sf.trace = s.trace ∧
  sf.readReg64 .x19 = g.r19 ∧
  sf.readReg64 .x20 = g.r20 ∧
  sf.readReg64 .x21 = g.q + 0x930#64 ∧
  sf.readReg64 .x24 = 1#64 ∧
  sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧
  sf.readReg64 .x26 = g.r26 ∧
  sf.readReg64 .x27 = g.prevPtr ∧
  sf.readReg64 .x28 = g.q + 0xa90#64 ∧
  sf.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs sf = calleeSavedVRegs s

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
