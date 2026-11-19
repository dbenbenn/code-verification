/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Shared Definitions and Run-to-Tail Bridges for `T5` Protocol-Error Tails

Common frame definitions, straight-line `SepWP`-to-tail bridges (`encTail_run`, `segExit_of_run`,
`encTail_run_withEncCommon`), and `pollWith` splitting lemmas shared by `tailSignalEncryptErr_ok`,
`tailPreKeyEncryptErr_ok`, `tailStoreHookErr_ok`, and `tailCmDrop_ok`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

/-! ## Tail Frame Definitions -/

@[expose] def words64At : BitVec 64 → List (BitVec 64) → SepProp
  | _, [] => emp
  | a, w :: ws => (a ↦₆₄ w) ∗ words64At (a + 8#64) ws

@[expose] def pollWith (sp : BitVec 64) (off : Nat) (ws : List (BitVec 64)) : SepProp :=
  memRegion (sp + 0x46a#64) (off - 0x46a) ∗ words64At (sp + BitVec.ofNat 64 off) ws ∗
    memRegion (sp + BitVec.ofNat 64 (off + 8 * ws.length)) (0xb80 - (off + 8 * ws.length))

@[expose] def otrSlotAt (A : RustAlloc) (sp : BitVec 64) :
    Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))) → SepProp
  | some (pqCap, pqPtr, ot) => otrAt A (sp + 0x288#64) pqCap pqPtr ot ∗ ((sp + 0x469#64) ↦₈ 1#8)
  | none => memRegion (sp + 0x288#64) 200 ∗ ((sp + 0x469#64) ↦₈ 0#8)

@[expose] def cmSlotAt (A : RustAlloc) (sp : BitVec 64) : Option CiphertextMessage → SepProp
  | some m => memRegion (sp + 0x350#64) 0x20 ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      memRegion (sp + 0x468#64) 1
  | none => memRegion (sp + 0x350#64) 0x119

@[expose] def dropRecordSlots (A : RustAlloc) (sp : BitVec 64) (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (cm : Option CiphertextMessage) (poll : SepProp) : SepProp :=
  scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
    otrSlotAt A sp ot ∗ cmSlotAt A sp cm ∗ poll

@[expose] def tailRegs (w0 w1 w2 : BitVec 64) (sp : BitVec 64) (s : State) : Prop :=
  s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w0 ∧
    s.readReg64 .x21 = w1 ∧ s.readReg64 .x23 = w2

open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Pure model and trace relation at an `encrypt` tail entry. -/
@[expose] def TailModel {A : RustAlloc} {base : BitVec 64} (kit : SessionStoreSpec A base)
    (st0 : kit.StoreState) (ikit : IdentityStoreSpec A base) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (x : WithStoresEncGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (s0 s : State) : Prop :=
  ((x.model C S parse answers).1 = res ∧
    kit.callsRel st0 answers (x.model C S parse answers).2 ∧
    ikit.idCallsRel ist0 answers (x.model C S parse answers).2) ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2

/-- `dropRecordSlots` excluding the `cmSlotAt` and poll-buffer components. -/
@[expose] def dropRecordBase (A : RustAlloc) (sp : BitVec 64) (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))) : SepProp :=
  scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
    otrSlotAt A sp ot

theorem dropRecordSlots_eq (A : RustAlloc) (sp : BitVec 64) (scratch : BitVec 64 → SepProp)
    (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (cm : Option CiphertextMessage) (poll : SepProp) :
    dropRecordSlots A sp scratch g rec ot cm poll = dropRecordBase A sp scratch g rec ot ∗ cmSlotAt A sp cm ∗ poll := by
  unfold dropRecordSlots dropRecordBase
  ac_rfl

/-! ## Run-to-Tail Bridges -/

theorem words64At_three_entails (a w0 w1 w2 : BitVec 64) :
    words64At a [w0, w1, w2] ⊢ memRegion a 24 := by
  unfold words64At words64At words64At words64At
  rw [sepConj_emp, memRegion_split a 8 16 (by decide), memRegion_split (a + BitVec.ofNat 64 8) 8 8
    (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem memRegion_24_eq (a : BitVec 64) :
    memRegion a 24 = (∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
      words64At a [u0, u1, u2]) := by
  unfold words64At words64At words64At words64At
  rw [memRegion_split a 8 16 (by decide), memRegion_split (a + BitVec.ofNat 64 8) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc,
    BitVec.reduceAdd]

theorem memRegion_cut (a : BitVec 64) (len n k : Nat) (hk : n + k = len) (h : len ≤ 2 ^ 64) :
    memRegion a len = memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k := by
  subst hk
  exact memRegion_split a n k h

theorem pollWith_9d0_eq (sp w3 w4 w5 : BitVec 64) :
    pollWith sp 0x9d0 [w3, w4, w5] =
      words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (sp + 0xb00#64) 24 ∗
        (memRegion (sp + 0x46a#64) 0x566 ∗ memRegion (sp + 0x9e8#64) 0x118 ∗
          memRegion (sp + 0xb18#64) 0x68) := by
  unfold pollWith
  rw [show (0xb80 - (0x9d0 + 8 * [w3, w4, w5].length)) = 0x198 from rfl,
    memRegion_cut _ 0x198 0x118 0x80 rfl (by decide),
    memRegion_cut _ 0x80 24 0x68 rfl (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
  ac_rfl

theorem pollWith_b00_eq (sp w3 w4 w5 : BitVec 64) :
    pollWith sp 0xb00 [w3, w4, w5] =
      memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
        (memRegion (sp + 0x46a#64) 0x566 ∗ memRegion (sp + 0x9e8#64) 0x118 ∗
          memRegion (sp + 0xb18#64) 0x68) := by
  unfold pollWith
  rw [show (0xb00 - 0x46a) = 0x696 from rfl,
    memRegion_cut _ 0x696 0x566 0x130 rfl (by decide),
    memRegion_cut _ 0x130 24 0x118 rfl (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
  ac_rfl

theorem addr_ofNat_add (sp : BitVec 64) (a b c : Nat) (h : a + b = c) :
    sp + BitVec.ofNat 64 a + BitVec.ofNat 64 b = sp + BitVec.ofNat 64 c := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h]

theorem memRegion_46a_src (sp : BitVec 64) (src : Nat) (hlo : 0x46a ≤ src)
    (hhi : src + 24 ≤ 0x9d0) :
    memRegion (sp + 0x46a#64) 0x566 = memRegion (sp + 0x46a#64) (src - 0x46a) ∗
      memRegion (sp + BitVec.ofNat 64 src) 24 ∗
      memRegion (sp + BitVec.ofNat 64 (src + 24)) (0x9d0 - (src + 24)) := by
  rw [memRegion_cut _ 0x566 (src - 0x46a) (24 + (0x9d0 - (src + 24))) (by omega) (by decide),
    memRegion_cut _ (24 + (0x9d0 - (src + 24))) 24 (0x9d0 - (src + 24)) rfl (by omega),
    addr_ofNat_add sp 0x46a (src - 0x46a) src (by omega),
    addr_ofNat_add sp src 24 (src + 24) rfl]

theorem pollWith_src_eq (sp w3 w4 w5 : BitVec 64) (src : Nat) (hhi : src + 24 ≤ 0x9d0) :
    pollWith sp src [w3, w4, w5] =
      memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + BitVec.ofNat 64 src) [w3, w4, w5] ∗
        (memRegion (sp + 0x46a#64) (src - 0x46a) ∗
          memRegion (sp + BitVec.ofNat 64 (src + 24)) (0x9d0 - (src + 24)) ∗
          memRegion (sp + 0x9e8#64) 0x198) := by
  unfold pollWith
  rw [show 8 * [w3, w4, w5].length = 24 from rfl,
    memRegion_cut _ (0xb80 - (src + 24)) (0x9d0 - (src + 24)) (24 + 0x198) (by omega)
      (Nat.le_trans (Nat.sub_le _ _) (by decide)),
    memRegion_cut _ (24 + 0x198) 24 0x198 rfl (by decide),
    addr_ofNat_add sp (src + 24) (0x9d0 - (src + 24)) 0x9d0 (by omega),
    addr_ofNat_add sp 0x9d0 24 0x9e8 rfl]
  ac_rfl

theorem pollWith_9d0_eq' (sp w3 w4 w5 : BitVec 64) :
    pollWith sp 0x9d0 [w3, w4, w5] =
      memRegion (sp + 0x46a#64) 0x566 ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
        memRegion (sp + 0x9e8#64) 0x198 := by
  unfold pollWith
  rfl

theorem cmSlot_none_eq (A : RustAlloc) (sp : BitVec 64) :
    cmSlotAt A sp none =
      memRegion (sp + 0x350#64) 0x20 ∗ memRegion (sp + 0x370#64) 248 ∗
        memRegion (sp + 0x468#64) 1 := by
  unfold cmSlotAt
  rw [memRegion_cut _ 0x119 0x20 249 rfl (by decide), memRegion_cut _ 249 248 1 rfl (by decide),
    addr_ofNat_add sp 0x350 0x20 0x370 rfl, addr_ofNat_add sp 0x370 248 0x468 rfl]

/-! ## Instruction Decode Lemmas -/

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
