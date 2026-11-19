/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageLengthBound
public import LibsignalBinary.Heap.Fine.CreditInst
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit -- proof-setup: allow-public-import
public import Arm64.Trusted.Object.Labels
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
public import VerifiedLibraries.RustStd.Spec.AllocStringClone
public import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import VerifiedLibraries.RustStd.Spec.FsRead
public import VerifiedLibraries.RustStd.Spec.FsWrite
public import VerifiedLibraries.RustStd.Spec.Stdio
public import VerifiedLibraries.RustStd.Spec.TimeAdd
public import VerifiedLibraries.RustStd.Spec.TimeDurationSince
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeStage1
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon

/-!
# Budget-Threaded `MessageEncrypt` Callee Contracts

Allocator-budget (`RustCliAllocBudget M`) contracts, exact allocation event envelopes,
`PhaseCreditSpec` bounds, and `FitsEnv` witnesses for `kyberMap`, `PreKeySignalMessage::new`,
and `drop_glue::<CiphertextMessage>`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FreeOnlyEvs
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel FineStepBound)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineStepReserveOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineMaxGroupsOfCum)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
  (phaseCredit_eq_append phaseCredit_eq_append_sym witnessPublicKey witnessIdentityKey)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (CiphertextMessage KyberPayload)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (KyberMapCall PreKeyMsgNewCall)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- Concrete allocation envelope for `kyberMap`
    (`Option<(KyberPreKeyId, &[u8])>::map(KyberPayload::new)`):
    `[]` when `none` or `ciphertext = []`, and `rustAllocEvents len 1` when `0 < len`. -/
@[expose] def KyberOptEnv (ct : Option (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match ct with
  | none => evs = []
  | some bs =>
    (bs.length = 0 ∧ evs = []) ∨
    (0 < bs.length ∧ evs = rustAllocEvents bs.length 1)

/-- Budget-threaded `kyberMap` contract (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def kyberMapSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (KyberMapCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (KyberOptEnv (x.kp.map (·.ciphertext)))⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.kyberMapSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜KyberOptEnv (x.kp.map (·.ciphertext)) evs⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.kyberMapSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Allocation events emitted when cloning an optional `KyberPayload` ciphertext inside
    `PreKeySignalMessage::new`. -/
@[expose] def kyberCopyEvs (kp : Option KyberPayload) : List AllocEvent :=
  match kp with
  | none => []
  | some k =>
    if k.ciphertext = [] then []
    else rustAllocEvents k.ciphertext.length 1

/-- Deallocation events emitted when dropping the cloned `KyberPayload` buffer inside
    `PreKeySignalMessage::new`. -/
@[expose] def kyberDeallocEvs (kp : Option KyberPayload) : List AllocEvent :=
  match kp with
  | none => []
  | some k =>
    if k.ciphertext = [] then []
    else rustDeallocEvents k.ciphertext.length 1

/-- Exact prologue allocation events of `PreKeySignalMessage::new` (up to `SeamA` / `SeamB`):
    optional Kyber ciphertext clone, two 33-byte public-key serializations (`baseKey`, `ik`),
    `SignalMessage` serialized bytes clone (`smLen`), and output `Vec<u8>` buffer (`outLen`). -/
@[expose] def preKeyMsgNewRawPrologueEvents (kp : Option KyberPayload) (smLen outLen : Nat) :
    List AllocEvent :=
  kyberCopyEvs kp ++ (rustAllocEvents 33 1 ++ rustAllocEvents 33 1) ++
    rustAllocEvents smLen 1 ++ rustAllocEvents outLen 1

/-- Exact full allocator event list of `PreKeySignalMessage::new`:
    prologue allocations followed by the 4 temporary buffer deallocations (`kyber`, `baseKey`,
    `ik`, `sm`). -/
@[expose] def preKeyMsgNewRawEvents (kp : Option KyberPayload) (smLen outLen : Nat) : List AllocEvent :=
  preKeyMsgNewRawPrologueEvents kp smLen outLen ++
    kyberDeallocEvs kp ++ (rustDeallocEvents 33 1 ++ rustDeallocEvents 33 1) ++
    rustDeallocEvents smLen 1

/-- Pointer-independent exact allocation envelope for `PreKeySignalMessage::new`. -/
@[expose] def PreKeyMsgNewRawEnv (kp : Option KyberPayload) (smLen outLen : Nat)
    (evs : List AllocEvent) : Prop :=
  evs = preKeyMsgNewRawEvents kp smLen outLen

/-- Concrete allocation envelope for `PreKeySignalMessage::new` on `PreKeyMsgNewCall`. -/
@[expose] def PreKeyMsgNewEnv (x : PreKeyMsgNewCall) (evs : List AllocEvent) : Prop :=
  PreKeyMsgNewRawEnv x.kp x.msg.serialized.length x.model.serialized.length evs

/-- Placement-free budget-threaded `PreKeySignalMessage::new` contract (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def preKeyMsgNewSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PreKeyMsgNewCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (PreKeyMsgNewEnv x)⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.preKeyMsgNewSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜PreKeyMsgNewEnv x evs⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.preKeyMsgNewSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Relocatable `[LibsignalPlacement]` budget-threaded `PreKeySignalMessage::new` contract (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
@[expose] def preKeyMsgNewSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (PreKeyMsgNewCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (PreKeyMsgNewEnv x) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.preKeyMsgNewSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜PreKeyMsgNewEnv x evs⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.preKeyMsgNewSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded `drop_glue::<CiphertextMessage>` contract (`FreeOnlyEvs`, `0` `FitsEnv`). -/
@[expose] def cmDropSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × CiphertextMessage × M.σ) where
  pre := fun (p, m, st) s =>
    ⌜LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.cmDropSpec
        (A.atState lim st s)).pre (p, m) s
  post := fun (p, m, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜FreeOnlyEvs evs⌝ ∗
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.cmDropSpec
        (A.atState lim (M.stepEvents evs st) sf)).post (p, m) s0 sf

/-! ## `PhaseCreditSpec` Bounds and Non-Vacuity Witnesses -/

@[expose] def kyberPayloadLen : Option KyberPayload → Nat
  | none => 0
  | some k => k.ciphertext.length

theorem kyberOptEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ct : Option (List (BitVec 8))) :
    let n := (ct.map List.length).getD 0
    PhaseCreditSpec M (KyberOptEnv ct) (2 * n + 9539) (n + 8195) (n + 8195) n := by
  cases ct with
  | none =>
    dsimp only [KyberOptEnv, Option.map, Option.getD]
    exact (PhaseCreditSpec.nil M).mono (by decide) (by decide) (by decide) (by decide)
  | some bs =>
    dsimp only [KyberOptEnv, Option.map, Option.getD]
    exact (PhaseCreditSpec.or_of_imp
      (fun _ h => h.elim (fun h1 => Or.inl h1.2) (fun h2 => Or.inr h2.2))
      (PhaseCreditSpec.nil M)
      (PhaseCreditSpec.rustAlloc_aff hM (req := bs.length) (al := 1) (by decide))).mono
      (by omega) (by omega) (by omega) (by omega)

theorem preKeyMsgNewRawEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (kp : Option KyberPayload) (smLen outLen : Nat) :
    let kL := kyberPayloadLen kp
    PhaseCreditSpec M (PreKeyMsgNewRawEnv kp smLen outLen)
      (2 * kL + 2 * smLen + 2 * outLen + 47827)
      (kL + smLen + outLen + 41041)
      (kL + smLen + outLen + 41041)
      (max (max kL 33) (max smLen outLen)) := by
  dsimp only [PreKeyMsgNewRawEnv, preKeyMsgNewRawEvents, preKeyMsgNewRawPrologueEvents]
  set kL := kyberPayloadLen kp
  have hky : PhaseCreditSpec M (· = kyberCopyEvs kp)
      (2 * kL + 9539) (kL + 8195) (kL + 8195) kL := by
    cases kp with
    | none =>
      dsimp only [kyberCopyEvs, kL, kyberPayloadLen]
      exact (PhaseCreditSpec.nil M).mono (by decide) (by decide) (by decide) (by decide)
    | some k =>
      dsimp only [kyberCopyEvs, kL, kyberPayloadLen]
      by_cases he : k.ciphertext = []
      · simp only [he, ↓reduceIte, List.length_nil]
        exact (PhaseCreditSpec.nil M).mono (by decide) (by decide) (by decide) (by decide)
      · simp only [he, ↓reduceIte]
        exact PhaseCreditSpec.rustAlloc_aff hM (req := k.ciphertext.length) (al := 1) (by decide)
  have h33 := PhaseCreditSpec.rustAlloc_aff hM (req := 33) (al := 1) (by decide)
  have hsm := PhaseCreditSpec.rustAlloc_aff hM (req := smLen) (al := 1) (by decide)
  have hout := PhaseCreditSpec.rustAlloc_aff hM (req := outLen) (al := 1) (by decide)
  have hkyd : PhaseCreditSpec M (· = kyberDeallocEvs kp) 0 0 0 0 := by
    cases kp with
    | none => simpa [kyberDeallocEvs] using PhaseCreditSpec.nil M
    | some k =>
      dsimp only [kyberDeallocEvs]
      by_cases he : k.ciphertext = []
      · simpa [he] using PhaseCreditSpec.nil M
      · simpa [he] using PhaseCreditSpec.rustDealloc hM.freeNonInc k.ciphertext.length 1
  have hd33 := PhaseCreditSpec.rustDealloc hM.freeNonInc 33 1
  have hdsm := PhaseCreditSpec.rustDealloc hM.freeNonInc smLen 1
  have hp :=
    phaseCredit_eq_append_sym
      (phaseCredit_eq_append_sym
        (phaseCredit_eq_append_sym
          (phaseCredit_eq_append_sym
            (phaseCredit_eq_append_sym
              (phaseCredit_eq_append_sym hky (phaseCredit_eq_append_sym h33 h33)) hsm) hout)
          hkyd) (phaseCredit_eq_append_sym hd33 hd33)) hdsm
  exact hp.mono (by omega) (by omega) (by omega) (by omega)

/-- Explicit serialized length bound for `PreKeySignalMessage.new` with `u32` IDs `< 128`
    (avoids reducing well-founded `Prost.varint` via `decide`). -/
theorem preKeySignalMessage_new_small_length_le (ver : BitVec 8) (regId : BitVec 32)
    (preKeyId : Option (BitVec 32)) (spk : BitVec 32)
    (kp : Option CryptoGames.LibsignalSessionApi.KyberPayload)
    (baseKey : CryptoGames.LibsignalSession.PublicKey)
    (ik : CryptoGames.LibsignalSession.IdentityKey)
    (msg : CryptoGames.LibsignalSession.SignalMessage)
    (hreg : regId.toNat < 128)
    (hpk : ∀ v, preKeyId = some v → v.toNat < 128)
    (hspk : spk.toNat < 128)
    (hkid : ∀ k, kp = some k → k.preKeyId.toNat < 128) :
    (CryptoGames.LibsignalSessionApi.PreKeySignalMessage.new
      ver regId preKeyId spk kp baseKey ik msg).serialized.length ≤
      2 * msg.serialized.length + 2 * kyberPayloadLen kp + 149 := by
  have u32_small (tag : Nat) (ht : tag ≤ 15) (v : Option (BitVec 32))
      (hv : ∀ x, v = some x → x.toNat < 128) :
      (CryptoGames.LibsignalSessionApi.Prost.uint32Field tag v).length ≤ 2 := by
    cases v with
    | none => simp [CryptoGames.LibsignalSessionApi.Prost.uint32Field]
    | some x =>
      simp only [CryptoGames.LibsignalSessionApi.Prost.uint32Field, List.length_append,
        CryptoVerification.LibsignalPublicApi.MessageEncrypt.key_length tag 0 ht (by omega)]
      have h1 := CryptoVerification.LibsignalPublicApi.MessageEncrypt.varint_length_le x.toNat
      have h2 := hv x rfl
      omega
  have hbk : baseKey.serialize.length = 33 := by
    simp [CryptoGames.LibsignalSession.PublicKey.serialize, List.Vector.toList_length]
  have hik : ik.serialize.length = 33 := by
    simp [CryptoGames.LibsignalSession.IdentityKey.serialize,
      CryptoGames.LibsignalSession.PublicKey.serialize, List.Vector.toList_length]
  have f1 := u32_small 1 (by omega) preKeyId hpk
  have f2 := CryptoVerification.LibsignalPublicApi.MessageEncrypt.bytesField_length_le 2 (by omega) baseKey.serialize
  have f3 := CryptoVerification.LibsignalPublicApi.MessageEncrypt.bytesField_length_le 3 (by omega) ik.serialize
  have f4 := CryptoVerification.LibsignalPublicApi.MessageEncrypt.bytesField_length_le 4 (by omega) msg.serialized
  have f5 := u32_small 5 (by omega) (some regId) (by rintro _ ⟨⟩; exact hreg)
  have f6 := u32_small 6 (by omega) (some spk) (by rintro _ ⟨⟩; exact hspk)
  have f7 := u32_small 7 (by omega) (kp.map (·.preKeyId)) (by
    cases kp with
    | none => rintro _ ⟨⟩
    | some k => rintro _ ⟨⟩; exact hkid k rfl)
  have f8 : (CryptoGames.LibsignalSessionApi.Prost.bytesField 8 (kp.map (·.ciphertext))).length ≤
      2 * kyberPayloadLen kp + 2 := by
    cases kp with
    | none => simp [CryptoGames.LibsignalSessionApi.Prost.bytesField, kyberPayloadLen]
    | some k =>
      have := CryptoVerification.LibsignalPublicApi.MessageEncrypt.bytesField_length_le 8 (by omega) k.ciphertext
      simp only [Option.map_some, kyberPayloadLen]
      omega
  simp only [CryptoGames.LibsignalSessionApi.PreKeySignalMessage.new,
    CryptoGames.LibsignalSessionApi.ProtoPreKeySignalMessage.encode,
    List.length_cons, List.length_append]
  omega

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
