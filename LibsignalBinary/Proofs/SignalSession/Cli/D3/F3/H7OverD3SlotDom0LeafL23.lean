/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget
import LibsignalBinary.Proofs.PeakBudget.W4InnerPeakSpec
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget

/-!
# `clearPending` Protobuf Length Monotonicity and Session-Cap `VerNe` Upgrade

Clearing optional pending pre-key fields (`clearPending`) drops only protobuf fields `9` and `14`
in `encSession`, preserving LEB128 record-length bounds below `2 ^ 64`. Combined with the `2 MiB`
session-store cap (`sessionCapBytes = 2 ^ 21`), this embeds `PromoteOverArchiveCanonSessEnv` into
`W4BinaryArchiveDirectEnv` and upgrades `VerNeTightTopRawEnv` to `VerNeTightTopEnv`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL23

open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Record
  (bytesField encPendingKyber encPendingPreKey encReceiverChain encSenderChain encSession
   encodeRecord lenField msgField uint32Field)
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliKitStk cliPollSessKitPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W4BinaryArchiveDirectEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BoundedEvs nonFreeCount)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
  (VerNeSessionCancelEnv VerNeSessionCancelRawEnv VerNeTightTopEnv VerNeTightTopRawEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (deserCancelFineMaxReq)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
  (PromoteOverArchiveCanonSessEnv)

/-! ## 1. Statements -/

/-- Clearing pending pre-key fields does not exceed the serialized outer `SessionRecord` byte
length when `r.currentSession = some s_old`. -/
@[expose] def h7l2_Stmt : Prop :=
  ∀ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
    r.currentSession = some s_old →
    (encSession (clearPending s_old)).length ≤ (encodeRecord r).length

/-- Under `CliPqOrD3RecvDom` and `F = runFiles i`, any `SessionRecord` `r` loaded via
`cliPollSessKitPlaced` with `r.currentSession = some s_old` satisfies
`(encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21`. -/
@[expose] def h7l3_Stmt : Prop :=
  ∀ [LibsignalPlacement] (A : RustAlloc) (P : PEParams) (B : RunBudgets)
    {i : Inputs} {F : FsFiles} {peer : AddrGhost}
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))},
    CliPqOrD3RecvDom P i →
    F = runFiles i →
    (cliPollSessKitPlaced A F scopeKit peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r)) →
    r.currentSession = some s_old →
    (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21

/-! ## 2. Pure Protobuf and `clearPending` Length Monotonicity -/

private theorem h7l23_encSession_clearPending_le (s : Session (List (BitVec 8))) :
    (encSession (clearPending s)).length ≤ (encSession s).length := by
  unfold encSession clearPending
  dsimp only [Option.map, msgField]
  simp only [List.length_append, List.length_nil]
  omega

private theorem h7l23_lenField_length_ge (tag : Nat) (b : List (BitVec 8)) :
    b.length ≤ (lenField tag b).length := by
  unfold lenField
  simp only [List.length_append]
  omega

theorem h7l23_encSession_clearPending_le_encodeRecord
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (hcur : r.currentSession = some s_old) :
    (encSession (clearPending s_old)).length ≤ (encodeRecord r).length := by
  have h1 := h7l23_encSession_clearPending_le s_old
  have h2 : (encSession s_old).length ≤ (encodeRecord r).length := by
    unfold encodeRecord
    rw [hcur]
    dsimp only [Option.map, msgField]
    exact h7l23_lenField_length_ge 1 (encSession s_old)
  exact Nat.le_trans h1 h2

private theorem h7l23_encodeVarintAux_length_mono :
    ∀ (k : Nat) {v₁ v₂ : BitVec 64}, v₁.toNat ≤ v₂.toNat →
      (encodeVarintAux k v₁).length ≤ (encodeVarintAux k v₂).length
  | 0, _, _, _ => by simp [encodeVarintAux]
  | k + 1, v₁, v₂, hle => by
    unfold encodeVarintAux
    split
    · split <;> simp
    · rename_i h₁
      split
      · rename_i h₂
        omega
      · simp only [List.length_cons]
        have hsh : (v₁ >>> 7).toNat ≤ (v₂ >>> 7).toNat := by
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
            Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
          exact Nat.div_le_div_right hle
        have ih := h7l23_encodeVarintAux_length_mono k hsh
        omega

/-- LEB128 varint length monotonicity below `2 ^ 64`: when `a ≤ b < 2 ^ 64`,
`(encodeVarint (BitVec.ofNat 64 a)).length ≤ (encodeVarint (BitVec.ofNat 64 b)).length`. -/
theorem h7l23_encodeVarint_ofNat_length_mono {a b : Nat}
    (hle : a ≤ b) (hlt : b < 2 ^ 64) :
    (encodeVarint (BitVec.ofNat 64 a)).length ≤ (encodeVarint (BitVec.ofNat 64 b)).length := by
  unfold encodeVarint
  apply h7l23_encodeVarintAux_length_mono 10
  simp only [BitVec.toNat_ofNat]
  omega

private theorem h7l23_lenField_length_mono {tag : Nat} {b₁ b₂ : List (BitVec 8)}
    (hle : b₁.length ≤ b₂.length) (hlt : b₂.length < 2 ^ 64) :
    (lenField tag b₁).length ≤ (lenField tag b₂).length := by
  unfold lenField
  simp only [List.length_append]
  have hv := h7l23_encodeVarint_ofNat_length_mono hle hlt
  omega

/-- Record-level `clearPending` length monotonicity below `2 ^ 64`: when `r.currentSession = some s_old`
and `(encodeRecord r).length < 2 ^ 64`, `(encodeRecord ⟨some (clearPending s_old)⟩).length ≤
(encodeRecord r).length`. -/
theorem h7l23_encodeRecord_clearPending_le_encodeRecord
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (hcur : r.currentSession = some s_old)
    (hlt : (encodeRecord r).length < 2 ^ 64) :
    (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ (encodeRecord r).length := by
  have h1 := h7l23_encSession_clearPending_le s_old
  have h2 : (encSession s_old).length ≤ (encodeRecord r).length := by
    unfold encodeRecord
    rw [hcur]
    dsimp only [Option.map, msgField]
    exact h7l23_lenField_length_ge 1 (encSession s_old)
  have hb_lt : (encSession s_old).length < 2 ^ 64 := Nat.lt_of_le_of_lt h2 hlt
  unfold encodeRecord
  rw [hcur]
  dsimp only [Option.map, msgField]
  exact h7l23_lenField_length_mono h1 hb_lt

/-! ## 3. `PromoteOverArchiveCanonSessEnv ⊆ W4BinaryArchiveDirectEnv` -/

/-! ## 4. Session-File `2 MiB` Cap and `VerNe` Raw-to-Tight Upgrade -/

/-- Any `SessionRecord` `r` loaded from `StoresGhost.opened.sessions` via `cliPollSessKitPlaced`
satisfies `(encodeRecord r).length ≤ sessionCapBytes` (`= 2 ^ 21`). -/
theorem h7l23_loadRel_encodeRecord_le_sessionCap_of_loadRel [LibsignalPlacement]
    {A : RustAlloc} {F : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {r : SessionRecord (List (BitVec 8))}
    (hload : (cliPollSessKitPlaced A F scopeKit peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r))) :
    (encodeRecord r).length ≤ sessionCapBytes := by
  obtain ⟨bs, hget, hans⟩ := hload
  have hbs : bs.length ≤ sessionCapBytes :=
    cliIo_rd_ok_length_le_sessionCapBytes F _ bs hget
  cases bs with
  | nil => cases hans
  | cons b₀ bs' =>
    obtain ⟨r', hr', henc, _⟩ := hans
    injection hr' with hr'
    injection hr' with hr'
    subst hr'
    rw [henc]
    exact hbs

theorem h7l23_loadRel_encodeRecord_le_sessionCap [LibsignalPlacement]
    {A : RustAlloc} {P : PEParams} {B : RunBudgets}
    {i : Inputs} {F : FsFiles} {peer : AddrGhost}
    {r : SessionRecord (List (BitVec 8))}
    (_hi : CliPqOrD3RecvDom P i)
    (_hfiles : F = runFiles i)
    (hload : (cliPollSessKitPlaced A F scopeKit peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r))) :
    (encodeRecord r).length ≤ sessionCapBytes :=
  h7l23_loadRel_encodeRecord_le_sessionCap_of_loadRel hload

theorem h7l23_encodeRecord_clearPending_le_cap [LibsignalPlacement]
    (A : RustAlloc) (P : PEParams) (B : RunBudgets)
    {i : Inputs} {F : FsFiles} {peer : AddrGhost}
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (hi : CliPqOrD3RecvDom P i)
    (hfiles : F = runFiles i)
    (hload : (cliPollSessKitPlaced A F scopeKit peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old) :
    (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21 := by
  have hr_cap : (encodeRecord r).length ≤ sessionCapBytes :=
    h7l23_loadRel_encodeRecord_le_sessionCap hi hfiles hload
  have hcap_eq : sessionCapBytes = 2 ^ 21 := rfl
  have hr_lt : (encodeRecord r).length < 2 ^ 64 := by
    rw [hcap_eq] at hr_cap
    omega
  have hmono : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ (encodeRecord r).length :=
    h7l23_encodeRecord_clearPending_le_encodeRecord hcur hr_lt
  rw [hcap_eq] at hr_cap
  exact Nat.le_trans hmono hr_cap

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL23
