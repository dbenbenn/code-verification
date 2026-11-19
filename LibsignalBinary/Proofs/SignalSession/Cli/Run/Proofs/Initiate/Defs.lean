/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Shared Definitions and Cut-Point Invariants for `signal_session_handshake::initiate`

Defines program/PC shorthands (`initProg`, `initProgExt`), stack-budget bounds, empty-scope
`SessionRecord::deserialize` discharge, accepted-call `StoresGhost` updates, the monotonic coin
cursor `coinsCursorAt`, and CFG cut-point invariants (`AtInitEntry`, `AtStage2`..`AtStage5`, and
their `*Ext` counterparts).
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## Program and symbolic PC definitions -/

/-- Shared OOM postcondition matching `(initSlotSpec A img S stk).onOom`. -/
@[expose] def initOom (_s0 : State) : State → SepProp :=
  fun _ => ⌜False⌝

/-- Size of `initiate`'s local stack area `[fsp, s0.sp - 0x60)`: `0x1000 + 0xc90 = 7312` bytes. -/
abbrev initLocalsSize : Nat := 0x1000 + 0xc90

/-! ## Stack budget arithmetic -/

theorem cliInitiateFrame_eq : cliInitiateFrame = 7408 := rfl

theorem initLocalsSize_add_saved : initLocalsSize + 0x60 = cliInitiateFrame := rfl

theorem cliInitiateFrame_dvd16 : 16 ∣ cliInitiateFrame := by decide

theorem stk_ge_frame {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    cliInitiateFrame ≤ stk := by
  unfold cliInitiateNeed at hstk
  unfold cliInitiateFrame at hstk ⊢
  omega

theorem stk_sub_ge_base {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    516880 ≤ stk - cliInitiateFrame := by
  unfold cliInitiateNeed at hstk
  unfold cliInitiateFrame at hstk ⊢
  omega

theorem stk_sub_ge_dirGet {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    848 + B.dirGetNeed ≤ stk - cliInitiateFrame := by
  unfold cliInitiateNeed at hstk
  unfold cliInitiateFrame at hstk ⊢
  omega

theorem sessLoadPoll_stk_le {B : RunBudgets} {addrStk stk : Nat}
    (haddr : addrStk ≤ 65536) (hstk : cliInitiateNeed B ≤ stk) :
    0x350 + max (max addrStk B.dirGetNeed) (max E2E.Record.recDeserializeStack extHookStack) ≤
      stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hrec : E2E.Record.recDeserializeStack ≤ 65536 := by decide
  have hext : extHookStack ≤ 65536 := by decide
  omega

/-! ## Empty-scope `SessionRecord::deserialize` discharge -/

theorem sessFileWf_false_of_nil : SessFileWf (fun _ => False) [] :=
  Or.inl rfl

/-- Final `StoresGhost` produced on an accepted `initiate` call. -/
@[expose] def initAcceptStoresGhost (F : FsFiles) (peer : AddrVal) (idKey : IdentityKey)
    (recBytes : List (BitVec 8)) : StoresGhost :=
  let g := StoresGhost.opened
  { g with
    identity := g.identity.saveUpd cliIo.rd F peer idKey
    sessions := g.sessions.put (addressText peer) recBytes }

theorem initAcceptStoresGhost_writes_cliWrOk {W : PEParams} {F : FsFiles}
    {peer me : AddrVal} (hok : InitOk₀ W F peer me) (idKey : IdentityKey)
    (recBytes : List (BitVec 8)) :
    ∀ pw ∈ (initAcceptStoresGhost F peer idKey recBytes).writes, cliWrOk pw.1 := by
  intro pw hpw
  rw [initAcceptStoresGhost] at hpw
  rw [IdGhost.saveUpd] at hpw
  split at hpw
  · simp only [StoresGhost.writes, StoresGhost.opened, DirGhost.new, DirGhost.put,
      DirGhost.setOrPush, DirGhost.writes, List.map, List.nil_append, List.append_nil,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hpw
    rcases hpw with rfl | rfl
    · exact ⟨hok.idPathOk, hok.idPathLt⟩
    · exact ⟨hok.sessPathOk, hok.sessPathLt⟩
  · simp only [StoresGhost.writes, StoresGhost.opened, DirGhost.new, DirGhost.put,
      DirGhost.setOrPush, DirGhost.writes, List.map, List.nil_append, List.append_nil,
      List.mem_singleton] at hpw
    subst hpw
    exact ⟨hok.sessPathOk, hok.sessPathLt⟩

/-! ## Coin cursor invariant -/

/-- The 12 callee-saved words stored by `initiate`'s prologue at `s0.sp - 0x60`. -/
@[expose] def initSaved (s0 : State) : SepProp :=
  let b := s0.sp - 0x60#64
  let w (k : Nat) (r : Reg) := (b + BitVec.ofNat 64 k) ↦₆₄ s0.readReg64 r
  w 0x00 .fp ∗ w 0x08 .lr ∗ w 0x10 (.gpr 28#5) ∗ w 0x18 (.gpr 27#5) ∗ w 0x20 (.gpr 26#5) ∗
    w 0x28 (.gpr 25#5) ∗ w 0x30 (.gpr 24#5) ∗ w 0x38 (.gpr 23#5) ∗ w 0x40 (.gpr 22#5) ∗
    w 0x48 (.gpr 21#5) ∗ w 0x50 (.gpr 20#5) ∗ w 0x58 (.gpr 19#5)

/-- Empty/fresh `SessionRecord` header at `[fsp + 0x128, fsp + 0x148)` under `InitOk₀.noSession`. -/
@[expose] def initFreshRecAt (fsp : BitVec 64) : SepProp :=
  ((fsp + 0x128#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
    ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64)

@[expose] def stage3KeySlotsAt (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32) : SepProp :=
  let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
  ((fsp + 0x298#64) ↦ₛ ekAPk) ∗
    memRegion (fsp + 0x2b8#64) 0x48 ∗
    ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
    memRegion (fsp + 0x308#64) 0x40 ∗
    ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
    ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
    ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
    ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
    ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
    ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
    ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
    ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
    A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
    ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
    (match b.opk with
     | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
     | none => memRegion (fsp + 0x439#64) 32) ∗
    ((fsp + 0x459#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x45a#64) 6

/-- Any `HookSat ext name spec` on a non-I/O symbol under `CliExternsOk` lifts to `spec.keepsFs`. -/
theorem hookSat_keepsFs_of_ok {α : Type} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {name : String} {spec : Spec α}
    (hOk : CliExternsOk P A ext) (hnio : name ∉ CliExt.ioNames)
    (hsat : HookSat ext name spec) :
    HookSat ext name spec.keepsFs := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hok.keepsFs (hOk.fsKept name f hf hnio)⟩

private theorem quietEv_false_of_isFsChange (e : TraceEvent)
    (h : e.isFsChange = true) : ¬ QuietEv e := by
  cases e with
  | writeByte st _ => cases st <;> simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢
  | _ => simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢

private theorem hookFsTraced_panicked :
    HookFsTraced (fun e => e.isFsChange = true) Rust.panicked := by
  intro s
  exact ⟨[], by simp [Rust.panicked], fun _ => rfl⟩

private theorem externAt_fsTraced_local {prog : Program}
    (hX : ∀ n f, prog.externs n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    (hO : ∀ n f, prog.overrides n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    {pc : BitVec 64} {f : State → State} (h : prog.externAt? pc = some f) :
    HookFsTraced (fun e => e.isFsChange = true) f := by
  unfold Program.externAt? Program.hookAtOff? at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hX n f hno
    · cases hno
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hO n f hno
    · cases hno

theorem idTrustPoll_eqStk_fits :
    192 + (64 + extHookStack) ≤ 516880 := by
  dsimp only [extHookStack]; decide

theorem idSavePoll_eqStk_fits :
    432 + (64 + extHookStack) ≤ 516880 := by
  dsimp only [extHookStack]; decide

theorem isSameAccount_eqStk_fits :
    208 + (64 + extHookStack) ≤ 516880 := by
  dsimp only [extHookStack]; decide

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
