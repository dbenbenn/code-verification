/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Hops -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Shared Call, Stack-Frame, and Semantic Helpers for Arm `R1b`

Symbol offsets, stack-budget bounds, generic `SepWPp` call/deallocation/`SignalProtocolError`-drop
combinators, `runLocals` (`0x29f0` B) focusing helpers, and bundle-path reject lemmas for Arm `R1b`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-! ## Symbol Offsets, Vtable Equations, and Callee Lemmas -/

structure r1b_StackBounds (B : RunBudgets) (resStack : Nat) : Prop where
  frame : runFrame ≤ resStack
  sub63 : resStack - runFrame ≤ 2 ^ 63
  sub64 : resStack - runFrame ≤ 2 ^ 64
  tryAlloc : finishGrowStackX ≤ resStack - runFrame
  readFile : B.readFile ≤ resStack - runFrame
  path : pathNeed ≤ resStack - runFrame
  bundleRead : B.bundleReadNeed ≤ resStack - runFrame
  splitId : splitIdNeed ≤ resStack - runFrame
  splitSigned : splitSignedNeed ≤ resStack - runFrame
  dropSpe : 32 + extHookStack ≤ resStack - runFrame
  hook : extHookStack ≤ resStack - runFrame
  kem : 48 + extHookStack ≤ resStack - runFrame

theorem r1b_stdout_eq_of_trace_eq {s sf : State}
    (htr : sf.trace = s.trace)
    (hout : Arm64.Process.ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    Arm64.Process.ProcessOutcome.traceStreamBytes .stdout sf.trace = [] := by
  rwa [htr]

theorem r1b_spAligned_of_fsp {s0 s : State}
    (hsp : s.sp = runFsp s0)
    (hsp0 : s0.spAligned = true) :
    s.spAligned = true := by
  have hs0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using hsp0
  have hfsp : (s0.sp - 0x2a50#64) &&& 15#64 = 0#64 := by
    bv_bits
  simp only [State.spAligned, hsp, runFsp, hfsp, beq_self_eq_true]

@[expose] def r1b_localsBound : List (Nat × Nat × SepProp) → Nat
  | [] => runLocalBytes
  | (o, _, _) :: _ => o

def r1b_localsEnd (off : Nat) : List (Nat × Nat × SepProp) → Nat
  | [] => off
  | (o, n, _) :: cs => r1b_localsEnd (o + n) cs

@[expose] def r1b_localsCtx (fsp : BitVec 64) :
    Nat → List (Nat × Nat × SepProp) → Nat → Nat → List (Nat × Nat × SepProp) → SepProp
  | off, [], o, n, cs₂ =>
    memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ runLocalsFrom fsp (o + n) cs₂
  | off, (o₁, n₁, P₁) :: cs₁, o, n, cs₂ =>
    memRegion (fsp + BitVec.ofNat 64 off) (o₁ - off) ∗ P₁ ∗
      r1b_localsCtx fsp (o₁ + n₁) cs₁ o n cs₂

theorem r1b_localsFrom_focus (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp)
    (cs₂ : List (Nat × Nat × SepProp)) :
    runLocalsFrom fsp off (cs₁ ++ (o, n, P) :: cs₂) =
      P ∗ r1b_localsCtx fsp off cs₁ o n cs₂ := by
  induction cs₁ generalizing off with
  | nil =>
    simp only [List.nil_append, runLocalsFrom, r1b_localsCtx]
    ac_rfl
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, runLocalsFrom, r1b_localsCtx, ih (o₁ + n₁)]
    ac_rfl

theorem r1b_locals_focus (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp)
    (cs₂ : List (Nat × Nat × SepProp)) :
    runLocals fsp (cs₁ ++ (o, n, P) :: cs₂) =
      P ∗ r1b_localsCtx fsp 0 cs₁ o n cs₂ :=
  r1b_localsFrom_focus fsp 0 cs₁ o n P cs₂

theorem r1b_locals_mono_piece (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) {P Q : SepProp}
    (cs₂ : List (Nat × Nat × SepProp)) (hPQ : P ⊢ Q) :
    runLocals fsp (cs₁ ++ (o, n, P) :: cs₂) ⊢
      runLocals fsp (cs₁ ++ (o, n, Q) :: cs₂) := by
  rw [r1b_locals_focus fsp cs₁ o n P cs₂, r1b_locals_focus fsp cs₁ o n Q cs₂]
  exact sepConj_mono_left hPQ

theorem r1b_localsFrom_carve_region (fsp : BitVec 64) (off o n : Nat)
    (cs : List (Nat × Nat × SepProp))
    (hlo : off ≤ o)
    (hhi : o + n ≤ r1b_localsBound cs)
    (hbnd : r1b_localsBound cs ≤ runLocalBytes) :
    runLocalsFrom fsp off cs =
      runLocalsFrom fsp off ((o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs) := by
  have hrlb : runLocalBytes = 0x29f0 := rfl
  have hsplit1 :
      memRegion (fsp + BitVec.ofNat 64 off) (r1b_localsBound cs - off) =
        memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗
          memRegion (fsp + BitVec.ofNat 64 o) (r1b_localsBound cs - o) := by
    refine ProofLib.memRegion_split' (n := o - off) (k := r1b_localsBound cs - o)
      (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hsplit2 :
      memRegion (fsp + BitVec.ofNat 64 o) (r1b_localsBound cs - o) =
        memRegion (fsp + BitVec.ofNat 64 o) n ∗
          memRegion (fsp + BitVec.ofNat 64 (o + n)) (r1b_localsBound cs - (o + n)) := by
    refine ProofLib.memRegion_split' (n := n) (k := r1b_localsBound cs - (o + n))
      (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  cases cs with
  | nil =>
    simp only [r1b_localsBound] at hhi hbnd hsplit1 hsplit2
    simp only [runLocalsFrom, hsplit1, hsplit2]
  | cons c cs' =>
    rcases c with ⟨o', n', P'⟩
    simp only [r1b_localsBound] at hhi hbnd hsplit1 hsplit2
    simp only [runLocalsFrom, hsplit1, hsplit2]
    ac_rfl

private theorem r1b_localsFrom_carve_after (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1b_localsEnd off cs₁ ≤ o)
    (hhi : o + n ≤ r1b_localsBound cs₂)
    (hbnd : r1b_localsBound cs₂ ≤ runLocalBytes) :
    runLocalsFrom fsp off (cs₁ ++ cs₂) =
      runLocalsFrom fsp off (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) := by
  induction cs₁ generalizing off with
  | nil =>
    exact r1b_localsFrom_carve_region fsp off o n cs₂ hlo hhi hbnd
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, runLocalsFrom]
    rw [ih (o₁ + n₁) hlo]

theorem r1b_locals_carve_region (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1b_localsEnd 0 cs₁ ≤ o := by simp [r1b_localsEnd, MainHops.cell])
    (hhi : o + n ≤ r1b_localsBound cs₂ := by simp [r1b_localsBound, MainHops.cell, runLocalBytes])
    (hbnd : r1b_localsBound cs₂ ≤ runLocalBytes := by
      simp [r1b_localsBound, MainHops.cell, runLocalBytes]) :
    runLocals fsp (cs₁ ++ cs₂) =
      runLocals fsp (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) :=
  r1b_localsFrom_carve_after fsp 0 cs₁ o n cs₂ hlo hhi hbnd

theorem r1b_locals_carve_cell (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1b_localsEnd 0 cs₁ ≤ o := by simp [r1b_localsEnd, MainHops.cell])
    (hhi : o + 8 ≤ r1b_localsBound cs₂ := by simp [r1b_localsBound, MainHops.cell, runLocalBytes])
    (hbnd : r1b_localsBound cs₂ ≤ runLocalBytes := by
      simp [r1b_localsBound, MainHops.cell, runLocalBytes]) :
    runLocals fsp (cs₁ ++ cs₂) =
      ∃∗ v : BitVec 64, runLocals fsp (cs₁ ++ MainHops.cell fsp o v :: cs₂) := by
  rw [r1b_locals_carve_region fsp cs₁ o 8 cs₂ hlo hhi hbnd,
    r1b_locals_focus fsp cs₁ o 8 _ cs₂, ProofLib.memRegion_eight, sepExists_sepConj_left]
  congr 1; funext v
  exact (r1b_locals_focus fsp cs₁ o 8 _ cs₂).symm

theorem r1b_locals_forget_cell (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o : Nat) (v : BitVec 64)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1b_localsEnd 0 cs₁ ≤ o := by simp [r1b_localsEnd, MainHops.cell])
    (hhi : o + 8 ≤ r1b_localsBound cs₂ := by simp [r1b_localsBound, MainHops.cell, runLocalBytes])
    (hbnd : r1b_localsBound cs₂ ≤ runLocalBytes := by
      simp [r1b_localsBound, MainHops.cell, runLocalBytes]) :
    runLocals fsp (cs₁ ++ MainHops.cell fsp o v :: cs₂) ⊢ runLocals fsp (cs₁ ++ cs₂) := by
  rw [r1b_locals_carve_cell fsp cs₁ o cs₂ hlo hhi hbnd]
  exact Entails.sepExists_right v (Entails.refl _)

/-! ## Bundle-Path Bounds and `AtInit1` Reject Semantics -/

theorem r1b_bundlePath_eq (dir : Bytes) (name : String) :
    bundlePath dir name = dir ++ [0x2f#8] ++ utf8 name := rfl

theorem r1b_vecU8_14_intro (A : RustAlloc) (a buf : BitVec 64) (hbuf : buf ≠ 0#64) :
    ((a ↦₆₄ 14#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗ ((a + 16#64) ↦₆₄ 14#64) ∗
      A.live buf 14 1 ∗ memRegion buf 14) ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  rw [memRegion_eq_exists_bytes buf 14 (by decide)]
  rw [sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs
  have hcomm :
      ((a ↦₆₄ 14#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗ ((a + 16#64) ↦₆₄ 14#64) ∗
        A.live buf 14 1 ∗ (⌜bs.length = 14⌝ ∗ (buf ↦ₛ bs))) =
      (⌜bs.length = 14⌝ ∗ ((a ↦₆₄ 14#64) ∗ ((a + 8#64) ↦₆₄ buf) ∗
        ((a + 16#64) ↦₆₄ 14#64) ∗ A.live buf 14 1 ∗ (buf ↦ₛ bs))) := by
    ac_rfl
  rw [hcomm]
  apply Entails.pure_left
  intro hlen
  refine Entails.sepExists_right bs ?_
  dsimp only [vecU8, vecU8At, vecHeader]
  refine Entails.sepExists_right 14#64 ?_
  refine Entails.sepExists_right buf ?_
  have h14 : BitVec.ofNat 64 bs.length = 14#64 := by rw [hlen]
  have h14nat : (14#64 : BitVec 64).toNat = 14 := rfl
  have hne14 : (14#64 : BitVec 64) ≠ 0 := by decide
  have hsub : 14 - bs.length = 0 := by omega
  simp only [h14, hne14, ↓reduceIte, h14nat, hsub, memRegion_zero, sepConj_emp]
  have hpure : bs.length ≤ 14 ∧ 14 < 2 ^ 63 ∧ buf ≠ 0 :=
    ⟨by omega, by decide, hbuf⟩
  conv => rhs; rw [sepConj_comm (a ↦₆₄ 14#64 ∗ (a + 8#64) ↦₆₄ buf ∗ (a + 16#64) ↦₆₄ 14#64),
    sepConj_assoc]
  exact Entails.pure_right hpure (Entails.of_eq (by ac_rfl))

end CryptoVerification.SignalSession.Cli.RunCompose
