/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSpe2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Version-Mismatch Closure Constants and Allocator Bridges

Symbol aliases, program equivalences (`contractProg = tripleRatchetProgAtExt`), the `.bss`
`MAX_LOG_LEVEL_FILTER` cell (`pqLogLevelCell`), and 4 KiB-to-16 KiB external-contract bridges
(`AllocContractsMem4K` to `AllocContractsX`) for the CLI PQXDH responder closure
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}` on the `msgVer ≠ 4` path.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

abbrev closureSymName : String :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName

abbrev pqxdhLogClosureSym : String :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName

abbrev growOneSpeSym : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one"

abbrev dropSessionStructure3Sym : String :=
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name

abbrev dropSpe2Sym : String :=
  CryptoVerification.Cli.dropSpe2Name

section Alloc33b0

open SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end Alloc33b0

section Mem4KToX

open SepProp CryptoGames.LibsignalSession CryptoVerification.LibsignalSessionRepr

private theorem subroutine_ok_conseq_pure {α : Type} {P : Program} {addr : BitVec 64}
    {s1 s2 : Spec α} (h : subroutine_ok P addr s1)
    (hpre : ∀ x R s0, s0.mem ⊨ s2.pre x s0 ∗ R → s0.mem ⊨ s1.pre x s0 ∗ R)
    (hpost : ∀ x R s0 sf, sf.mem ⊨ s1.post x s0 sf ∗ R → sf.mem ⊨ s2.post x s0 sf ∗ R)
    (hpan : ∀ x s0 sf, s1.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, s1.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, s1.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P addr s2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hal => ?_
  refine h.mono_outcome x R s0 hpc hrun (hpre x R s0 hp) hal ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hp'⟩ | ⟨code, _, he'⟩ | ⟨_, ho'⟩)
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hq⟩
  · rw [hpan x s0 sf, satisfies_pure_sepConj] at hp'; exact False.elim hp'.1
  · rw [hex x code s0 sf, satisfies_pure_sepConj] at he'; exact False.elim he'.1
  · rw [hoom x s0 sf, satisfies_pure_sepConj] at ho'; exact False.elim ho'.1

private theorem subroutine_ok_stack_mono {α : Type} {P : Program} {addr : BitVec 64}
    {base : Spec α} {s1 s2 : Nat} (h : subroutine_ok P addr (withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P addr (withStack base s2) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (withStack base s1).pre x s0 ∗ R' := by
    dsimp only [withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [withStack] at hp; rw [hpan x s0 sf, satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [withStack] at he; rw [hex x code s0 sf, satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [withStack] at ho; rw [hoom x s0 sf, satisfies_pure_sepConj] at ho
    exact False.elim ho.1

private theorem sessionMemcpy_mono {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemcpySpec allocHookStack))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    subroutine_ok P addr (sessionMemcpySpec stk) := by
  have h1 : subroutine_ok P addr (withStack sessionMemcpyRegionSpec allocHookStack) :=
    subroutine_ok_conseq_pure hh
      (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
        sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
      (fun _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
        sessionMemcpyRegionSpec, sepConj_assoc] using hq)
  have h2 := subroutine_ok_stack_mono h1 hle hmax
  exact subroutine_ok_conseq_pure h2
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)

private theorem libcMemcpy_of_session {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemcpySpec stk)) :
    subroutine_ok P addr (libcMemcpySpec stk) :=
  subroutine_ok_conseq_pure hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)

private theorem sessionMemmove_mono {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemmoveSpec allocHookStack))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    subroutine_ok P addr (sessionMemmoveSpec stk) := by
  let base : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
    { pre := fun (b, buf, dst, src, len) s0 =>
        ⌜s0.readReg64 .x0 = b + BitVec.ofNat 64 dst ∧
         s0.readReg64 .x1 = b + BitVec.ofNat 64 src ∧
         (s0.readReg64 .x2).toNat = len ∧
         dst + len ≤ buf.length ∧ src + len ≤ buf.length⌝ ∗ (b ↦ₛ buf)
      post := fun (b, buf, dst, src, len) s0 sf =>
        ⌜sf.readReg64 .x0 = b + BitVec.ofNat 64 dst ∧ sf.trace = s0.trace⌝ ∗
          (b ↦ₛ listMove buf dst src len) }
  have h1 : subroutine_ok P addr (withStack base allocHookStack) :=
    subroutine_ok_conseq_pure hh
      (fun _ _ _ hp => by simpa only [sessionMemmoveSpec, libcMemmoveSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ hq => by simpa only [sessionMemmoveSpec, withStack, base,
        sepConj_assoc] using hq)
  have h2 := subroutine_ok_stack_mono h1 hle hmax
  exact subroutine_ok_conseq_pure h2
    (fun _ _ _ hp => by simpa only [sessionMemmoveSpec, libcMemmoveSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ hq => by simpa only [sessionMemmoveSpec, withStack, base,
      sepConj_assoc] using hq)

private theorem libcMemmove_of_session {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemmoveSpec stk)) :
    subroutine_ok P addr (libcMemmoveSpec stk) :=
  subroutine_ok_conseq_pure hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      simp only [sessionMemmoveSpec, libcMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)

private theorem sessionMemset_mono {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemsetSpec allocHookStack))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    subroutine_ok P addr (sessionMemsetSpec stk) := by
  let base : Spec (BitVec 64 × BitVec 8 × Nat) :=
    { pre := fun (ptr, c, len) s0 =>
        ⌜s0.readReg64 .x0 = ptr ∧ (s0.readReg32 .x1).truncate 8 = c ∧
         (s0.readReg64 .x2).toNat = len⌝ ∗ memRegion ptr len
      post := fun (ptr, c, len) s0 sf =>
        ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c) }
  have h1 : subroutine_ok P addr (withStack base allocHookStack) :=
    subroutine_ok_conseq_pure hh
      (fun _ _ _ hp => by simpa only [sessionMemsetSpec, libcMemsetSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack, base,
        sepConj_assoc] using hq)
  have h2 := subroutine_ok_stack_mono h1 hle hmax
  exact subroutine_ok_conseq_pure h2
    (fun _ _ _ hp => by simpa only [sessionMemsetSpec, libcMemsetSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack, base,
      sepConj_assoc] using hq)

private theorem libcMemset_of_session {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemsetSpec stk)) :
    subroutine_ok P addr (libcMemsetSpec stk) :=
  subroutine_ok_conseq_pure hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      simp only [sessionMemsetSpec, libcMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)

end Mem4KToX

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
