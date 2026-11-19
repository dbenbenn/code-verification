/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.Sep
import ProofLib.SepLogic.WPp
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

/-!
# `SignalMessage::new` Instruction Fetches & OOM Helpers

Instruction-decode theorems, `new_fetches_range` macro, `SepWPp` composition helpers, and
OOM panic-block lemmas (`+0x15c`, `+0x858`, `+0x864`, `+0x898`) for
`<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`, 556 instructions = 2224 bytes).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

end Fetch

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `SepWPp` composition helpers with allocator-failure panic postcondition -/

@[expose] def PanicAllocPost (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem panicAllocPost_of_eq {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    PanicAllocPost s0 sf P_f :=
  fun _ hm => allowPanic_panicked h hm

theorem allocFailedIn_of_append_one {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem signalMessageNew_seq_wpp {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hfoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hfoom).elim

theorem signalMessageNew_seq_wp {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  rcases h1.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, hfoom⟩⟩
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hfoom).elim

@[expose] def PanicAllocOrOverflowPost (ovf : Prop) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ ovf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem panicAllocOrOverflowPost_of_eq {ovf : Prop} {s0 sf : State} {P_f : SepProp}
    (h : (allocFailedIn s0 sf ∨ ovf) ∧ s0.trace <+: sf.trace) :
    PanicAllocOrOverflowPost ovf s0 sf P_f :=
  fun _ hm => allowPanic_panicked h hm

theorem panicAllocOrOverflowPost_of_overflow {ovf : Prop} {s0 sf : State} {P_f : SepProp}
    (hovf : ovf) (htr : sf.trace = s0.trace) :
    PanicAllocOrOverflowPost ovf s0 sf P_f :=
  panicAllocOrOverflowPost_of_eq ⟨Or.inr hovf, htr ▸ List.prefix_refl _⟩

theorem panicAllocOrOverflowPost_of_alloc {ovf : Prop} {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    PanicAllocOrOverflowPost ovf s0 sf P_f :=
  panicAllocOrOverflowPost_of_eq ⟨Or.inl h.1, h.2⟩

theorem signalMessageNew_seq_wpp_or {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {ovf : Prop} {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocOrOverflowPost ovf s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, ((allocFailedIn s0 sf ∨ ovf) ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hfoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : (allocFailedIn s0 sm ∨ ovf) ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hfoom).elim

theorem signalMessageNew_stackAt_split_bottom (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega,
    memRegion_split' (n := d) (k := n) (by omega) rfl (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem stackAt_split_top (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = stackAt (sp - BitVec.ofNat 64 d) n ∗ memRegion (sp - BitVec.ofNat 64 d) d := by
  simp only [stackAt]
  rw [memRegion_split' (n := n) (k := d) rfl rfl h]
  have e1 : sp - BitVec.ofNat 64 (n + d) = sp - BitVec.ofNat 64 d - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + d) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 d := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

/-- The 3 untouched stack padding slices inside `sp0 - 416#64 .. sp0 - 96#64` (52 bytes total). -/
@[expose] def newUnusedPad (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 416#64) 8 ∗
  memRegion (sp0 - 336#64) 4 ∗
  memRegion (sp0 - 136#64) 40

/-- Callee-saved registers stored at `sp0 - 96#64 .. sp0` by the prologue (`+0x004..+0x018`). -/
@[expose] def newSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem memRegion_cells' (a : BitVec 64) (n k : Nat) (h : n = 8 * k := by rfl)
    (hle : 8 * k ≤ 2 ^ 64 := by decide) :
    memRegion a n = cells a k :=
  h ▸ memRegion_cells a k hle

theorem stackAt_signalMessageNewStack_split (sp0 : BitVec 64) :
    stackAt sp0 signalMessageNewStack =
      stackAt (sp0 - 416#64) computeMacStack ∗
      newUnusedPad sp0 ∗
      cells (sp0 - 408#64) 3 ∗
      (∃∗ w384 : BitVec 32, (sp0 - 384#64) ↦₃₂ w384) ∗
      (∃∗ w380 : BitVec 32, (sp0 - 380#64) ↦₃₂ w380) ∗
      cells (sp0 - 376#64) 5 ∗
      (∃∗ w332 : BitVec 32, (sp0 - 332#64) ↦₃₂ w332) ∗
      cells (sp0 - 328#64) 2 ∗
      memRegion (sp0 - 312#64) 24 ∗
      cells (sp0 - 288#64) 12 ∗
      (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
      (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
      (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
      (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
      cells (sp0 - 176#64) 3 ∗
      memRegion (sp0 - 152#64) 16 ∗
      cells (sp0 - 96#64) 12 := by
  have htop := stackAt_split_top sp0 computeMacStack 416 (by decide)
  change stackAt sp0 signalMessageNewStack =
    stackAt (sp0 - 416#64) computeMacStack ∗ memRegion (sp0 - 416#64) 416 at htop
  rw [htop]
  congr 1
  unfold newUnusedPad
  sep_interval_eq

theorem signalMessageNew_stackAt_split_bottom' (sp : BitVec 64) (N n d : Nat) (hN : N = n + d := by decide)
    (h : n + d ≤ 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) d ∗ stackAt sp n :=
  hN ▸ signalMessageNew_stackAt_split_bottom sp n d h

theorem stackAt_computeMac_to_serializeAddresses (sp : BitVec 64) :
    stackAt sp computeMacStack = memRegion (sp - 4624#64) 400 ∗ stackAt sp serializeAddressesStack :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStack serializeAddressesStack 400

theorem stackAt_computeMac_to_publicKeySerialize (sp : BitVec 64) :
    stackAt sp computeMacStack = memRegion (sp - 4624#64) 496 ∗ stackAt sp publicKeySerializeStack :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStack publicKeySerializeStack 496

theorem stackAt_computeMac_to_allocHook (sp : BitVec 64) :
    stackAt sp computeMacStack = memRegion (sp - 4624#64) 528 ∗ stackAt sp allocHookStack :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStack allocHookStack 528

theorem stackAt_computeMac_to_encodedLen (sp : BitVec 64) :
    stackAt sp computeMacStack = memRegion (sp - 4624#64) 4608 ∗ stackAt sp encodedLenStack :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStack encodedLenStack 4608

theorem stackAt_computeMac_to_encodeVarint (sp : BitVec 64) :
    stackAt sp computeMacStack = memRegion (sp - 4624#64) 368 ∗ stackAt sp encodeVarintStack :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStack encodeVarintStack 368

theorem stackAt_signalMessageNew_to_allocHook (sp0 : BitVec 64) :
    stackAt sp0 signalMessageNewStack = memRegion (sp0 - 5040#64) 944 ∗ stackAt sp0 allocHookStack :=
  signalMessageNew_stackAt_split_bottom' sp0 signalMessageNewStack allocHookStack 944

/-! ## Extended-hook (`extHookStack`) stack split lemmas -/

theorem stackAt_signalMessageNewStackX_split (sp0 : BitVec 64) :
    stackAt sp0 signalMessageNewStackX =
      stackAt (sp0 - 416#64) computeMacStackX ∗
      newUnusedPad sp0 ∗
      cells (sp0 - 408#64) 3 ∗
      (∃∗ w384 : BitVec 32, (sp0 - 384#64) ↦₃₂ w384) ∗
      (∃∗ w380 : BitVec 32, (sp0 - 380#64) ↦₃₂ w380) ∗
      cells (sp0 - 376#64) 5 ∗
      (∃∗ w332 : BitVec 32, (sp0 - 332#64) ↦₃₂ w332) ∗
      cells (sp0 - 328#64) 2 ∗
      memRegion (sp0 - 312#64) 24 ∗
      cells (sp0 - 288#64) 12 ∗
      (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
      (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
      (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
      (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
      cells (sp0 - 176#64) 3 ∗
      memRegion (sp0 - 152#64) 16 ∗
      cells (sp0 - 96#64) 12 := by
  have htop := stackAt_split_top sp0 computeMacStackX 416 (by decide)
  change stackAt sp0 signalMessageNewStackX =
    stackAt (sp0 - 416#64) computeMacStackX ∗ memRegion (sp0 - 416#64) 416 at htop
  rw [htop]
  congr 1
  unfold newUnusedPad
  sep_interval_eq

theorem stackAt_computeMacX_to_serializeAddressesX (sp : BitVec 64) :
    stackAt sp computeMacStackX = memRegion (sp - 16912#64) 128 ∗ stackAt sp serializeAddressesStackX :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStackX serializeAddressesStackX 128

theorem stackAt_computeMacX_to_publicKeySerializeX (sp : BitVec 64) :
    stackAt sp computeMacStackX = memRegion (sp - 16912#64) 496 ∗ stackAt sp publicKeySerializeStackX :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStackX publicKeySerializeStackX 496

theorem stackAt_computeMacX_to_extHook (sp : BitVec 64) :
    stackAt sp computeMacStackX = memRegion (sp - 16912#64) 528 ∗ stackAt sp extHookStack :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStackX extHookStack 528

theorem stackAt_computeMacX_to_encodedLen (sp : BitVec 64) :
    stackAt sp computeMacStackX = memRegion (sp - 16912#64) 16896 ∗ stackAt sp encodedLenStack :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStackX encodedLenStack 16896

theorem stackAt_computeMacX_to_encodeVarintX (sp : BitVec 64) :
    stackAt sp computeMacStackX = memRegion (sp - 16912#64) 368 ∗ stackAt sp encodeVarintStackX :=
  signalMessageNew_stackAt_split_bottom' sp computeMacStackX encodeVarintStackX 368

theorem stackAt_encodeVarintX_to_extHook (sp : BitVec 64) :
    stackAt sp encodeVarintStackX = memRegion (sp - 16544#64) 160 ∗ stackAt sp extHookStack :=
  signalMessageNew_stackAt_split_bottom' sp encodeVarintStackX extHookStack 160

theorem stackAt_signalMessageNewX_to_extHook (sp0 : BitVec 64) :
    stackAt sp0 signalMessageNewStackX = memRegion (sp0 - 17328#64) 944 ∗ stackAt sp0 extHookStack :=
  signalMessageNew_stackAt_split_bottom' sp0 signalMessageNewStackX extHookStack 944

/-! ## Relocatable `[LibsignalPlacement]` sequencing and panic lemmas (Block `63`) -/

theorem signalMessageNew_of_sepWP_placed [LibsignalPlacement] {prog : Program} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem →
      SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_seq_lscl hcl h

theorem signalMessageNew_call_placed [LibsignalPlacement] {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre' hsp hL
  have hcl_m : LibsignalCodeLoaded lsmpl sm.mem := hcl.of_keepsFrozen hsteps.keepsFrozen
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hcl_m hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost
    exact (hexit sm code _ hex hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    exact (hoom sm _ hoom_s hpost).elim

theorem signalMessageNew_seq_wpp_placed [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hfoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm (hcl.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hfoom).elim

theorem signalMessageNew_seq_wp_placed [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  rcases h1.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, hfoom⟩⟩
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm (hcl.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hfoom).elim

theorem signalMessageNew_seq_wpp_or_placed [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {ovf : Prop} {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocOrOverflowPost ovf s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, ((allocFailedIn s0 sf ∨ ovf) ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hfoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm (hcl.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : (allocFailedIn s0 sm ∨ ovf) ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hfoom).elim

theorem layout_err_at_158_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsRawVecHandleErrorSym = some Rust.panicked)
    {ovf : Prop} {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hovf : ovf)
    (hpc : s.pc = (blkPl_63).base + 344#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H) ret s P Q (PanicAllocOrOverflowPost ovf s0) := by
  have hext : ((blkPC_63).rebase (blkPl_63).base H).externAt? (lsρ lsRawVecHandleErrorSym) = some Rust.panicked :=
    new_externAt?_handle_error hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsRawVecHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocOrOverflowPost_of_overflow hovf (by simp_all [Rust.panicked, arm64_norm])

theorem oom_at_15c_or_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsRawVecHandleErrorSym = some Rust.panicked)
    {ovf : Prop} {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_63).base + 348#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H) ret s P Q (PanicAllocOrOverflowPost ovf s0) := by
  have hext : ((blkPC_63).rebase (blkPl_63).base H).externAt? (lsρ lsRawVecHandleErrorSym) = some Rust.panicked :=
    new_externAt?_handle_error hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsRawVecHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocOrOverflowPost_of_alloc (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem oom_at_15c_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsRawVecHandleErrorSym = some Rust.panicked)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_63).base + 348#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H) ret s P Q (PanicAllocPost s0) := by
  have hext : ((blkPC_63).rebase (blkPl_63).base H).externAt? (lsρ lsRawVecHandleErrorSym) = some Rust.panicked :=
    new_externAt?_handle_error hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsRawVecHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem oom_at_858_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsRawVecHandleErrorSym = some Rust.panicked)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_63).base + 2136#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H) ret s P Q (PanicAllocPost s0) := by
  have hext : ((blkPC_63).rebase (blkPl_63).base H).externAt? (lsρ lsRawVecHandleErrorSym) = some Rust.panicked :=
    new_externAt?_handle_error hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsRawVecHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem oom_at_864_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsRawVecHandleErrorSym = some Rust.panicked)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_63).base + 2148#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H) ret s P Q (PanicAllocPost s0) := by
  have hext : ((blkPC_63).rebase (blkPl_63).base H).externAt? (lsρ lsRawVecHandleErrorSym) = some Rust.panicked :=
    new_externAt?_handle_error hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsRawVecHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem oom_at_898_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_63).base + 2200#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H) ret s P Q (PanicAllocPost s0) := by
  have hext : ((blkPC_63).rebase (blkPl_63).base H).externAt? (lsρ lsAllocHandleErrorSym) = some Rust.panicked :=
    new_externAt?_handle_alloc_error hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsAllocHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

end CryptoVerification.LibsignalTripleRatchet

