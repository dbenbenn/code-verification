/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P4.1 Segments: `IdentityKeyStore::save_identity`

Basic-block `SepWP` segments (`+0x34dc → saveShim`, `+0x3564 → savePoll`, `+0x6c → saveFutDrop`,
`+0x2ec → kyberMarkUsedShimAddr` / `+0x550`) and error-slot bijection helpers for Substage P4.1 on
`tripleRatchetProgAtExt img.base ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.E2E.Pqxdh.ResponderClosure.extractLsb_0_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.extractLsb_32_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.setWidth_32_append_32
  CryptoVerification.E2E.Pqxdh.ResponderClosure.append_1_32_getElem_zero

/-- `SepWPp.bind_sepWP_frame` refined to pass `Steps prog s s1` to the continuation. -/
theorem SepWPp.bind_sepWP_frame_steps {prog : Program} {mid ret : BitVec 64} {s : State}
    {P T F : SepProp} {Q1 Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s T Q1)
    (hP : P = T ∗ F)
    (hnext : ∀ s1 P1, s1.pc = mid → s1.status = .Running → Steps prog s s1 →
      Q1 s1 P1 → SepWPp prog ret s1 (P1 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  rcases h1.elim hm hL with ⟨s1, hsteps1, ⟨hpc1, hrun1, P1, hm1, hQ1⟩ | ⟨_, hoom⟩⟩
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps2, hout⟩ := hnext s1 P1 hpc1 hrun1 hsteps1 hQ1 R hm1 (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Inject read-only `.rodata` points-to atoms extracted from `img.FrozenLoaded s` into a `SepWPp`
precondition at zero spatial cost. -/
theorem SepWPp.intro_ro {prog : Program} {ret : BitVec 64} {s : State}
    {R_ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {M : SepProp}, s.mem ⊨ M → s.mem ⊨ R_ro ∗ M)
    (h : SepWPp prog ret s (R_ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (R_ro ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact hro hm
  exact h R hm' hL

/-- Layout-independent unpack of a right-associated 5-word + `errTailAt`-shaped
`SignalProtocolError` poll slot (`savePollOutAt ... (.error ())` or `storePollOutAt ... (.error ())`)
into `pollCellsAt`. -/
theorem fiveWords_tail_eq_exists_pollCells (p w0 w1 w2 w3 w4 strAddr : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗
      ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗ (strAddr ↦ᵣ storeHookStr) ∗
      memRegion (p + 0x28#64) 8 =
    ∃∗ w5 : BitVec 64,
      pollCellsAt p w0 (w1.extractLsb' 0 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32) ∗ (strAddr ↦ᵣ storeHookStr) := by
  rw [ProofLib.memRegion_eight (p + 0x28#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun w5 => ?_)
  rw [← speWordsAt_eq_pollCellsAt p w0 w1 w2 w3 w4 w5]
  unfold speWordsAt; ac_rfl

/-- Layout-independent repack of `pollCellsAt outPtr ... ∗ (strAddr ↦ᵣ storeHookStr)` back into a
right-associated 5-word + `errTailAt` `SignalProtocolError` return slot. -/
theorem pollCells_entails_fiveWords_tail (outPtr w0 w1 w2 w3 w4 w5 strAddr : BitVec 64) :
    pollCellsAt outPtr w0 (w1.extractLsb' 0 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32) ∗ (strAddr ↦ᵣ storeHookStr) ⊢
      (outPtr ↦₆₄ w0) ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 0x10#64) ↦₆₄ w2) ∗
        ((outPtr + 0x18#64) ↦₆₄ w3) ∗ ((outPtr + 0x20#64) ↦₆₄ w4) ∗ (strAddr ↦ᵣ storeHookStr) ∗
        memRegion (outPtr + 0x28#64) 8 := by
  rw [← speWordsAt_eq_pollCellsAt outPtr w0 w1 w2 w3 w4 w5]
  have hswap : speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗ (strAddr ↦ᵣ storeHookStr) =
      (outPtr ↦₆₄ w0) ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 0x10#64) ↦₆₄ w2) ∗
        ((outPtr + 0x18#64) ↦₆₄ w3) ∗ ((outPtr + 0x20#64) ↦₆₄ w4) ∗ (strAddr ↦ᵣ storeHookStr) ∗
        ((outPtr + 0x28#64) ↦₆₄ w5) := by
    unfold speWordsAt; ac_rfl
  rw [hswap]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (pointsTo64_entails_memRegion _ _))))))

/-- Layout-independent existential unpack + repack of a 5-word + `errTailAt` poll slot into
    `pollCellsAt` with explicit witness terms. -/
theorem fiveWords_tail_unpack_repack {w0_tag : BitVec 64}
    (p w0 w1 w2 w3 w4 strAddr : BitVec 64) (hw0 : w0 = w0_tag) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗
      ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗ (strAddr ↦ᵣ storeHookStr) ∗
      memRegion (p + 0x28#64) 8 ⊢
    ∃∗ w0' : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
    ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32, ∃∗ H_err : SepProp,
      ⌜w0' = w0_tag ∧
        (∀ outPtr : BitVec 64,
          pollCellsAt outPtr w0' o1 o2 o3 o4 o5 o6 ∗ H_err ⊢
            (outPtr ↦₆₄ w0) ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 0x10#64) ↦₆₄ w2) ∗
              ((outPtr + 0x18#64) ↦₆₄ w3) ∗ ((outPtr + 0x20#64) ↦₆₄ w4) ∗
              (strAddr ↦ᵣ storeHookStr) ∗ memRegion (outPtr + 0x28#64) 8)⌝ ∗
      pollCellsAt p w0' o1 o2 o3 o4 o5 o6 ∗ H_err := by
  rw [fiveWords_tail_eq_exists_pollCells p w0 w1 w2 w3 w4 strAddr]
  refine Entails.sepExists_elim fun w5 => ?_
  let o1 := w1.extractLsb' 0 32
  let o2 := w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32
  let o3 := w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32
  let o4 := w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32
  let o5 := w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32
  let o6 := w5.extractLsb' 32 32
  let H_err : SepProp := strAddr ↦ᵣ storeHookStr
  refine Entails.sepExists_right w0
    (Entails.sepExists_right o1 (Entails.sepExists_right o2 (Entails.sepExists_right o3
    (Entails.sepExists_right o4 (Entails.sepExists_right o5 (Entails.sepExists_right o6
    (Entails.sepExists_right H_err ?_)))))))
  refine Entails.pure_right ⟨hw0, fun outPtr => ?_⟩ (Entails.refl _)
  exact pollCells_entails_fiveWords_tail outPtr w0 w1 w2 w3 w4 w5 strAddr

/-- Read-only `.rodata` vtable bundle for `ikit`'s `save_identity` dispatch, poll, and drop. -/
@[expose] def saveIdVtablesAt {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : SepProp :=
  ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (b + ikit.saveShimOff)) ∗
  ((b + ikit.saveFutVtOff) ↦₆₄ᵣ (b + ikit.saveFutDropOff)) ∗
  ((b + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
  ((b + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.savePollOff))

theorem memRegion24_eq_unaligned_cells (p : BitVec 64) :
    memRegion p 24 =
      ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 32,
        (p ↦₃₂ u0) ∗ ((p + 0x4#64) ↦₆₄ u1) ∗ ((p + 0xc#64) ↦₆₄ u2) ∗ ((p + 0x14#64) ↦₃₂ u3) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 4) (k := 20)
        (b' := p + 0x4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x4#64) (n := 8) (k := 12)
        (b' := p + 0xc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0xc#64) (n := 8) (k := 4)
        (b' := p + 0x14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four p,
      ProofLib.memRegion_eight (p + 0x4#64),
      ProofLib.memRegion_eight (p + 0xc#64),
      ProofLib.memRegion_four (p + 0x14#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion20_eq_cells (p : BitVec 64) :
    memRegion p 20 =
      ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 0x8#64) ↦₆₄ u1) ∗ ((p + 0x10#64) ↦₃₂ u2) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 12)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x8#64) (n := 8) (k := 4)
        (b' := p + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_eight (p + 0x8#64),
      ProofLib.memRegion_four (p + 0x10#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem cells20_entails_memRegion20 (p w0 w1 : BitVec 64) (w2 : BitVec 32) :
    (p ↦₆₄ w0) ∗ ((p + 0x8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₃₂ w2) ⊢ memRegion p 20 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 12)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x8#64) (n := 8) (k := 4)
        (b' := p + 0x10#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo32_entails_memRegion _ _))

theorem memRegion16_eq_cells (p : BitVec 64) :
    memRegion p 16 =
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 0x8#64) ↦₆₄ u1) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 8)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_eight (p + 0x8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem cells16_entails_memRegion16 (p w0 w1 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 0x8#64) ↦₆₄ w1) ⊢ memRegion p 16 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 8)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

/-- Advance `FsAt` across any execution segment that appends no trace events. -/
theorem FsAt.of_steps_nil {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s s' : State}
    (h : FsAt envOk Q P s) (hst : Steps P s s') (htr : s'.trace = s.trace) :
    FsAt envOk Q P s' :=
  h.of_steps hst (evs := []) (by rw [htr, List.append_nil]) (fun _ => NoFsEv.nil)

/-- Unpack `savePollOutAt b p (.ok c)` into `pollCellsAt p (-2) ...`. -/
theorem savePollOk_eq_exists_pollCells (b p : BitVec 64) (c : IdentityChange) :
    savePollOutAt b p (.ok c) =
      ∃∗ o6 : BitVec 32, ∃∗ o5 : BitVec 64, ∃∗ o4 : BitVec 64,
      ∃∗ o3 : BitVec 64, ∃∗ o2 : BitVec 64,
        pollCellsAt p 0xfffffffffffffffe#64
          (if c == .replacedExisting then 1#32 else 0#32) o2 o3 o4 o5 o6 := by
  dsimp only [savePollOutAt]
  rw [memRegion36_eq_exists_stagingCells (p + 0xc#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun o6 => congrArg sepExists (funext fun o5 =>
    congrArg sepExists (funext fun o4 => congrArg sepExists (funext fun o3 =>
    congrArg sepExists (funext fun o2 => ?_)))))
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Layout-independent unpack + repack of `savePollOutAt b p (.error ())` into `pollCellsAt`. -/
theorem savePollErr_unpack_repack (b p : BitVec 64) :
    savePollOutAt b p (.error ()) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32, ∃∗ H_err : SepProp,
        ⌜w0 = 0x800000000000001A#64 ∧
          (∀ outPtr : BitVec 64,
            pollCellsAt outPtr w0 o1 o2 o3 o4 o5 o6 ∗ H_err ⊢ savePollOutAt b outPtr (.error ()))⌝ ∗
        pollCellsAt p w0 o1 o2 o3 o4 o5 o6 ∗ H_err := by
  dsimp only [savePollOutAt, errTailAt]
  simp only [sepConj_assoc]
  exact fiveWords_tail_unpack_repack p _ _ _ _ _ _ rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
