/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopError -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Field Merge Branches and Tag Dispatch

CPS proofs for field 1 (`publicKey`, `+264`), field 2 (`privateKey`, `+92`), unknown-tag
`skip_field` (`+284`), and tag dispatch (`+248 .. +260`) in `IdentityKeyPair::try_from`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section LoopMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_lm (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_lm (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_lm (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_lm (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_lm (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_lm (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_lm (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_lm (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_lm (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_lm (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_lm (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_lm (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_lm (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_lm (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_lm (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_lm (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end LoopMergeStateSimp

/-! ## Helper lemmas for loop invariants and frame splitting -/

theorem vecU8Buf_cap_lt63 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  rw [pure_true_emp h.2.1, emp_sepConj, pure_true_emp h, emp_sepConj]
  exact Entails.refl _

theorem ikpStructAt_entails_of (A : RustAlloc) (pk sk : VecPin) (a : BitVec 64)
    (m : IdentityKeyPairStructure) :
    ikpStructAt A pk sk a m ⊢ ikpStructOf A a m :=
  Entails.trans (sepExists_intro (fun sk' => ikpStructAt A pk sk' a m) sk)
    (sepExists_intro (fun pk' => ∃∗ sk', ikpStructAt A pk' sk' a m) pk)

theorem ikpMem144_prologue_cells (sp' : BitVec 64) :
    memRegion sp' 144 ⊢
      ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64,
      ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64,
        memRegion sp' 32 ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₆₄ w48) ∗ ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 64#64) ↦₆₄ w64) ∗ ((sp' + 72#64) ↦₆₄ w72) ∗
        ((sp' + 80#64) ↦₆₄ w80) ∗ ((sp' + 88#64) ↦₆₄ w88) ∗
        memRegion (sp' + 96#64) 48 := by
  rw [show (144 : Nat) = 32 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 48)))))))) by decide,
    Prost.memRegion_split sp' 32 112 (by decide),
    Prost.memRegion_split (sp' + 32#64) 8 104 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64) 8 96 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64) 8 88 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64) 8 80 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem ikpEmptyCells_entails_structAt (A : RustAlloc) (sp' : BitVec 64) :
    ((sp' + 48#64) ↦₆₄ 0#64) ∗ ((sp' + 56#64) ↦₆₄ 1#64) ∗ ((sp' + 64#64) ↦₆₄ 0#64) ∗
      ((sp' + 72#64) ↦₆₄ 0#64) ∗ ((sp' + 80#64) ↦₆₄ 1#64) ∗ ((sp' + 88#64) ↦₆₄ 0#64) ⊢
      ikpStructAt A ⟨0#64, 1#64⟩ ⟨0#64, 1#64⟩ (sp' + 48#64) IdentityKeyPairStructure.empty := by
  unfold ikpStructAt IdentityKeyPairStructure.empty
  have h1ne : (1#64 : BitVec 64) ≠ 0 := by decide
  simp only [vecU8At_eq_header_buf, vecHeader, vecU8Buf_zero,
    BitVec.add_assoc, BitVec.reduceAdd, List.length_nil,
    pure_true_emp (And.intro trivial h1ne), sepConj_emp, sepConj_assoc]
  exact Entails.refl _

theorem tag_ge3_conds (tag : ℕ) (hge : 3 ≤ tag) (hlt : tag < 2 ^ 32) :
    let w1 := (BitVec.ofNat 64 tag).setWidth 32
    ((w1 == 2#32) = false) ∧ ((w1 == 1#32) = false) ∧ ((w1 != 1#32) = true) := by
  dsimp only
  rw [setWidth32_ofNat64]
  have h2 : BitVec.ofNat 32 tag ≠ 2#32 := by bv_omega
  have h1 : BitVec.ofNat 32 tag ≠ 1#32 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h1, bne_iff_ne.mpr h1⟩

/-! ## Field merge branches: `publicKey` (`+264`), `privateKey` (`+92`), `skipField` (`+284`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem decodeErrorFrom_600_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hpc : s.pc = (blkPl_84).base + 600#64) (hrun : s.status = .Running)
    (hkind : KindNoHeap (s.readReg64 .x8)) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A (sp' + 48#64) mErr ∗
        ((sp' + 96#64) ↦₆₄ w0) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hcall := ikp_decodeErrorFrom_placed_ok d
  have herr := @decodeErr_616_placed_wp _ A H d x s0
  have hsp_subst := hregs.base.sp; subst hsp_subst
  have _hx29 := hregs.x29
  have hstack := stackAt_sub_split s.sp (2 * extHookStack) (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 261) ?_; wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro (s.sp + 96#64, s.readReg64 (Reg.gpr 8#5)) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hcrl1
    (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (612))
    (by simp_all [hregs.base.trace, arm64_norm])
    (T := ((s.sp + 96#64) ↦₆₄ s.readReg64 (Reg.gpr 8#5)) ∗ memRegion (s.sp + 104#64) 40 ∗
      A.pool ∗ stackAt s.sp (2 * extHookStack))
    (φ := KindNoHeap (s.readReg64 (Reg.gpr 8#5)))
    (by simp_all [decodeErrorFromSpecWithStack, arm64_norm])
    hkind (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs1 := hregs.of_steps hcrl1 rfl
    (by simp_all [hregs.base.trace, arm64_norm])
    (by simp_all [hregs.base.x26, arm64_norm]) (by simp_all [hregs.base.x27, arm64_norm])
    (by simp_all [hregs.base.x28, arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [hregs.x19, arm64_norm]) (by simp_all [hregs.x21, arm64_norm])
    (by simp_all [hregs.x24, arm64_norm])
  dsimp only [decodeErrorFromSpecWithStack]; rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨_hx0_ne, htr2⟩ => ?_
  have hregs2' := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl3
  refine Wire.SepWPp.mono_pre
    (P' := memRegion s.sp 32 ∗ memRegion (s.sp + 32#64) 16 ∗ ikpStructOf A (s.sp + 48#64) mErr ∗
      memRegion (s.sp + 96#64) 48 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
      memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool ∗
      stackAt s.sp (skipFieldStackX 100) ∗ decodeErrorAt A (s2.readReg64 (Reg.gpr 0#5)))
    (by simp only [arm64_norm]; rw [hstack]
        refine Entails.trans
          (sepConj_mono (decodeErrorWith_entails_at A (s2.readReg64 (Reg.gpr 0#5)) 0) (Entails.refl _)) ?_
        apply entails_of_eq; ac_rfl) ?_
  exact herr htry_err
    (hregs2'.base.of_steps hcrl3 (by simp_all [hregs2'.base.sp, arm64_norm])
      (by simp_all [hregs2'.base.trace, arm64_norm]) (by simp_all [hregs2'.base.x26, arm64_norm])
      (by simp_all [hregs2'.base.x27, arm64_norm]) (by simp_all [hregs2'.base.x28, arm64_norm]))
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [hregs2'.x19, arm64_norm]) (by simp_all [hregs2'.x24, arm64_norm])
    (by simp_all [arm64_norm])

theorem decodeErrorPush_916_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr err : BitVec 64}
    {n : Nat} {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hpc : s.pc = (blkPl_84).base + 916#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = sp' + 96#64) (herr_ne : err ≠ 0#64) (hn : n < 2 ^ 32) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A (sp' + 48#64) mErr ∗
        ((sp' + 96#64) ↦₆₄ err) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAtStackLen A err n)
      (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hcall := ikp_decodeErrorPush_placed_ok d
  have herr := @decodeErr_616_placed_wp _ A H d x s0
  have hsp_subst := hregs.base.sp; subst hsp_subst
  have hstack := stackAt_sub_split s.sp (2 * extHookStack) (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 257) ?_; wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro (s.sp + 96#64, err, n) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hcrl1
    (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (920))
    (by simp_all [hregs.base.trace, arm64_norm])
    (T := ((s.sp + 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ A.pool ∗ stackAt s.sp (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ n < 4294967296)
    (by simp_all [decodeErrorPushExternSpecWithStack, arm64_norm])
    ⟨herr_ne, hn⟩ (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [decodeErrorPushExternSpecWithStack]; rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun err' => Wire.SepWPp.pure_pre fun _herr' => ?_
  have hregs1 := hregs.of_steps hcrl1 rfl
    (by simp_all [hregs.base.trace, arm64_norm])
    (by simp_all [hregs.base.x26, arm64_norm]) (by simp_all [hregs.base.x27, arm64_norm])
    (by simp_all [hregs.base.x28, arm64_norm]) (by simp_all [hregs.x29, arm64_norm])
    (by simp_all [hregs.x19, arm64_norm]) (by simp_all [hregs.x21, arm64_norm])
    (by simp_all [hregs.x24, arm64_norm])
  have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
  have _hx29_2 := hregs2.x29
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl3
  have hm48 := ikpPointsTo64_96_mem40_entails_mem48 s.sp err'
  refine Wire.SepWPp.mono_pre
    (P' := memRegion s.sp 32 ∗ memRegion (s.sp + 32#64) 16 ∗ ikpStructOf A (s.sp + 48#64) mErr ∗
      memRegion (s.sp + 96#64) 48 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
      memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool ∗
      stackAt s.sp (skipFieldStackX 100) ∗ decodeErrorAt A err')
    (by simp only [arm64_norm]; rw [hstack]
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono (decodeErrorWith_entails_at A err' (n + 1)) (Entails.refl _))) ?_
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm48))))
        apply entails_of_eq; ac_rfl) ?_
  exact herr htry_err
    (hregs2.base.of_steps hcrl3 (by simp_all [hregs2.base.sp, arm64_norm])
      (by simp_all [hregs2.base.trace, arm64_norm]) (by simp_all [hregs2.base.x26, arm64_norm])
      (by simp_all [hregs2.base.x27, arm64_norm]) (by simp_all [hregs2.base.x28, arm64_norm]))
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [hregs2.x19, arm64_norm]) (by simp_all [hregs2.x24, arm64_norm])
    (by simp_all [arm64_norm])

theorem decodeVarintSlice_168_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 168#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64) (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 63) (hpre_slice : VarintSlicePre bs)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_84).base + 220#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 → s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x20 = key →
      Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ ikpLoopCommonPlaced A sp' x.ret bs.length m)
        (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : decodeVarint bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗ ikpLoopCommonPlaced A sp' x.ret bs.length m)
      (ikpExitPostPlaced A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  have hcall := ikp_varintSlice_placed_ok d
  have herr := @decodeErr_616_placed_wp _ A H d x s0
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_subst := hregs.base.sp; subst hsp_subst
  have _hsp_align := hregs.base.spAligned; have _hx29 := hregs.x29
  have _hx1' : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have _hx2' : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split s.sp decodeVarintSliceStackX (skipFieldStackX 100)
  unfold sliceCursorAt ikpLoopCommonPlaced
  simp only [hstack, ikpMem48_split24 s.sp, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 76) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro ⟨s.sp + 96#64, ptr, bs⟩ hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (176))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := memRegion (s.sp + 96#64) 24 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp decodeVarintSliceStackX)
    (φ := bs.length < 9223372036854775808 ∧ VarintSlicePre bs)
    (by simp [*, decodeVarintSliceSpecX, arm64_norm])
    ⟨hlen, hpre_slice⟩ (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs1 := hregs.of_steps hcrl1 rfl
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm]) (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm]) (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm]) (by simp [*, hregs.x21, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = s.sp + 32#64 :=
    hcs2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = s.sp + 40#64 :=
    hcs2.2.2.2.1.trans (by simp [*, arm64_norm])
  dsimp only [decodeVarintSliceSpecX]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [varintSliceResultAt]
    obtain ⟨k, _, _hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
        BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]
      omega
    have hult_false :
        (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64,
        decide_eq_false_iff_not]
      omega
    rw [pointsTo64_zero_split32 (s.sp + 96#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hx29_2 : s2.readReg64 (Reg.gpr 29#5) = s.sp + 144#64 := hregs2.x29
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (220)) ?_; wp_steps
    wp_if hcc
    · exfalso; rw [← hrest] at hcc; exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
      have hscr := ikpScratch24_ok_entails_mem48 s.sp key (BitVec.ofNat 64 (bs.length - rest.length))
      refine Wire.SepWPp.mono_pre
        (P' := sliceCursorAfter (s.sp + 32#64) ptr bs rest ∗ ikpLoopCommonPlaced A s.sp x.ret bs.length m)
        (by unfold sliceCursorAfter ikpLoopCommonPlaced
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
            rw [hstack]; apply entails_of_eq; simp only [← hrest, hsub_bv, arm64_norm]; ac_rfl) ?_
      exact hcont key rest _ hd (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (hregs2.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
          (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
          (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm])
          (by simp [*, hregs2.x29, arm64_norm]) (by simp [*, hregs2.x19, arm64_norm])
          (by simp [*, hregs2.x21, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
  | none =>
    dsimp only [varintSliceResultAt]
    rw [pointsTo64_one_split32 (s.sp + 96#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.exists_pre fun e => Wire.SepWPp.pure_pre fun _he_ne => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hx29_2 : s2.readReg64 (Reg.gpr 29#5) = s.sp + 144#64 := hregs2.x29
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hpair := pointsTo64_pair_entails_memRegion16 (s.sp + 32#64) ptr (BitVec.ofNat 64 bs.length)
    have hscr := ikpScratch24_err_entails_mem48 s.sp e
    refine Wire.SepWPp.mono_pre
      (P' := memRegion s.sp 32 ∗ memRegion (s.sp + 32#64) 16 ∗ ikpStructOf A (s.sp + 48#64) m ∗
        memRegion (s.sp + 96#64) 48 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
        memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool ∗
        stackAt s.sp (skipFieldStackX 100) ∗ decodeErrorAt A e)
      (by refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono hpair
              (sepConj_mono (ikpStructLoopOf_entails_of A (s.sp + 48#64) bs.length m)
                (sepConj_mono hscr
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (decodeErrorWith_entails_at A e 0)))))))))))
          rw [hstack]; apply entails_of_eq; simp only [arm64_norm]; ac_rfl) ?_
    exact herr (hnone hd)
      (hregs2.base.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, hregs2.x19, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm])
      (by simp [*, arm64_norm])

end Placed

end CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
