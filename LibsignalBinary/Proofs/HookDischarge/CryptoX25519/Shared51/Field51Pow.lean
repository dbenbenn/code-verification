/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51

/-!
# `FieldElement51::pow22501` machine-code proof

Verifies `x25519CliMultiLib` block `05` (`FieldElement51::pow22501`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Pow

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpPow)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl x25519Caller_ok x25519Call_of_blockOk
  seq_codeLoaded_lr goalIsSeqCodeLoaded clearOldCodeLoadedHyps
  resolve_blk01 resolve_blk02)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBounded Fe51MulOk Fe51Pow2kOk Fe51Pow22501Ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  HasLenGe write64_length_eq readLE_write64_self' readLE_write64_ne sub_ofNat64_add
  fpPow_mod_eq_pow_mod sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes sepWP_abstract_bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51 (
  fe51_mul_ok fe51_pow2k_ok)

arm64_proof_prelude

attribute [local irreducible] MultiPlacedLib.CodeLoaded

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 05 x25519CliMultiLib X25519CliPlacement 101 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl05_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl05.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

open Lean Meta Elab Tactic in
local elab "clean_prev_sf2" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut stateDecls : Array LocalDecl := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && decl.type.isConstOf ``Arm64.State && decl.userName != `s0 then
      stateDecls := stateDecls.push decl
  if stateDecls.size ≥ 2 then
    let (prevSf, currSf) := (stateDecls[stateDecls.size - 2]!, stateDecls[stateDecls.size - 1]!)
    let mut prevEqs : Array FVarId := #[]
    let mut prevHyps : Array FVarId := #[]
    let mut currHyps : Array FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail && decl.fvarId != prevSf.fvarId && decl.fvarId != currSf.fvarId then
        let ty ← instantiateMVars decl.type
        if ty.containsFVar prevSf.fvarId then
          prevHyps := prevHyps.push decl.fvarId
          if !ty.containsFVar currSf.fvarId then
            if let some (_, lhs, _) := ty.eq? then
              if lhs.containsFVar prevSf.fvarId then prevEqs := prevEqs.push decl.fvarId
          else currHyps := currHyps.push decl.fvarId
    for cId in currHyps do
      let cIdent := mkIdent (← cId.getUserName)
      for pId in prevEqs do
        let pIdent := mkIdent (← pId.getUserName)
        try evalTactic (← `(tactic| rw [$pIdent:term] at $cIdent:ident)) catch _ => pure ()
    let mut toClear : Array Ident := #[]
    for pId in prevHyps do
      if !currHyps.contains pId then toClear := toClear.push (mkIdent (← pId.getUserName))
    toClear := toClear.push (mkIdent prevSf.userName)
    for id in toClear do
      try evalTactic (← `(tactic| clear $id:ident)) catch _ => pure ()

private theorem pc_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).pc = pc := rfl
private theorem pc_setMem' (s : State) (m : Memory) : (s.setMem m).pc = s.pc := rfl
private theorem pc_setPState' (s : State) (ps : PState) : (s.setPState ps).pc = s.pc := rfl
private theorem pc_writeVReg128' (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).pc = s.pc := rfl
private theorem pc_advancePC' (s : State) : s.advancePC.pc = s.pc + 4#64 := rfl
private theorem pc_writeReg64' (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).pc = s.pc := rfl
private theorem pc_writeReg32' (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).pc = s.pc := rfl
private theorem pc_writeReg' (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).pc = s.pc := rfl
private theorem status_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := rfl
private theorem status_setMem' (s : State) (m : Memory) : (s.setMem m).status = s.status := rfl
private theorem status_setPState' (s : State) (ps : PState) : (s.setPState ps).status = s.status := rfl
private theorem status_writeVReg128' (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).status = s.status := rfl
private theorem status_advancePC' (s : State) : s.advancePC.status = s.status := rfl
private theorem status_writeReg64' (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).status = s.status := rfl
private theorem status_writeReg32' (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).status = s.status := rfl
private theorem status_writeReg' (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).status = s.status := rfl
private theorem mem_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := rfl
private theorem mem_setPState' (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := rfl
private theorem mem_writeVReg128' (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).mem = s.mem := rfl
private theorem mem_advancePC' (s : State) : s.advancePC.mem = s.mem := rfl
private theorem mem_writeReg64' (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).mem = s.mem := rfl
private theorem mem_writeReg32' (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).mem = s.mem := rfl
private theorem mem_writeReg' (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).mem = s.mem := rfl

open Lean Meta Elab Tactic in
local elab "close_cut_codeLoaded" : tactic => do
  evalTactic (← `(tactic| (
    apply SepWP.done
    · try simp only [pc_setPC', pc_setMem', pc_setPState', pc_writeVReg128', pc_advancePC',
        pc_writeReg64', pc_writeReg32', pc_writeReg']
      rfl
    · try simp only [status_setPC', status_setMem', status_setPState', status_writeVReg128', status_advancePC',
        status_writeReg64', status_writeReg32', status_writeReg']
      first | with_reducible assumption | assumption)))
  clearOldCodeLoadedHyps
  let hclId := mkIdent (← mkFreshUserName `hcl_cut)
  evalTactic (← `(tactic| intro $hclId:ident))

open Lean Meta Elab Tactic in
local elab "wp_x25519_call_fast " hcall:term : tactic => do
  if ← goalIsSeqCodeLoaded (← getMainGoal) then
    evalTactic (← `(tactic| close_cut_codeLoaded))
  let gCur ← getMainGoal
  let progStx ← gCur.withContext do
    let ty := (← instantiateMVars (← gCur.getType)).consumeMData
    Term.exprToSyntax (ty.getArg! 0)
  let hclPostId := mkIdent (← mkFreshUserName `hcl_post)
  evalTactic (← `(tactic| (
    apply seq_codeLoaded_lr (by
      try simp only [mem_setPC', mem_setPState', mem_writeVReg128', mem_advancePC',
        mem_writeReg64', mem_writeReg32', mem_writeReg']
      first | with_reducible assumption | assumption)
    wp_call (x25519Call_of_blockOk $progStx $hcall))))
  let postCallGoals ← getGoals
  let mut newGoals : List MVarId := []
  for g in postCallGoals do
    if ← goalIsSeqCodeLoaded g then
      setGoals [g]
      evalTactic (← `(tactic| (
        apply SepWP.done
        · first
            | with_reducible assumption
            | (conv => rhs; simp (config := { decide := true }) only [wp_norm, arm64_norm]
               with_reducible assumption)
            | (wp_norm_goal; rfl)
            | rfl
        · first | with_reducible assumption | wp_norm_lhs | assumption)))
      clearOldCodeLoadedHyps
      evalTactic (← `(tactic| intro $hclPostId:ident))
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [g]
  setGoals newGoals

private theorem sepWP_callee_224_to_96 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - 816#64 - 224#64) 224 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((memRegion (sp - 816#64 - 96#64) 96 ∗ stackAt (sp - 912#64) 128) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have h912 : sp - 816#64 - 96#64 = sp - 912#64 := by rw [BitVec.sub_sub]; rfl
  rw [hf]; change SepWP prog target_pc s (stackAt (sp - 816#64) (128 + 96) ∗ P) post oom
  rw [stackAt_region (sp - 816#64) 128 96 (by decide), sepConj_comm (stackAt _ _) (memRegion _ _)]; rw [← h912] at hnext; exact hnext

private theorem sepWP_callee_96_to_224 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp - 816#64 - 96#64) 96 ∗ stackAt (sp - 912#64) 128) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp - 816#64 - 224#64) 224 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have h912 : sp - 912#64 = sp - 816#64 - 96#64 := by rw [BitVec.sub_sub]; rfl
  rw [hf, h912, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region (sp - 816#64) 128 96 (by decide)]; exact hnext

private theorem sepWP_split2_80 (base : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 80 := by assumption)
    (hnext : ∀ b0 b1 : List (BitVec 8), b0.length = 40 → b1.length = 40 →
      SepWP prog target_pc s (((base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hs0 := (congrArg (base ↦ₛ ·) (List.take_append_drop 40 bs).symm).trans (pointsToBytes_append base (bs.take 40) (bs.drop 40))
  rw [show (bs.take 40).length = 40 by simp [hbs]] at hs0; rw [hf, hs0]; exact hnext (bs.take 40) (bs.drop 40) (by simp [hbs]) (by simp [hbs])

private theorem sepWP_merge2_80 (base : BitVec 64) {b0 b1 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1)) ∗ P) := by sep_frame) (h0 : b0.length = 40 := by assumption)
    (hnext : SepWP prog target_pc s (((base ↦ₛ (b0 ++ b1)) ∗ P)) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : (base ↦ₛ (b0 ++ b1)) = (base ↦ₛ b0) ∗ ((base + 40#64) ↦ₛ b1) := by rw [pointsToBytes_append, h0]
  rw [hf, ← hm]; exact hnext


private theorem pow_pow_mod_step (w_val src_val A E K E' m : Nat)
    (hw : w_val % m = src_val ^ K % m) (hsrc : src_val % m = A ^ E % m) (hE' : E * K = E') : w_val % m = A ^ E' % m := by
  rw [hw, Nat.pow_mod src_val K m, hsrc, ← Nat.pow_mod (A ^ E) K m, ← Nat.pow_mul, hE']

private theorem mul_pow_mod_step (w_val s1_val s2_val A E1 E2 E' m : Nat)
    (hw : w_val % m = (s1_val * s2_val) % m) (hs1 : s1_val % m = A ^ E1 % m) (hs2 : s2_val % m = A ^ E2 % m) (hE' : E1 + E2 = E') :
    w_val % m = A ^ E' % m := by
  rw [hw, Nat.mul_mod s1_val s2_val m, hs1, hs2, ← Nat.mul_mod (A ^ E1) (A ^ E2) m, ← Nat.pow_add, hE']

private theorem fe51_pow2k_chain_props (w : List (BitVec 8)) (E' : Nat) {src : List (BitVec 8)} {A E K : Nat}
    (hb : fe51LimbsBounded w (2 ^ 52) := by assumption)
    (hv : fe51ValOfBytes w % p25519 = fpPow (fe51ValOfBytes src % p25519) K := by assumption)
    (hsrc : fe51ValOfBytes src % p25519 = A ^ E % p25519 := by assumption)
    (hK : K < 2 ^ 256 := by decide) (hE' : E * K = E' := by decide) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 54) ∧ fe51LimbsBounded w (2 ^ 52) ∧ fe51ValOfBytes w % p25519 = A ^ E' % p25519 := by
  have ⟨hl, h0, h1, h2, h3, h4⟩ := hb
  have hv' : fe51ValOfBytes w % p25519 = (fe51ValOfBytes src) ^ K % p25519 :=
    hv.trans (fpPow_mod_eq_pow_mod (fe51ValOfBytes src) K hK)
  exact ⟨hl, ⟨hl, by omega, by omega, by omega, by omega, by omega⟩, hb, pow_pow_mod_step _ _ A E K E' p25519 hv' hsrc hE'⟩

private theorem fe51_mul_chain_props (w : List (BitVec 8)) (E' : Nat) {src1 src2 : List (BitVec 8)} {A E1 E2 : Nat}
    (hb : fe51LimbsBounded w (2 ^ 52) := by assumption)
    (hv : fe51ValOfBytes w % p25519 = (fe51ValOfBytes src1 * fe51ValOfBytes src2) % p25519 := by assumption)
    (hs1 : fe51ValOfBytes src1 % p25519 = A ^ E1 % p25519 := by assumption)
    (hs2 : fe51ValOfBytes src2 % p25519 = A ^ E2 % p25519 := by assumption) (hE' : E1 + E2 = E' := by decide) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 54) ∧ fe51LimbsBounded w (2 ^ 52) ∧ fe51ValOfBytes w % p25519 = A ^ E' % p25519 := by
  have ⟨hl, h0, h1, h2, h3, h4⟩ := hb
  exact ⟨hl, ⟨hl, by omega, by omega, by omega, by omega, by omega⟩, hb, mul_pow_mod_step _ _ _ A E1 E2 E' p25519 hv hs1 hs2 hE'⟩

private theorem fe51_mul_fpPow_props (w : List (BitVec 8)) (E' : Nat) {src1 src2 : List (BitVec 8)} {A E1 E2 : Nat}
    (hb : fe51LimbsBounded w (2 ^ 52) := by assumption)
    (hv : fe51ValOfBytes w % p25519 = (fe51ValOfBytes src1 * fe51ValOfBytes src2) % p25519 := by assumption)
    (hs1 : fe51ValOfBytes src1 % p25519 = A ^ E1 % p25519 := by assumption)
    (hs2 : fe51ValOfBytes src2 % p25519 = A ^ E2 % p25519 := by assumption)
    (hE' : E1 + E2 = E' := by decide) (hlt : E' < 2 ^ 256 := by decide) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 52) ∧ fe51ValOfBytes w % p25519 = fpPow (A % p25519) E' := by
  obtain ⟨hl, _, hb52, hpow⟩ := fe51_mul_chain_props w E' hb hv hs1 hs2 hE'
  exact ⟨hl, hb52, hpow.trans (fpPow_mod_eq_pow_mod A E' hlt).symm⟩

private theorem copy40_fe51_props (dst src : List (BitVec 8)) (V : Nat)
    (hdst : dst.length = 40) (hsrc_b : fe51LimbsBounded src (2 ^ 52)) (hsrc_v : fe51ValOfBytes src % p25519 = V) :
    let res := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      dst 32 (ByteSlice.readLE src 32 8)) 0 (ByteSlice.readLE src 0 8))
      8 (ByteSlice.readLE src 8 8)) 16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8)
    res.length = 40 ∧ fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 = V := by
  have : HasLenGe dst 40 := ⟨by omega⟩; intro res
  have hlen : res.length = 40 := by simp (disch := decide) only [res, write64_length_eq, hdst, Nat.min_eq_left]
  have hb : fe51LimbsBounded res (2 ^ 52) := by
    unfold fe51LimbsBounded; simp (disch := decide) only [res, readLE_write64_self', readLE_write64_ne, write64_length_eq, hdst, Nat.min_eq_left]; exact ⟨trivial, hsrc_b.2⟩
  have hv : fe51ValOfBytes res % p25519 = V := by
    unfold fe51ValOfBytes; simp (disch := decide) only [res, readLE_write64_self', readLE_write64_ne]; exact hsrc_v
  exact ⟨hlen, hb, hv⟩

private theorem sepWP_head_region_sub (sp : BitVec 64) (off off' n m : Nat) {v : BitVec 64}
    {prog : Program} {tpc : BitVec 64} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = (((sp - BitVec.ofNat 64 off) ↦₆₄ v) ∗ memRegion (sp - BitVec.ofNat 64 off') m) ∗ F := by sep_focus)
    (hoff : off = off' + 8 := by decide) (hnm : n = 8 + m := by decide) (hb : n ≤ 2 ^ 64 := by decide)
    (h : SepWP prog tpc s (memRegion (sp - BitVec.ofNat 64 off) n ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  have ha : sp - BitVec.ofNat 64 off + 8#64 = sp - BitVec.ofNat 64 off' := by
    rw [sub_ofNat64_add sp off 8 (by omega), show off - 8 = off' by omega]
  rw [← ha] at hP; exact SepWP.head_region (sp - BitVec.ofNat 64 off) n m hnm hb hP h

local syntax "close_cells_sub " term:max num num num : tactic
macro_rules
  | `(tactic| close_cells_sub $sp $off $n $k) => do
    let (off, n, k) := (off.getNat, n.getNat, k.getNat)
    if k == 0 then `(tactic| skip) else
    if n == 8 then
      let offLit := Lean.Syntax.mkNumLit (toString off)
      `(tactic| apply SepWP.last_region ($sp - BitVec.ofNat 64 $offLit))
    else
      let offLit := Lean.Syntax.mkNumLit (toString off)
      let off'Lit := Lean.Syntax.mkNumLit (toString (off - 8))
      let nLit := Lean.Syntax.mkNumLit (toString n)
      let n'Lit := Lean.Syntax.mkNumLit (toString (n - 8))
      let k'Lit := Lean.Syntax.mkNumLit (toString (k - 1))
      `(tactic| (close_cells_sub $sp $off'Lit $n'Lit $k'Lit; apply sepWP_head_region_sub $sp $offLit $off'Lit $nLit $n'Lit))

public section

set_option maxHeartbeats 1600000 in
/-- Conditional `FieldElement51::pow22501` (`Blk05`, 101 insns) contract. -/
theorem fe51_pow22501_ok_of (hPow2k : Fe51Pow2kOk) (hMul : Fe51MulOk) : Fe51Pow22501Ok := by
  intro _
  apply x25519Caller_ok x25519CliPC05 x25519CliPl05
  intro b hb hbase
  wp_init
  unpack_fe51 h_1
  have ha_pow1 : fe51ValOfBytes a_rest % p25519 = (fe51ValOfBytes a_rest) ^ 1 % p25519 := by rw [Nat.pow_one]
  apply sepWP_split2_80 a_1; intro out0 out1 hout0 hout1
  apply sepWP_split_stack_callee 224 816
  apply sepWP_peel_stack_bytes s0.sp 816 8 808; intro sp_816 h_816; apply sepWP_peel_stack_bytes s0.sp 808 40 768; intro sp_808 h_808
  apply sepWP_peel_stack_bytes s0.sp 768 40 728; intro sp_768 h_768; apply sepWP_peel_stack_bytes s0.sp 728 40 688; intro sp_728 h_728
  apply sepWP_peel_stack_bytes s0.sp 688 40 648; intro sp_688 h_688; apply sepWP_peel_stack_bytes s0.sp 648 40 608; intro sp_648 h_648
  apply sepWP_peel_stack_bytes s0.sp 608 40 568; intro sp_608 h_608; apply sepWP_peel_stack_bytes s0.sp 568 40 528; intro sp_568 h_568
  apply sepWP_peel_stack_bytes s0.sp 528 40 488; intro sp_528 h_528; apply sepWP_peel_stack_bytes s0.sp 488 40 448; intro sp_488 h_488
  apply sepWP_peel_stack_bytes s0.sp 448 40 408; intro sp_448 h_448; apply sepWP_peel_stack_bytes s0.sp 408 40 368; intro sp_408 h_408
  apply sepWP_peel_stack_bytes s0.sp 368 40 328; intro sp_368 h_368; apply sepWP_peel_stack_bytes s0.sp 328 40 288; intro sp_328 h_328
  apply sepWP_peel_stack_bytes s0.sp 288 40 248; intro sp_288 h_288; apply sepWP_peel_stack_bytes s0.sp 248 40 208; intro sp_248 h_248
  apply sepWP_peel_stack_bytes s0.sp 208 40 168; intro sp_208 h_208; apply sepWP_peel_stack_bytes s0.sp 168 40 128; intro sp_168 h_168
  apply sepWP_peel_stack_bytes s0.sp 128 40 88; intro sp_128 h_128; apply sepWP_peel_stack_bytes s0.sp 88 40 48; intro sp_88 h_88
  open_cells (s0.sp - 48#64) 48 6; apply sepWP_callee_224_to_96 s0.sp
  wp_cut_codeLoaded; wp_steps; wp_x25519_call_fast hPow2k; norm_sf 96; obtain ⟨hw_l, hw_b54, hw_b52, hw_v⟩ := fe51_pow2k_chain_props w 2; unpack_fe51 hw_b54
  wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw1_l, hw1_b54, hw1_b52, hw1_v⟩ := fe51_pow2k_chain_props w_1 4; unpack_fe51 hw1_b54
  wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw2_l, hw2_b54, hw2_b52, hw2_v⟩ := fe51_pow2k_chain_props w_2 8; unpack_fe51 hw2_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw3_l, hw3_b54, hw3_b52, hw3_v⟩ := fe51_mul_chain_props w_3 9; unpack_fe51 hw3_b54
  wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw4_l, hw4_b54, hw4_b52, hw4_v⟩ := fe51_mul_chain_props w_4 11; unpack_fe51 hw4_b54; clear ha_pow1
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw5_l, hw5_b54, hw5_b52, hw5_v⟩ := fe51_pow2k_chain_props w_5 22; unpack_fe51 hw5_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw6_l, hw6_b54, hw6_b52, hw6_v⟩ := fe51_mul_chain_props w_6 (2 ^ 5 - 1); unpack_fe51 hw6_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw7_l, hw7_b54, hw7_b52, hw7_v⟩ := fe51_pow2k_chain_props w_7 (2 ^ 10 - 2 ^ 5); unpack_fe51 hw7_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw8_l, hw8_b54, hw8_b52, hw8_v⟩ := fe51_mul_chain_props w_8 (2 ^ 10 - 1); unpack_fe51 hw8_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw9_l, hw9_b54, hw9_b52, hw9_v⟩ := fe51_pow2k_chain_props w_9 (2 ^ 20 - 2 ^ 10); unpack_fe51 hw9_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw10_l, hw10_b54, hw10_b52, hw10_v⟩ := fe51_mul_chain_props w_10 (2 ^ 20 - 1); unpack_fe51 hw10_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw11_l, hw11_b54, hw11_b52, hw11_v⟩ := fe51_pow2k_chain_props w_11 (2 ^ 40 - 2 ^ 20); unpack_fe51 hw11_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw12_l, hw12_b54, hw12_b52, hw12_v⟩ := fe51_mul_chain_props w_12 (2 ^ 40 - 1); unpack_fe51 hw12_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw13_l, hw13_b54, hw13_b52, hw13_v⟩ := fe51_pow2k_chain_props w_13 (2 ^ 50 - 2 ^ 10); unpack_fe51 hw13_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw14_l, hw14_b54, hw14_b52, hw14_v⟩ := fe51_mul_chain_props w_14 (2 ^ 50 - 1); unpack_fe51 hw14_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw15_l, hw15_b54, hw15_b52, hw15_v⟩ := fe51_pow2k_chain_props w_15 (2 ^ 100 - 2 ^ 50); unpack_fe51 hw15_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw16_l, hw16_b54, hw16_b52, hw16_v⟩ := fe51_mul_chain_props w_16 (2 ^ 100 - 1); unpack_fe51 hw16_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw17_l, hw17_b54, hw17_b52, hw17_v⟩ := fe51_pow2k_chain_props w_17 (2 ^ 200 - 2 ^ 100); unpack_fe51 hw17_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw18_l, hw18_b54, hw18_b52, hw18_v⟩ := fe51_mul_chain_props w_18 (2 ^ 200 - 1); unpack_fe51 hw18_b54
  apply sepWP_callee_224_to_96 s0.sp; wp_steps; wp_x25519_call_fast hPow2k; clean_prev_sf2; norm_sf 96; obtain ⟨hw19_l, hw19_b54, hw19_b52, hw19_v⟩ := fe51_pow2k_chain_props w_19 (2 ^ 250 - 2 ^ 50); unpack_fe51 hw19_b54
  apply sepWP_callee_96_to_224 s0.sp; wp_steps; wp_x25519_call_fast hMul; clean_prev_sf2; norm_sf 224; obtain ⟨hw20_l, hw20_b52, hw20_fp⟩ := fe51_mul_fpPow_props w_20 (2 ^ 250 - 1); try clear hpost_20
  have : HasLenGe out1 40 := ⟨by omega⟩; have : HasLenGe w_4 40 := ⟨by omega⟩; wp_steps
  apply sepWP_abstract_bytes (a_1 + 40#64)
    (fun t3_bs => t3_bs.length = 40 ∧ fe51LimbsBounded t3_bs (2 ^ 52) ∧ fe51ValOfBytes t3_bs % p25519 = fpPow (fe51ValOfBytes a_rest % p25519) 11)
    (hQ := copy40_fe51_props out1 w_4 (fpPow (fe51ValOfBytes a_rest % p25519) 11) hout1 hw4_b52 (hw4_v.trans (fpPow_mod_eq_pow_mod (fe51ValOfBytes a_rest) 11 (by decide)).symm))
  intro t3_bs ⟨ht3_l, ht3_b52, ht3_v⟩; unpack_fe51 hw20_b52; unpack_fe51 ht3_b52; apply sepWP_merge2_80 a_1; close_cells_sub s0.sp 48 48 6
  apply sepWP_unpeel_stack_bytes s0.sp 88 40 48; apply sepWP_unpeel_stack_bytes s0.sp 128 40 88
  apply sepWP_unpeel_stack_bytes s0.sp 168 40 128; apply sepWP_unpeel_stack_bytes s0.sp 208 40 168
  apply sepWP_unpeel_stack_bytes s0.sp 248 40 208; apply sepWP_unpeel_stack_bytes s0.sp 288 40 248
  apply sepWP_unpeel_stack_bytes s0.sp 328 40 288; apply sepWP_unpeel_stack_bytes s0.sp 368 40 328
  apply sepWP_unpeel_stack_bytes s0.sp 408 40 368; apply sepWP_unpeel_stack_bytes s0.sp 448 40 408
  apply sepWP_unpeel_stack_bytes s0.sp 488 40 448; apply sepWP_unpeel_stack_bytes s0.sp 528 40 488
  apply sepWP_unpeel_stack_bytes s0.sp 568 40 528; apply sepWP_unpeel_stack_bytes s0.sp 608 40 568
  apply sepWP_unpeel_stack_bytes s0.sp 648 40 608; apply sepWP_unpeel_stack_bytes s0.sp 688 40 648
  apply sepWP_unpeel_stack_bytes s0.sp 728 40 688; apply sepWP_unpeel_stack_bytes s0.sp 768 40 728
  apply sepWP_unpeel_stack_bytes s0.sp 808 40 768; apply sepWP_unpeel_stack_bytes s0.sp 816 8 808
  apply sepWP_merge_stack_callee 224 816; wp_done


/-- `FieldElement51::pow22501` (`Blk05`, 101 insns). -/
theorem fe51_pow22501_ok : Fe51Pow22501Ok :=
  fe51_pow22501_ok_of fe51_pow2k_ok fe51_mul_ok

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Pow
