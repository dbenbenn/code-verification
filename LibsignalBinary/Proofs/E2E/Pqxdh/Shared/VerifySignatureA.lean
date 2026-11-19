/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.CodeLayout
/-!
# `<PublicKey>::verify_signature` (`0x3dd4c`) and `verify_signature_for_multipart_message` (`0x3dd74`)

Proves `verifySignatureMultipart_sepWP` (`verifySignatureMultipart_base_ok`) and
`verifySignature_sepWP` (`verifySignature_base_ok`) on `tripleRatchetProgAt` and
`tripleRatchetProgAtExt`.
-/

public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
namespace CryptoVerification.E2E.Pqxdh.Shared
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open SignalPqxdh SignalPqxdh.Model
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
private theorem calleeSavedVRegs_setPC_pre_trap (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := calleeSavedVRegs_setPC s pc
private theorem calleeSavedVRegs_setMem_setPC_pre_trap (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ((s.setMem m).setPC pc) = calleeSavedVRegs s := by
  rw [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  calleeSavedVRegs_setPC_pre_trap calleeSavedVRegs_setMem_setPC_pre_trap
structure RoQuad64 (m : Memory) (ea v1 v2 v3 v4 : BitVec 64) : Prop where
  read0 : m.read64 ea = v1
  read8 : m.read64 (ea + 8#64) = v2
  read16 : m.read64 (ea + 16#64) = v3
  read24 : m.read64 (ea + 24#64) = v4
  canRead0 : m.canRead ea 8 = true
  canRead8 : m.canRead (ea + 8#64) 8 = true
  canRead16 : m.canRead (ea + 16#64) 8 = true
  canRead24 : m.canRead (ea + 24#64) 8 = true
theorem RoQuad64.of_holdsBytes {m : Memory} {ea v1 v2 v3 v4 : BitVec 64} {bs : List (BitVec 8)}
    (h : Obj.HoldsBytes m ea bs (fun _ => Perm.ro))
    (hbs : bs = unpack64 v1 ++ unpack64 v2 ++ unpack64 v3 ++ unpack64 v4) :
    RoQuad64 m ea v1 v2 v3 v4 := by
  rw [hbs, List.append_assoc, List.append_assoc] at h; obtain ⟨h1, hrest1⟩ := holdsBytes_append h
  obtain ⟨h2, hrest2⟩ := holdsBytes_append hrest1; obtain ⟨h3, h4⟩ := holdsBytes_append hrest2
  simp only [unpack64_length, BitVec.add_assoc] at h2 h3 h4
  obtain ⟨hc1, hr1⟩ := memSlice_of_holdsBytes_ro h1
  obtain ⟨hc2, hr2⟩ := memSlice_of_holdsBytes_ro h2
  obtain ⟨hc3, hr3⟩ := memSlice_of_holdsBytes_ro h3
  obtain ⟨hc4, hr4⟩ := memSlice_of_holdsBytes_ro h4
  exact ⟨Memory.read64_of_readBytes_eq_unpack64 m _ _ hr1,
    Memory.read64_of_readBytes_eq_unpack64 m _ _ hr2,
    Memory.read64_of_readBytes_eq_unpack64 m _ _ hr3,
    Memory.read64_of_readBytes_eq_unpack64 m _ _ hr4, hc1, hc2, hc3, hc4⟩
@[expose, irreducible] def roStop (pc : BitVec 64) : BitVec 64 := pc
theorem reaches_pc_keepsFrozen {prog : Program} {target_pc : BitVec 64} {s : State}
    {Q : State → Prop} (h : reaches_pc prog target_pc s Q) :
    reaches_pc prog target_pc s (fun sf => s.mem.KeepsFrozen sf.mem ∧ Q sf) := by
  intro hL; obtain ⟨sf, hsteps, ⟨hpc, hrun, hQ⟩ | hoom⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hsteps.keepsFrozen, hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩
theorem SepWP.done_ro {prog : Program} {mid : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} (hpc : s.pc = mid)
    (hrun : s.status = .Running) (hpost : post s P) : SepWP prog (roStop mid) s P post := by
  unfold roStop; exact SepWP.done hpc hrun hpost
theorem SepWP.step_ldpSimd128_ro {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea' ea2 ea3 ea4 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 v3 v4 : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .Q128 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hea3 : ea + 16#64 = ea3) (hea4 : ea3 + 8#64 = ea4)
    (hro : RoQuad64 s.mem ea' v1 v2 v3 v4) (hea : ea' = ea)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 (v2 ++ v1)).writeVReg128 vt2 (v4 ++
      v3)).setPC (pc + 4#64) = s') (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  subst hea
  have hs_pc : s.setPC pc = s := by
    cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hread1 : s.mem.read64 ea' = v1 := hro.read0
  have hread2 : s.mem.read64 ea2 = v2 := hea2 ▸ hro.read8
  have hread3 : s.mem.read64 ea3 = v3 := hea3 ▸ hro.read16
  have hread4 : s.mem.read64 ea4 = v4 := by
    have h24 : ea' + 24#64 = ea4 := by rw [← hea4, ← hea3, BitVec.add_assoc]; rfl
    exact h24 ▸ hro.read24
  have hcan1 : s.mem.canRead ea' 8 = true := hro.canRead0
  have hcan2 : s.mem.canRead ea2 8 = true := hea2 ▸ hro.canRead8
  have hcan3 : s.mem.canRead ea3 8 = true := hea3 ▸ hro.canRead16
  have hcan4 : s.mem.canRead ea4 8 = true := by
    have h24 : ea' + 24#64 = ea4 := by rw [← hea4, ← hea3, BitVec.add_assoc]; rfl
    exact h24 ▸ hro.canRead24
  have hcan_lo : s.mem.canRead ea' 16 = true := Memory.canRead_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  have hcan_hi : s.mem.canRead ea3 16 = true := Memory.canRead_16_of_8_8 hcan3 (hea4.symm ▸ hcan4)
  have hstep : execInst (.ldpSimd .Q128 vt1 vt2 addr) (s.setPC pc) = s' := by
    rw [hs_pc, ← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.readSimdSized, Memory.read128, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hea3, hea4,
      hread1, hread2, hread3, hread4, hcan_lo, hcan_hi, SimdMemSize.bytes, hpc]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]; cases wb <;> rfl
  exact SepWP.step_pure hpc hrun hfetch hstep hmem hnext
macro "wp_step_ldp_ro " hquad:term:max : tactic =>
  `(tactic| (
    apply SepWP.step_ldpSimd128_ro
    wp_focus_close wp_norm_lhs
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_assumption | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close wp_norm_lhs
    wp_focus_close wp_norm_lhs
    wp_focus_close wp_norm_lhs
    wp_focus_close wp_norm_lhs
    wp_focus_close (exact $hquad)
    wp_focus_close (first | rfl | wp_assumption | (simp only [*, BitVec.add_assoc,
                                                   BitVec.reduceAdd]; done) | (bv_omega; done))
    wp_focus_close wp_norm_lhs
  ))
macro "wp_ldp_ro " f:term:max : tactic =>
  `(tactic| (
    apply SepWP.done_ro (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hro_ldp
    wp_step_ldp_ro ($f _hro_ldp)))
theorem and_pageMask_eq_sub_and_fff (x : BitVec 64) :
    x &&& 0xfffffffffffff000#64 = x - (x &&& 0xfff#64) := by bv_bits
theorem aligned_and_fff {b : BitVec 64} (hb : b.toNat % Arm64.Obj.pageSize = 0) :
    b &&& 0xfff#64 = 0#64 := by
  simp only [Arm64.Obj.pageSize] at hb; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.and_two_pow_sub_one_eq_mod _ 12, hb]
theorem bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit',
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]))
macro "wp_simp_pre_fast " "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (conv => arg 4; simp only [$rules,*]))
macro "wp_extract_exists" : tactic =>
  `(tactic| (
    (conv =>
      arg 4
      simp (config := { maxSteps := 1000000 }) only [
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    repeat' (apply SepWP.exists_elim; intro _)
    try (apply SepWP.pure_elim; intro _)))
theorem bytesToBv8_append (xs ys : Bytes) :
    bytesToBv8 (xs ++ ys) = bytesToBv8 xs ++ bytesToBv8 ys := by simp [bytesToBv8]
theorem bytesToBv8_inj {xs ys : Bytes} (h : bytesToBv8 xs = bytesToBv8 ys) : xs = ys := by
  have h1 := congrArg (List.map (fun b : BitVec 8 => UInt8.ofBitVec b)) h
  simpa [bytesToBv8, List.map_map, Function.comp_def] using h1
theorem exists_unpack64_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
            ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗
            ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : (bs.drop 32).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, hp1]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem cells_10_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ⊢ cells a 10 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <| Entails.refl _
@[expose] def pqxdhCtEqSliceSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec
    64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6
@[expose] def sha512IVBytesLE : List (BitVec 8) := bytesToBv8 (revWords64 sha512InitState)
theorem sha512IVBytesLE_eq_unpack64 : sha512IVBytesLE =
      (unpack64 0x6a09e667f3bcc908#64 ++ unpack64 0xbb67ae8584caa73b#64 ++
       unpack64 0x3c6ef372fe94f82b#64 ++ unpack64 0xa54ff53a5f1d36f1#64) ++
      (unpack64 0x510e527fade682d1#64 ++ unpack64 0x9b05688c2b3e6c1f#64 ++
       unpack64 0x1f83d9abfb41bd6b#64 ++ unpack64 0x5be0cd19137e2179#64) := by decide

theorem StructuralPrims.montToEd_len {P : Primitives} (_hWF : StructuralPrims P)
    (u : Bytes) (s : UInt8) (pt : Bytes) (h : P.montToEdBytes u s = some pt) :
    pt.length = 160 :=
  P.montToEdBytes_len u s pt h

theorem StructuralPrims.edNeg_len {P : Primitives} (_hWF : StructuralPrims P) (pt : Bytes) :
    (P.edNegBytes pt).length = 160 :=
  P.edNegBytes_len pt

theorem StructuralPrims.doubleScalarMulBasepoint_len {P : Primitives} (_hWF : StructuralPrims P)
    (h a s : Bytes) : (P.doubleScalarMulBasepointBytes h a s).length = 160 :=
  P.doubleScalarMulBasepointBytes_len h a s

theorem StructuralPrims.compressBytes_len {P : Primitives} (hWF : StructuralPrims P) (pt : Bytes) :
    (P.compressBytes pt).length = 32 :=
  P.compressBytes_len hWF.compress_len pt

def xeddsaVerifyBinRef (P : Primitives) (pk m sig : Bytes) : Bool :=
  if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
    let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    match P.montToEd pk signBit with
    | none => false
    | some edPk =>
      let capA := P.compress edPk; let minusCapA := P.edNeg edPk; let capR := sig.take 32
      let sRaw := sig.drop 32; let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
      let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
      let sScalar := P.scalarFromBytesModOrder sClamped
      let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
      capRCheck == capR
  else false
theorem uint8_ubfm7_eq_signBit (b : UInt8) :
    BitVec.zeroExtend 64 ((BitVec.zeroExtend 32 b.toBitVec).extractLsb 31 7) =
      BitVec.ofNat 64 (((b &&& 0x80) >>> 7).toNat) := by
  rcases b with ⟨bv⟩; revert bv; decide
theorem uint8_and7f_ult32_iff (b : UInt8) :
    (BitVec.zeroExtend 32 b.toBitVec &&& 0x7f#32).ult 32#32 = ((b &&& 0x60) == 0) := by
  rcases b with ⟨bv⟩; revert bv; decide
theorem fitBytes_eq_fitBytesRef (n : Nat) (bs : Bytes) : fitBytes n bs = fitBytesRef n bs := rfl
theorem revWords64_length {bs : Bytes} (h : bs.length = 64) : (revWords64 bs).length = 64 := by
  simp [revWords64, h]
theorem list_split8_64 {α : Type} (bs : List α) (h : bs.length = 64) :
    bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ ((bs.drop 24).take 8 ++
      ((bs.drop 32).take 8 ++ ((bs.drop 40).take 8 ++ ((bs.drop 48).take 8 ++
        (bs.drop 56).take 8)))))) := by
  have h56 : (bs.drop 56).take 8 = bs.drop 56 := List.take_of_length_le (by simp [h])
  have s7 : bs.drop 48 = (bs.drop 48).take 8 ++ bs.drop 56 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 48)).symm
  have s6 : bs.drop 40 = (bs.drop 40).take 8 ++ bs.drop 48 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 40)).symm
  have s5 : bs.drop 32 = (bs.drop 32).take 8 ++ bs.drop 40 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 32)).symm
  have s4 : bs.drop 24 = (bs.drop 24).take 8 ++ bs.drop 32 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 24)).symm
  have s3 : bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop 24 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 16)).symm
  have s2 : bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop 16 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 8)).symm
  have s1 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  rw [h56, ← s7, ← s6, ← s5, ← s4, ← s3, ← s2, ← s1]
theorem revWords64_of_append8 {w0 w1 w2 w3 w4 w5 w6 w7 : Bytes}
    (h0 : w0.length = 8) (h1 : w1.length = 8) (h2 : w2.length = 8) (h3 : w3.length = 8)
    (h4 : w4.length = 8) (h5 : w5.length = 8) (h6 : w6.length = 8) (h7 : w7.length = 8) :
    revWords64 (w0 ++ (w1 ++ (w2 ++ (w3 ++ (w4 ++ (w5 ++ (w6 ++ w7))))))) =
      w0.reverse ++ (w1.reverse ++ (w2.reverse ++ (w3.reverse ++
        (w4.reverse ++ (w5.reverse ++ (w6.reverse ++ w7.reverse)))))) := by
  unfold revWords64; simp only [List.take_left' h0, List.drop_left' h0,
    show (16 : Nat) = 8 + 8 from rfl, ← List.drop_drop, List.take_left' h1, List.drop_left' h1,
    show (24 : Nat) = 8 + (8 + 8) from rfl, List.take_left' h2, List.drop_left' h2,
    show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl, List.take_left' h3, List.drop_left' h3,
    show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) from rfl, List.take_left' h4, List.drop_left' h4,
    show (48 : Nat) = 8 + (8 + (8 + (8 + (8 + 8)))) from rfl,
    List.take_left' h5, List.drop_left' h5,
    show (56 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + 8))))) from rfl,
    List.take_left' h6, List.drop_left' h6,
    List.take_of_length_le (Nat.le_of_eq h7), List.append_assoc]
theorem revWords64_involutive {bs : Bytes} (h : bs.length = 64) :
    revWords64 (revWords64 bs) = bs := by
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 24).take 8).length = 8 := by simp [h]
  have h4 : ((bs.drop 32).take 8).length = 8 := by simp [h]
  have h5 : ((bs.drop 40).take 8).length = 8 := by simp [h]
  have h6 : ((bs.drop 48).take 8).length = 8 := by simp [h]
  have h7 : ((bs.drop 56).take 8).length = 8 := by simp [h]
  conv => lhs; arg 1; rw [list_split8_64 bs h]
  rw [revWords64_of_append8 h0 h1 h2 h3 h4 h5 h6 h7,
    revWords64_of_append8 (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [h3])
      (by simp [h4]) (by simp [h5]) (by simp [h6]) (by simp [h7])]
  simp only [List.reverse_reverse]; exact (list_split8_64 bs h).symm
theorem sha512CompressOutBytes_length (P : Primitives) (st blk : Bytes) :
    (sha512CompressOutBytes P st blk).length = 64 := by
  apply revWords64_length; exact fitBytes_length 64 _
theorem sha512Step_length (P : Primitives) (st blk : Bytes) : (sha512Step P st blk).length = 64 :=
  fitBytesRef_length 64 _
theorem foldl_sha512Step_length (P : Primitives) (blks : List Bytes) (st : Bytes)
    (hst : st.length = 64) : (blks.foldl (sha512Step P) st).length = 64 := by
  induction blks generalizing st with
  | nil => exact hst
  | cons b rest ih => exact ih (sha512Step P st b) (sha512Step_length P st b)
theorem revWords64_sha512CompressOutBytes_of_len (P : Primitives) {st blk : Bytes}
    (hst : st.length = 64) : revWords64 (sha512CompressOutBytes P st blk) =
      (chunkBlocks 128 blk).foldl (sha512Step P) (revWords64 st) := by
  unfold sha512CompressOutBytes
  rw [revWords64_involutive (fitBytes_length 64 _), fitBytes_eq_fitBytesRef,
    fitBytesRef_of_length_eq (foldl_sha512Step_length P _ _ (revWords64_length hst))]
theorem sha512Ref_of_length_97 (P : Primitives) {msg : Bytes} (h : msg.length = 97) :
    sha512Ref P msg = revWords64 (sha512CompressOutBytes P (revWords64 sha512InitState)
        (msg ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 97)) := by
  have hpad_eq : sha512Pad msg = msg ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 97 := by
    unfold sha512Pad; rw [h]; rfl
  have hinit_len : sha512InitState.length = 64 := rfl
  rw [revWords64_sha512CompressOutBytes_of_len P (revWords64_length hinit_len),
    revWords64_involutive hinit_len, ← hpad_eq]
  unfold sha512Ref; rw [fitBytesRef_of_length_eq (foldl_sha512Step_length P _ _ hinit_len)]
theorem list_range_add (m n : Nat) :
    List.range (m + n) = List.range m ++ (List.range n).map (m + ·) := by
  induction n with
  | zero => simp
  | succ n ih => rw [← Nat.add_assoc, List.range_succ, List.range_succ, ih]; simp
theorem chunkBlocks_128_append {a b : Bytes} (k m : Nat)
    (ha : a.length = k * 128) (hb : b.length = m * 128) :
    chunkBlocks 128 (a ++ b) = chunkBlocks 128 a ++ chunkBlocks 128 b := by
  unfold chunkBlocks; dsimp only
  have hab : (a ++ b).length / 128 = k + m := by rw [List.length_append, ha, hb]; omega
  have ha_div : a.length / 128 = k := by rw [ha]; omega
  have hb_div : b.length / 128 = m := by rw [hb]; omega
  rw [hab, ha_div, hb_div, list_range_add k m, List.map_append, List.map_map]; congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi; have hle : i * 128 + 128 ≤ a.length := by rw [ha]; omega
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · apply List.map_congr_left
    intro i _
    have hmul : (k + i) * 128 = a.length + i * 128 := by rw [ha, Nat.add_mul]
    simp only [Function.comp_apply, hmul, ← List.drop_drop, List.drop_left]
theorem sha512Ref_of_length_1633 (P : Primitives) {blk0 blks1_11 tail97 : Bytes}
    (h0 : blk0.length = 128) (h11 : blks1_11.length = 1408) (ht : tail97.length = 97) :
    sha512Ref P (blk0 ++ blks1_11 ++ tail97) =
      let st0 := revWords64 sha512InitState
      let st1 := sha512CompressOutBytes P st0 blk0; let st2 := sha512CompressOutBytes P st1 blks1_11
      let padBlk := tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633
      revWords64 (sha512CompressOutBytes P st2 padBlk) := by
  dsimp only; have hinit_len : sha512InitState.length = 64 := rfl
  have hst0_len : (revWords64 sha512InitState).length = 64 := revWords64_length hinit_len
  have hst1_len : (sha512CompressOutBytes P (revWords64 sha512InitState) blk0).length = 64 :=
    sha512CompressOutBytes_length P _ _
  have hst2_len : (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64 sha512InitState)
    blk0) blks1_11).length = 64 := sha512CompressOutBytes_length P _ _
  rw [revWords64_sha512CompressOutBytes_of_len P hst2_len,
    revWords64_sha512CompressOutBytes_of_len P hst1_len,
    revWords64_sha512CompressOutBytes_of_len P hst0_len,
    revWords64_involutive hinit_len, ← List.foldl_append, ← List.foldl_append]
  have hpad_len : (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633).length =
    1 * 128 := by
    simp [encodeBitLen128BE, encodeBitLen64BE, ht]
  have h011_len : (blk0 ++ blks1_11).length = 12 * 128 := by simp [h0, h11]
  rw [← List.append_assoc (chunkBlocks 128 blk0),
    ← chunkBlocks_128_append (a := blk0) (b := blks1_11) 1 11 (by omega) (by omega),
    ← chunkBlocks_128_append 12 1 h011_len hpad_len]
  have htot_len : (blk0 ++ blks1_11 ++ tail97).length = 1633 := by simp [h0, h11, ht]
  have hpad_eq : sha512Pad (blk0 ++ blks1_11 ++ tail97) =
      (blk0 ++ blks1_11) ++ (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633) :=
        by
    unfold sha512Pad; rw [htot_len]; simp [List.append_assoc]
  rw [← hpad_eq]; unfold sha512Ref
  rw [fitBytesRef_of_length_eq (foldl_sha512Step_length P _ _ hinit_len)]
theorem unpack64_rev64_eq_reverse (w : BitVec 64) : unpack64 (rev64 w) = (unpack64 w).reverse := by
  simp only [unpack64, rev64, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.cons.injEq, and_true]
  generalize w.extractLsb' 0 8 = b0
  generalize w.extractLsb' 8 8 = b1
  generalize w.extractLsb' 16 8 = b2
  generalize w.extractLsb' 24 8 = b3
  generalize w.extractLsb' 32 8 = b4
  generalize w.extractLsb' 40 8 = b5
  generalize w.extractLsb' 48 8 = b6
  generalize w.extractLsb' 56 8 = b7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
theorem bytesToBv8_reverse (bs : Bytes) : bytesToBv8 bs.reverse = (bytesToBv8 bs).reverse := by
  simp [bytesToBv8, List.map_reverse]
def unpackL (ws : List (BitVec 64)) : List (BitVec 8) := ws.flatMap unpack64
theorem pointsToBytes_unpack8 (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (a ↦ₛ unpackL [w0, w1, w2, w3, w4, w5, w6, w7]) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
        ((a + 56#64) ↦₆₄ w7)) := by
  simp only [unpackL, List.flatMap_cons, List.flatMap_nil, List.append_nil, pointsToBytes_append,
    unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
theorem exists_unpackL8_revWords64 {bs : Bytes} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      bytesToBv8 bs = unpackL [w0, w1, w2, w3, w4, w5, w6, w7] ∧ bytesToBv8 (revWords64 bs) =
        unpackL [rev64 w0, rev64 w1, rev64 w2, rev64 w3, rev64 w4, rev64 w5, rev64 w6, rev64 w7] :=
        by
  have h0 : (bytesToBv8 (bs.take 8)).length = 8 := by simp [bytesToBv8, h]
  have h1 : (bytesToBv8 ((bs.drop 8).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h2 : (bytesToBv8 ((bs.drop 16).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h3 : (bytesToBv8 ((bs.drop 24).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h4 : (bytesToBv8 ((bs.drop 32).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h5 : (bytesToBv8 ((bs.drop 40).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h6 : (bytesToBv8 ((bs.drop 48).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h7 : (bytesToBv8 ((bs.drop 56).take 8)).length = 8 := by simp [bytesToBv8, h]
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 h0
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 h1
  obtain ⟨w2, hw2⟩ := exists_unpack64_of_length_8 h2
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 h3
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 h4
  obtain ⟨w5, hw5⟩ := exists_unpack64_of_length_8 h5
  obtain ⟨w6, hw6⟩ := exists_unpack64_of_length_8 h6
  obtain ⟨w7, hw7⟩ := exists_unpack64_of_length_8 h7
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, ?_, ?_⟩
  · conv => lhs; arg 1; rw [list_split8_64 bs h]
    simp only [bytesToBv8_append, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      unpackL, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · unfold revWords64
    simp only [bytesToBv8_append, bytesToBv8_reverse, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      ← unpack64_rev64_eq_reverse,
      unpackL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
theorem exists_unpack64_revWords64_of_length_64 {bs : Bytes} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64, (∀ a : BitVec 64, (a ↦ₛ bytesToBv8 bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
            ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
            ((a + 56#64) ↦₆₄ w7))) ∧ (∀ b : BitVec 64, (b ↦ₛ bytesToBv8 (revWords64 bs)) =
          ((b ↦₆₄ rev64 w0) ∗ ((b + 8#64) ↦₆₄ rev64 w1) ∗ ((b + 16#64) ↦₆₄ rev64 w2) ∗
            ((b + 24#64) ↦₆₄ rev64 w3) ∗ ((b + 32#64) ↦₆₄ rev64 w4) ∗ ((b + 40#64) ↦₆₄ rev64 w5) ∗
            ((b + 48#64) ↦₆₄ rev64 w6) ∗ ((b + 56#64) ↦₆₄ rev64 w7))) := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hbs, hrev⟩ := exists_unpackL8_revWords64 h
  exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => by rw [hbs, pointsToBytes_unpack8],
    fun b => by rw [hrev, pointsToBytes_unpack8]⟩
@[expose] def first7 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8]
def last7 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]
theorem cell_split7 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦ₛ first7 v) ∗ ((a + 7#64) ↦₈ v.extractLsb' 56 8)) := by
  rw [pointsTo64_eq_pointsToBytes, show unpack64 v = first7 v ++ [v.extractLsb' 56 8] from rfl,
    pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  rfl
theorem cell_split1 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦₈ v.extractLsb' 0 8) ∗ ((a + 1#64) ↦ₛ last7 v)) := by
  rw [pointsTo64_eq_pointsToBytes, show unpack64 v = v.extractLsb' 0 8 :: last7 v from rfl,
    pointsToBytes_cons]
theorem cell_pack1 (a : BitVec 64) (b0 : BitVec 8) : (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜w.extractLsb' 0 8 = b0⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes (a + 1#64) 7 (by decide)]
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine Entails.sepExists_elim fun junk => Entails.pure_left fun hj => ?_
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := b0 :: junk) (by simp [hj])
  have hext : w.extractLsb' 0 8 = b0 := by
    have h := congrArg (fun l => l.getD 0 0#8) hw; simp [unpack64] at h; exact h.symm
  refine Entails.sepExists_right w (Entails.pure_right hext ?_)
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons]; exact Entails.refl _
theorem cell_pack7 (a : BitVec 64) (b7 : BitVec 8) : memRegion a 7 ∗ ((a + 7#64) ↦₈ b7) ⊢
      ∃∗ w : BitVec 64, ⌜w.extractLsb' 56 8 = b7⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes a 7 (by decide)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Entails.sepExists_elim fun junk => Entails.pure_left fun hj => ?_
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := junk ++ [b7]) (by simp [hj])
  have hext : w.extractLsb' 56 8 = b7 := by
    have h := congrArg (fun l => l.drop 7) hw; rw [List.drop_left' hj] at h; simp [unpack64] at h
    exact h.symm
  refine Entails.sepExists_right w (Entails.pure_right hext ?_)
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_append, hj, pointsToBytes_cons,
    pointsToBytes_nil, sepConj_emp]
  exact Entails.refl _
theorem list_capS_split {sig : Bytes} (hsig : sig.length = 64) :
    (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F] =
      (sig.drop 32).take 15 ++ ((sig.drop 47).take 16 ++ [sig.getD 63 0 &&& 0x7F]) := by
  rcases sig with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | ⟨b32, _ | ⟨b33, _ | ⟨b34, _ | ⟨b35, _ | ⟨b36, _ | ⟨b37, _ | ⟨b38, _ | ⟨b39,
    _ | ⟨b40, _ | ⟨b41, _ | ⟨b42, _ | ⟨b43, _ | ⟨b44, _ | ⟨b45, _ | ⟨b46, _ | ⟨b47,
    _ | ⟨b48, _ | ⟨b49, _ | ⟨b50, _ | ⟨b51, _ | ⟨b52, _ | ⟨b53, _ | ⟨b54, _ | ⟨b55,
    _ | ⟨b56, _ | ⟨b57, _ | ⟨b58, _ | ⟨b59, _ | ⟨b60, _ | ⟨b61, _ | ⟨b62, _ | ⟨b63, _ |
      _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at hsig)
  rfl
theorem uint8_and7f_bv8 (u : UInt8) :
    (BitVec.ofNat 8 u.toNat) &&& 0x7f#8 = BitVec.ofNat 8 (u &&& 0x7F).toNat := by
  rcases u with ⟨bv⟩; revert bv; decide
theorem bytesToBv8_getD_eq (bs : Bytes) (i : Nat) :
    (bytesToBv8 bs).getD i 0#8 = BitVec.ofNat 8 (bs.getD i 0).toNat := by
  induction bs generalizing i with
  | nil => simp [bytesToBv8]
  | cons b rest ih =>
    cases i with
    | zero => simp [bytesToBv8]
    | succ j => exact ih j
theorem exists_sig_capS_cells {sig : Bytes} (hsig : sig.length = 64) :
    ∃ q0_lo q0_hi q1_lo q1_hi : BitVec 64, (∀ p : BitVec 64, (p ↦ₛ bytesToBv8 sig) =
          ((p ↦ₛ bytesToBv8 (sig.take 32)) ∗ ((p + 32#64) ↦₆₄ q0_lo) ∗ ((p + 40#64) ↦₆₄ q0_hi) ∗
           ((p + 48#64) ↦ₛ bytesToBv8 (sig.drop 48)))) ∧ (∀ p : BitVec 64, (p ↦ₛ bytesToBv8 sig) =
          ((p ↦ₛ bytesToBv8 (sig.take 47)) ∗ ((p + 47#64) ↦₆₄ q1_lo) ∗ ((p + 55#64) ↦₆₄ q1_hi) ∗
           ((p + 63#64) ↦ₛ bytesToBv8 (sig.drop 63)))) ∧ (∀ a : BitVec 64,
        ((a ↦₆₄ q0_lo) ∗ ((a + 8#64) ↦₆₄ q0_hi)) ∗ memRegion (a + 16#64) 15 ⊢
          (a ↦ₛ bytesToBv8 ((sig.drop 32).take 15)) ∗
          (∃∗ v0, (a + 15#64) ↦₆₄ v0) ∗ (∃∗ v1, (a + 23#64) ↦₆₄ v1)) ∧ (∀ a : BitVec 64,
        (a ↦ₛ bytesToBv8 ((sig.drop 32).take 15)) ∗
          ((a + 15#64) ↦₆₄ q1_lo) ∗ ((a + 23#64) ↦₆₄ q1_hi) ∗
          ((a + 31#64) ↦₈ ((bytesToBv8 sig).getD 63 0#8 &&& 0x7f#8)) =
          (a ↦ₛ bytesToBv8 ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]))) := by
  have h16a : (bytesToBv8 ((sig.drop 32).take 16)).length = 16 := by simp [bytesToBv8, hsig]
  have h16b : (bytesToBv8 ((sig.drop 47).take 16)).length = 16 := by simp [bytesToBv8, hsig]
  obtain ⟨q0_lo, q0_hi, hq0_eq, hq0_pts⟩ := exists_unpack64_of_length_16 h16a
  obtain ⟨q1_lo, q1_hi, hq1_eq, hq1_pts⟩ := exists_unpack64_of_length_16 h16b
  refine ⟨q0_lo, q0_hi, q1_lo, q1_hi, fun p => ?_, fun p => ?_, fun a => ?_, fun a => ?_⟩
  · have hsp : sig = sig.take 32 ++ ((sig.drop 32).take 16 ++ sig.drop 48) := by
      rw [show (48 : Nat) = 32 + 16 from rfl, ←
        List.drop_drop, List.take_append_drop, List.take_append_drop]
    conv => lhs; arg 2; arg 1; rw [hsp]
    have ht32 : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
    simp only [bytesToBv8_append, pointsToBytes_append, ht32, h16a, hq0_pts,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · have hsp : sig = sig.take 47 ++ ((sig.drop 47).take 16 ++ sig.drop 63) := by
      rw [show (63 : Nat) = 47 + 16 from rfl, ←
        List.drop_drop, List.take_append_drop, List.take_append_drop]
    conv => lhs; arg 2; arg 1; rw [hsp]
    have ht47 : (bytesToBv8 (sig.take 47)).length = 47 := by simp [bytesToBv8, hsig]
    simp only [bytesToBv8_append, pointsToBytes_append, ht47, h16b, hq1_pts,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · rw [← hq0_pts a]
    have hsp16 : (sig.drop 32).take 16 = (sig.drop 32).take 15 ++ ((sig.drop 32).drop 15).take 1 :=
      by
      rw [show (16 : Nat) = 15 + 1 from rfl, List.take_add]
    have ht15 : (bytesToBv8 ((sig.drop 32).take 15)).length = 15 := by simp [bytesToBv8, hsig]
    have hd1 : (bytesToBv8 (((sig.drop 32).drop 15).take 1)).length = 1 := by
      simp [bytesToBv8, hsig]
    rw [hsp16, bytesToBv8_append, pointsToBytes_append, ht15, sepConj_assoc]
    refine sepConj_mono_right ?_
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion _ _)) ?_
    rw [hd1, ← ProofLib.memRegion_split' (b := a + 15#64) (n := 1) (k := 15) (b' :=
      a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 15#64) (n := 8) (k := 8) (b' :=
        a + 23#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    exact Entails.refl _
  · symm
    rw [list_capS_split hsig]
    have ht15 : (bytesToBv8 ((sig.drop 32).take 15)).length = 15 := by simp [bytesToBv8, hsig]
    have hq1_at : ((a + 15#64) ↦ₛ bytesToBv8 ((sig.drop 47).take 16)) =
        (((a + 15#64) ↦₆₄ q1_lo) ∗ ((a + 23#64) ↦₆₄ q1_hi)) := by
      have := hq1_pts (a + 15#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this
      exact this
    rw [bytesToBv8_append, bytesToBv8_append,
      pointsToBytes_append, pointsToBytes_append, ht15, h16b, hq1_at,
      bytesToBv8_getD_eq, uint8_and7f_bv8]
    simp only [bytesToBv8, List.map_cons, List.map_nil, pointsToBytes_cons, pointsToBytes_nil,
      sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem blockBuf_tail32_pack (q : BitVec 64) (b0 b7 : BitVec 8) :
    (q ↦₈ b0) ∗ memRegion (q + 1#64) 30 ∗ ((q + 31#64) ↦₈ b7) ⊢ ∃∗ b12, ∃∗ b13, ∃∗ b14, ∃∗ b15,
        ⌜b12.extractLsb' 0 8 = b0 ∧ b15.extractLsb' 56 8 = b7⌝ ∗
        ((q ↦₆₄ b12) ∗ ((q + 8#64) ↦₆₄ b13) ∗ ((q + 16#64) ↦₆₄ b14) ∗ ((q + 24#64) ↦₆₄ b15)) := by
  rw [ProofLib.memRegion_eq_exists_bytes (q + 1#64) 30 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun junk => ?_; rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hj => ?_; have h31 : (b0 :: junk).length = 31 := by simp [hj]
  obtain ⟨b12, b13, b14, b15, hw, hp⟩ := exists_unpack64_of_length_32
    (bs := (b0 :: junk) ++ [b7]) (by simp [hj])
  have hb12 : b12.extractLsb' 0 8 = b0 := by
    have h := congrArg (fun l => l.getD 0 0#8) hw; simp [unpack64] at h; exact h.symm
  have hb15 : b15.extractLsb' 56 8 = b7 := by
    have h := congrArg (fun l => l.drop 31) hw; rw [List.drop_left' h31] at h; simp [unpack64] at h
    exact h.symm
  refine Entails.sepExists_right b12 (Entails.sepExists_right b13
    (Entails.sepExists_right b14 (Entails.sepExists_right b15 (Entails.pure_right ⟨hb12,
      hb15⟩ ?_))))
  have hpq := hp q; simp only [pointsToBytes_append, h31, pointsToBytes_cons,
    pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, sepConj_assoc] at hpq
  rw [← hpq]
  exact Entails.refl _
theorem blockBuf_tail32_unpack (q b12 b13 b14 b15 : BitVec 64) (b0 b7 : BitVec 8)
    (hb12 : b12.extractLsb' 0 8 = b0) : (q ↦₆₄ b12) ∗ ((q + 8#64) ↦₆₄ b13) ∗ ((q + 16#64) ↦₆₄ b14) ∗
      ((q + 24#64) ↦ₛ first7 b15) ∗ ((q + 31#64) ↦₈ b7) ⊢
      (q ↦₈ b0) ∗ (∃∗ c, (q + 1#64) ↦₈ c) ∗ memRegion (q + 2#64) 30 := by
  rw [cell_split1 q b12, hb12, sepConj_assoc]
  refine sepConj_mono_right ?_
  have hl7 : (last7 b12).length = 7 := rfl
  have hf7 : (first7 b15).length = 7 := rfl
  have hm12 : ((q + 1#64) ↦ₛ last7 b12) ⊢ memRegion (q + 1#64) 7 := by
    rw [← hl7]; exact pointsToBytes_entails_memRegion _ _
  have hm15 : ((q + 24#64) ↦ₛ first7 b15) ⊢ memRegion (q + 24#64) 7 := by
    rw [← hf7]; exact pointsToBytes_entails_memRegion _ _
  have hm31 : ((q + 31#64) ↦₈ b7) ⊢ memRegion (q + 31#64) 1 := by
    rw [ProofLib.memRegion_one]; exact Entails.sepExists_intro b7
  refine Entails.trans (sepConj_mono hm12 (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono hm15 hm31)))) ?_
  rw [← ProofLib.memRegion_split' (b := q + 24#64) (n := 7) (k := 1) (b' :=
    q + 31#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := q + 16#64) (n := 8) (k := 8) (b' :=
      q + 24#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := q + 8#64) (n := 8) (k := 16) (b' :=
      q + 16#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := q + 1#64) (n := 7) (k := 24) (b' :=
      q + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := q + 1#64) (n := 1) (k := 30) (b' :=
      q + 2#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  exact Entails.refl _
theorem unpack64_encodeBitLen128BE {L : Nat} (hL : L = 97 ∨ L = 1633) (r : BitVec 64) :
    ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ rev64 (BitVec.ofNat 64 (8 * L)))) =
      (r ↦ₛ bytesToBv8 (encodeBitLen128BE L)) := by
  have heq : unpack64 0#64 ++ unpack64 (rev64 (BitVec.ofNat 64 (8 * L))) =
      bytesToBv8 (encodeBitLen128BE L) := by
    rcases hL with rfl | rfl <;> decide
  rw [← heq, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes]
theorem exists_pad97_cells {tail97 : Bytes} (ht : tail97.length = 97) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 p12 p13 : BitVec 64, (∀ p : BitVec 64,
        (p ↦ₛ bytesToBv8 tail97) =
          ((p ↦₆₄ b0) ∗ ((p + 8#64) ↦₆₄ b1) ∗ ((p + 16#64) ↦₆₄ b2) ∗ ((p + 24#64) ↦₆₄ b3) ∗
           ((p + 32#64) ↦₆₄ b4) ∗ ((p + 40#64) ↦₆₄ b5) ∗ ((p + 48#64) ↦₆₄ b6) ∗ ((p +
           56#64) ↦₆₄ b7) ∗
           ((p + 64#64) ↦₆₄ b8) ∗ ((p + 72#64) ↦₆₄ b9) ∗ ((p + 80#64) ↦₆₄ b10) ∗ ((p +
           88#64) ↦₆₄ b11) ∗ ((p + 96#64) ↦₈ (bytesToBv8 tail97).getD 96 0#8))) ∧ (∀ q : BitVec 64,
        (q ↦₈ (bytesToBv8 tail97).getD 96 0#8) ∗ ((q + 1#64) ↦₈ 128#8) ∗
          ((q + 2#64) ↦ₛ List.replicate 30 0#8) =
          ((q ↦₆₄ p12) ∗ ((q + 8#64) ↦₆₄ p13) ∗ ((q + 16#64) ↦₆₄ 0#64) ∗ ((q + 24#64) ↦₆₄ 0#64))) ∧
      (∀ (r : BitVec 64) {L : Nat}, (L = 97 ∨ L = 1633) →
        ((r ↦₆₄ b0) ∗ ((r + 8#64) ↦₆₄ b1) ∗ ((r + 16#64) ↦₆₄ b2) ∗ ((r + 24#64) ↦₆₄ b3) ∗
         ((r + 32#64) ↦₆₄ b4) ∗ ((r + 40#64) ↦₆₄ b5) ∗ ((r + 48#64) ↦₆₄ b6) ∗ ((r + 56#64) ↦₆₄ b7) ∗
         ((r + 64#64) ↦₆₄ b8) ∗ ((r + 72#64) ↦₆₄ b9) ∗ ((r + 80#64) ↦₆₄ b10) ∗ ((r +
         88#64) ↦₆₄ b11) ∗ ((r + 96#64) ↦₆₄ p12) ∗ ((r + 104#64) ↦₆₄ p13) ∗
         ((r + 112#64) ↦₆₄ 0#64) ∗ ((r + 120#64) ↦₆₄ rev64 (BitVec.ofNat 64 (8 * L)))) =
          (r ↦ₛ bytesToBv8 (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L))) := by
  have h64 : (bytesToBv8 (tail97.take 64)).length = 64 := by simp [bytesToBv8, ht]
  have h32 : (bytesToBv8 ((tail97.drop 64).take 32)).length = 32 := by simp [bytesToBv8, ht]
  have h16 : (bytesToBv8 ([tail97.getD 96 0, 0x80] ++ List.replicate 14 0)).length = 16 := by
    simp [bytesToBv8]
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb07⟩ := exists_unpack64_of_length_64 h64
  obtain ⟨b8, b9, b10, b11, _, hb811⟩ := exists_unpack64_of_length_32 h32
  obtain ⟨p12, p13, _, hp1213⟩ := exists_unpack64_of_length_16 h16
  have ht96_drop : tail97.drop 96 = [tail97.getD 96 0] := by
    rcases hp : tail97.drop 96 with _ | ⟨x, _ | ⟨y, _⟩⟩
    · have := congrArg List.length hp; simp [ht] at this
    · have hget : (tail97.drop 96).getD 0 0 = tail97.getD 96 0 := by
        simp [List.getD_eq_getElem?_getD]
      rw [hp] at hget; simp at hget; rw [hget]; rfl
    · have := congrArg List.length hp; simp [ht] at this
  have hsp97 : tail97 = tail97.take 64 ++ ((tail97.drop 64).take 32 ++ [tail97.getD 96 0]) := by
    rw [← ht96_drop, show (96 : Nat) = 64 + 32 from rfl, ← List.drop_drop,
      List.take_append_drop, List.take_append_drop]
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, p12, p13, fun p => ?_, fun q =>
    ?_, fun r L hL => ?_⟩
  · conv => lhs; arg 2; arg 1; rw [hsp97]
    simp only [bytesToBv8_append, pointsToBytes_append, h64, h32, hb07, hb811,
      bytesToBv8_getD_eq, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    simp only [bytesToBv8, List.map_cons, List.map_nil, pointsToBytes_cons, pointsToBytes_nil,
      sepConj_emp]
  · have hrep30 : List.replicate 30 (0#8 : BitVec 8) = List.replicate 14 0#8 ++ (unpack64 0#64 ++
      unpack64 0#64) := by decide
    have hp1213_q : (q ↦₈ (bytesToBv8 tail97).getD 96 0#8) ∗ ((q + 1#64) ↦₈ 128#8) ∗
        ((q + 2#64) ↦ₛ List.replicate 14 0#8) = ((q ↦₆₄ p12) ∗ ((q + 8#64) ↦₆₄ p13)) := by
      rw [← hp1213 q, bytesToBv8_getD_eq]
      have hmap14 : bytesToBv8 (List.replicate 14 0) = List.replicate 14 0#8 := by decide
      simp only [bytesToBv8_append, hmap14]
      simp only [bytesToBv8, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        pointsToBytes_cons, BitVec.add_assoc, BitVec.reduceAdd]; rfl
    rw [hrep30, pointsToBytes_append, show (List.replicate 14 (0#8 : BitVec 8)).length = 14 from
      rfl, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes, ←
        pointsTo64_eq_pointsToBytes]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    rw [sepConj_assoc (q ↦₈ _), hp1213_q]
  · symm
    have hsp_pad : tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L =
        tail97.take 64 ++ ((tail97.drop 64).take 32 ++
          (([tail97.getD 96 0, 0x80] ++ List.replicate 14 0) ++ encodeBitLen128BE L)) := by
      conv => lhs; arg 1; arg 1; arg 1; rw [hsp97]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hsp_pad, bytesToBv8_append, bytesToBv8_append, bytesToBv8_append,
      pointsToBytes_append, h64, pointsToBytes_append, h32, pointsToBytes_append, h16,
      hb07, hb811, hp1213, ← unpack64_encodeBitLen128BE hL]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem cells_16_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗
      ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗ ((a + 96#64) ↦₆₄ v12) ∗
      ((a + 104#64) ↦₆₄ v13) ∗ ((a + 112#64) ↦₆₄ v14) ∗ ((a + 120#64) ↦₆₄ v15) ⊢ cells a 16 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <|
    Entails.sepExists_right v12 <| Entails.sepExists_right v13 <|
    Entails.sepExists_right v14 <| Entails.sepExists_right v15 <| Entails.refl _
theorem first7_pack (a v : BitVec 64) (b7 : BitVec 8) :
    ((a ↦ₛ first7 v) ∗ ((a + 7#64) ↦₈ b7)) ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) := by
  have hf7 : (first7 v).length = 7 := rfl
  have hm : (a ↦ₛ first7 v) ⊢ memRegion a 7 := by
    rw [← hf7]; exact pointsToBytes_entails_memRegion a (first7 v)
  refine Entails.trans (sepConj_mono_left hm) (Entails.trans (cell_pack7 a b7) ?_)
  exact Entails.sepExists_elim fun w => Entails.pure_left fun _ => Entails.sepExists_intro w
theorem fitBv8_64_sha512CompressOutBytes (P : Primitives) (st blk : Bytes) :
    fitBv8 64 (sha512CompressOutBytes P st blk) = bytesToBv8 (sha512CompressOutBytes P st blk) := by
  have hlen : (bytesToBv8 (sha512CompressOutBytes P st blk)).length = 64 := by
    simp [bytesToBv8, sha512CompressOutBytes_length]
  simp [fitBv8, hlen, List.take_of_length_le (Nat.le_of_eq hlen)]
theorem fitBv8_of_length_eq {n : Nat} {bs : Bytes} (h : bs.length = n) :
    fitBv8 n bs = bytesToBv8 bs := by
  have hlen : (bytesToBv8 bs).length = n := by simp [bytesToBv8, h]
  simp [fitBv8, hlen, List.take_of_length_le (Nat.le_of_eq hlen)]
theorem sClamped_buf_pre (a v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ memRegion (a + 16#64) 15 ∗
      (∃∗ b31 : BitVec 8, (a + 31#64) ↦₈ b31) := by
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo64_entails_memRegion _ _)) ?_
  rw [← ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' :=
    a + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 16#64) (n := 15) (k := 1) (b' :=
      a + 31#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  exact Entails.refl _
theorem stackAt_hook_split_48 (sp : BitVec 64) : stackAt sp pqxdhHookStack =
      memRegion (sp - 4096#64) 4048 ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, pqxdhHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4096) (n := 4048) (k := 48)
      (b' := sp - 48#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 48#64) 6 (by decide) : memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]
theorem pointsToBytes_32_merge_128 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) ∗ memRegion (a + 32#64) 128 ⊢ memRegion a 160 := by
  have hm : (a ↦ₛ bs) ⊢ memRegion a 32 := by rw [← h]; exact pointsToBytes_entails_memRegion a bs
  refine Entails.trans (sepConj_mono_left hm) ?_
  rw [← ProofLib.memRegion_split' (b := a) (n := 32) (k := 128) (b' :=
    a + 32#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _
theorem sig_split_32 (p : BitVec 64) {sig : Bytes} (hsig : sig.length = 64) :
    (p ↦ₛ bytesToBv8 sig) =
      ((p ↦ₛ bytesToBv8 (sig.take 32)) ∗ ((p + 32#64) ↦ₛ bytesToBv8 (sig.drop 32))) := by
  conv => lhs; arg 2; arg 1; rw [← List.take_append_drop 32 sig]
  have ht32 : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  rw [bytesToBv8_append, pointsToBytes_append, ht32]
@[local simp, local wp_norm, local arm64_norm]
theorem and64_mask255_ite_1_0 (p : Prop) [Decidable p] :
    ((if p then 1#64 else 0#64) &&& 4294967551#64) = if p then 1#64 else 0#64 := by
  by_cases hp : p <;> simp [hp]
@[local simp, local wp_norm, local arm64_norm]
theorem csinc_eq_zero32_ite_1_0 (p : Prop) [Decidable p] :
    (if (BitVec.setWidth 32 (if p then 1#64 else 0#64) == 0#32) = true then 0#64 else 1#64) =
      if p then 1#64 else 0#64 := by
  by_cases hp : p <;> simp [hp]
theorem truncate8_zeroExtend32_and7f (b : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 32 b &&& 0x7f#32) = b &&& 0x7f#8 := by revert b; decide
theorem pointsToBytes_entails_memRegion_n (a : BitVec 64) (bs : List (BitVec 8)) {n : Nat}
    (h : bs.length = n) : (a ↦ₛ bs) ⊢ memRegion a n := by
  subst h; exact pointsToBytes_entails_memRegion a bs
theorem x0_cteq_simplify (xs ys : Bytes) : (if (BitVec.truncate 32 ((if bytesToBv8 xs =
      bytesToBv8 ys then 1#64 else 0#64) &&& 1095216660735#64) == 0#32) = true
     then 0#64 else 1#64) = (if (xs == ys) = true then 1#64 else 0#64) := by
  by_cases h : xs = ys
  · subst h; simp
  · have hne : ¬ (bytesToBv8 xs = bytesToBv8 ys) := fun heq => h (bytesToBv8_inj heq)
    have hbeq : ¬ ((xs == ys) = true) := by rw [beq_iff_eq]; exact h
    simp only [hne, hbeq, ↓reduceIte]; decide

section WithProgramTrap
variable {C : Crypto}
local notation "PP" b:arg absHooks:arg => trTrapProgAt b C absHooks

end WithProgramTrap

section WithProgram
variable {C : Crypto} {ctl : BitVec 64}
end WithProgram

/-! ## Contract-Backed Generalization on `tripleRatchetProgAtExt` -/

section WithProgramExt
@[expose] def pqxdhCtEqSliceSpecExt :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6 ∗ stackAt (sp - 48#64) pqxdhHookStackExt
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = (if k1 = k2 then 1#8 else 0#8) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6 ∗ stackAt (sp - 48#64) pqxdhHookStackExt

theorem stackAt_verifySigHook_split_48_ext (sp : BitVec 64) :
    stackAt sp verifySigHookStackExt =
      cells (sp - 48#64) 6 ∗ stackAt (sp - 48#64) pqxdhHookStackExt := by
  simpa only [sepConj_comm] using
    ProofLib.stackAt_split_cells sp pqxdhHookStackExt 6 (by decide)

private theorem truncate32_and_mask_eq_zext32_setWidth8_ext (v : BitVec 64) :
    BitVec.truncate 32 (v &&& 1095216660735#64) = BitVec.zeroExtend 32 (v.setWidth 8) := by
  bv_bits

theorem x0_cteq_simplify_ext {v : BitVec 64} (xs ys : Bytes)
    (hv : v.setWidth 8 = (if bytesToBv8 xs = bytesToBv8 ys then 1#8 else 0#8)) :
    (if (BitVec.truncate 32 (v &&& 1095216660735#64) == 0#32) = true
     then 0#64 else 1#64) = (if (xs == ys) = true then 1#64 else 0#64) := by
  rw [truncate32_and_mask_eq_zext32_setWidth8_ext, hv]
  by_cases h : xs = ys
  · subst h; simp
  · have hne : ¬ (bytesToBv8 xs = bytesToBv8 ys) := fun heq => h (bytesToBv8_inj heq)
    have hbeq : ¬ ((xs == ys) = true) := by rw [beq_iff_eq]; exact h
    simp only [hne, hbeq, ↓reduceIte]; decide

private theorem hookSat_sessionMemcpy_ext {absHooks : String → Option (State → State)}
    (h : HookSat absHooks memcpyName SignalSession.CliExt.memcpySpec) :
    HookSat absHooks memcpyName (sessionMemcpySpec pqxdhHookStackExt) := by
  obtain ⟨fn, hfn, hok⟩ := h
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases x with ⟨dst, src, bs⟩
  have hsplit : stackAt s0.sp pqxdhHookStackExt =
      stackAt s0.sp SignalSession.CliExt.memHookStack ∗ memRegion (s0.sp - 16384#64) 12288 :=
    (ProofLib.stackAt_split_bottom s0.sp 4096 12288 (by decide)).trans (sepConj_comm _ _)
  dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpre
  rw [hsplit] at hpre
  have hpre0 : s0.mem ⊨ SignalSession.CliExt.memcpySpec.pre (dst, src, bs) s0 ∗
      (memRegion (s0.sp - 16384#64) 12288 ∗ R) := by
    dsimp only [SignalSession.CliExt.memcpySpec, libcMemcpySpec]
    convert hpre using 1; ac_rfl
  rcases hok (dst, src, bs) (memRegion (s0.sp - 16384#64) 12288 ∗ R) s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.memcpySpec] at hpost
    dsimp only [sessionMemcpySpec]
    rw [hsplit]
    convert hpost using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem hookSat_sessionMemset_ext {absHooks : String → Option (State → State)}
    (h : HookSat absHooks memsetName SignalSession.CliExt.memsetSpec) :
    HookSat absHooks memsetName (sessionMemsetSpec pqxdhHookStackExt) := by
  obtain ⟨fn, hfn, hok⟩ := h
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases x with ⟨ptr, c, len⟩
  have hsplit : stackAt s0.sp pqxdhHookStackExt =
      stackAt s0.sp SignalSession.CliExt.memHookStack ∗ memRegion (s0.sp - 16384#64) 12288 :=
    (ProofLib.stackAt_split_bottom s0.sp 4096 12288 (by decide)).trans (sepConj_comm _ _)
  dsimp only [sessionMemsetSpec, libcMemsetSpec] at hpre
  rw [hsplit] at hpre
  have hpre0 : s0.mem ⊨ SignalSession.CliExt.memsetSpec.pre (ptr, c, len) s0 ∗
      (memRegion (s0.sp - 16384#64) 12288 ∗ R) := by
    dsimp only [SignalSession.CliExt.memsetSpec, libcMemsetSpec]
    convert hpre using 1; ac_rfl
  rcases hok (ptr, c, len) (memRegion (s0.sp - 16384#64) 12288 ∗ R) s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.memsetSpec] at hpost
    dsimp only [sessionMemsetSpec]
    rw [hsplit]
    convert hpost using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private def blackBoxU8SpecExt : Spec (BitVec 64) where
  pre := fun v s => ⌜s.readReg64 .x0 = v⌝ ∗ stackAt s.sp pqxdhHookStackExt
  post := fun v s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = v.setWidth 8 ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp pqxdhHookStackExt

private theorem setWidth8_of_setWidth32_zext8_ext {a b : BitVec 64}
    (h : a.setWidth 32 = (b.setWidth 8).zeroExtend 32) :
    a.setWidth 8 = b.setWidth 8 := by
  have h8 := congrArg (BitVec.setWidth 8) h
  revert h8; bv_bits

private theorem hookSat_blackBoxU8_ext {absHooks : String → Option (State → State)}
    (h : HookSat absHooks "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec) :
    HookSat absHooks "subtle::black_box::<u8>" blackBoxU8SpecExt := by
  obtain ⟨fn, hfn, hok⟩ := h
  refine ⟨fn, hfn, fun v R s0 hrun hpre hsp => ?_⟩
  dsimp only [blackBoxU8SpecExt, pqxdhHookStackExt] at hpre
  have hpre0 : s0.mem ⊨ SignalSession.CliExt.blackBoxSpec.pre v s0 ∗ R := by
    simpa only [SignalSession.CliExt.blackBoxSpec, SignalSession.CliExt.withStack] using hpre
  rcases hok v R s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.blackBoxSpec, SignalSession.CliExt.withStack] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨h32, htr⟩, hmem⟩
    dsimp only [blackBoxU8SpecExt, pqxdhHookStackExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨setWidth8_of_setWidth32_zext8_ext h32, htr⟩, hmem⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_ext (a b : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 b) = (a != b) :=
  FindReceiverChainIndex.byte_bne_zext32 a b

@[local simp, local wp_norm, local arm64_norm]
private theorem ite_bne_byte_0_1_ext (a b : BitVec 8) :
    (if (a != b) = true then 0#64 else 1#64) = if (a == b) = true then 1#64 else 0#64 :=
  FindReceiverChainIndex.ite_bne_byte_0_1 a b

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0_ext (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_prop_1_0_ext (P : Prop) [Decidable P] :
    BitVec.setWidth 8 (if P then 1#64 else 0#64) = if P then 1#8 else 0#8 := by
  split <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0_32_ext (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#32 else 0#32) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_zext64_32_ext (x : BitVec 32) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 x) = BitVec.setWidth 8 x := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_setWidth32_ext (x : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 x := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_and64_ext (x y : BitVec 64) :
    BitVec.setWidth 8 (x &&& y) = BitVec.setWidth 8 x &&& BitVec.setWidth 8 y :=
  BitVec.setWidth_and

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_and32_ext (x y : BitVec 32) :
    BitVec.setWidth 8 (x &&& y) = BitVec.setWidth 8 x &&& BitVec.setWidth 8 y :=
  BitVec.setWidth_and

@[local simp, local wp_norm, local arm64_norm]
private theorem ite_one_zero_and_8_ext (b1 b2 : Bool) :
    ((if b1 = true then 1#8 else 0#8) &&& (if b2 = true then 1#8 else 0#8)) =
      if (b1 && b2) = true then 1#8 else 0#8 := by
  cases b1 <;> cases b2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_and_4294967297_ext (x : BitVec 64) :
    BitVec.setWidth 32 (x &&& 4294967297#64) =
      BitVec.zeroExtend 32 (BitVec.setWidth 8 x &&& 1#8) := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem ite_one_zero_and_one_8_ext (b : Bool) :
    ((if b = true then 1#8 else 0#8) &&& 1#8) =
      if b = true then 1#8 else 0#8 := by
  cases b <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem zeroExtend32_ite_one_zero_8_ext (b : Bool) :
    BitVec.zeroExtend 32 (if b = true then 1#8 else 0#8) =
      if b = true then 1#32 else 0#32 := by
  cases b <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_32_ext (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

attribute [local simp, local wp_norm, local arm64_norm] Bool.and_assoc

private theorem ct_eq_bool_32_u8_ext {k1 k2 : List (BitVec 8)} (h1 : k1.length = 32) (h2 : k2.length = 32) :
    (if (k1.getD 0 0#8 == k2.getD 0 0#8 &&
        (k1.getD 1 0#8 == k2.getD 1 0#8 &&
        (k1.getD 2 0#8 == k2.getD 2 0#8 &&
        (k1.getD 3 0#8 == k2.getD 3 0#8 &&
        (k1.getD 4 0#8 == k2.getD 4 0#8 &&
        (k1.getD 5 0#8 == k2.getD 5 0#8 &&
        (k1.getD 6 0#8 == k2.getD 6 0#8 &&
        (k1.getD 7 0#8 == k2.getD 7 0#8 &&
        (k1.getD 8 0#8 == k2.getD 8 0#8 &&
        (k1.getD 9 0#8 == k2.getD 9 0#8 &&
        (k1.getD 10 0#8 == k2.getD 10 0#8 &&
        (k1.getD 11 0#8 == k2.getD 11 0#8 &&
        (k1.getD 12 0#8 == k2.getD 12 0#8 &&
        (k1.getD 13 0#8 == k2.getD 13 0#8 &&
        (k1.getD 14 0#8 == k2.getD 14 0#8 &&
        (k1.getD 15 0#8 == k2.getD 15 0#8 &&
        (k1.getD 16 0#8 == k2.getD 16 0#8 &&
        (k1.getD 17 0#8 == k2.getD 17 0#8 &&
        (k1.getD 18 0#8 == k2.getD 18 0#8 &&
        (k1.getD 19 0#8 == k2.getD 19 0#8 &&
        (k1.getD 20 0#8 == k2.getD 20 0#8 &&
        (k1.getD 21 0#8 == k2.getD 21 0#8 &&
        (k1.getD 22 0#8 == k2.getD 22 0#8 &&
        (k1.getD 23 0#8 == k2.getD 23 0#8 &&
        (k1.getD 24 0#8 == k2.getD 24 0#8 &&
        (k1.getD 25 0#8 == k2.getD 25 0#8 &&
        (k1.getD 26 0#8 == k2.getD 26 0#8 &&
        (k1.getD 27 0#8 == k2.getD 27 0#8 &&
        (k1.getD 28 0#8 == k2.getD 28 0#8 &&
        (k1.getD 29 0#8 == k2.getD 29 0#8 &&
        (k1.getD 30 0#8 == k2.getD 30 0#8 &&
        (k1.getD 31 0#8 == k2.getD 31 0#8)))))))))))))))))))))))))))))))) = true then 1#8 else 0#8) =
      (if k1 = k2 then 1#8 else 0#8) := by
  have h64 := FindReceiverChainIndex.ct_eq_bool_32 h1 h2
  have h8 := congrArg (BitVec.setWidth 8) h64
  simpa only [setWidth8_ite_1_0_ext, setWidth8_ite_prop_1_0_ext] using h8

private theorem ctEqCells_entails_ext (sp : BitVec 64) (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
     ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) ⊢
      cells (sp - 48#64) 6 := by
  refine cells_sub_succ_entails 48 6 ?_
  refine cells_sub_succ_entails 40 5 ?_
  refine cells_sub_succ_entails 32 4 ?_
  refine cells_sub_succ_entails 24 3 ?_
  refine cells_sub_succ_entails 16 2 ?_
  have h1 : (((sp - 8#64) ↦₆₄ v5) ∗ emp) ⊢ cells (sp - BitVec.ofNat 64 8) 1 :=
    cells_sub_succ_entails 8 1 (Entails.refl _)
  rwa [sepConj_emp] at h1

theorem ctEqCells_sepConj_stackAt_ext (sp : BitVec 64) :
    cells (sp - 48#64) 6 ∗ stackAt (sp - 48#64) pqxdhHookStackExt =
      stackAt sp pqxdhHookStackExt ∗ memRegion (sp - 16432#64) 48 := by
  rw [← stackAt_verifySigHook_split_48_ext sp]
  exact (ProofLib.stackAt_split_bottom sp 16384 48 (by decide)).trans (sepConj_comm _ _)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
private theorem step_blackBox_ext
    {prog : Program} {target_pc entry_bb ret_pc : BitVec 64}
    {s0 s : State} {sp_cur x19_v x20_v : BitVec 64}
    {x0_v x19_8_v x21_8_v x22_8_v : BitVec 8}
    {R_rest : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok prog entry_bb blackBoxU8SpecExt)
    (hal_cur : (sp_cur &&& 15#64 == 0#64) = true)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hlr : s.readReg64 (Reg.gpr 30#5) = ret_pc)
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x19_v)
    (hx19_8 : (s.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x20_v)
    (hx21_8 : (s.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v)
    (hx22_8 : (s.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = sp_cur)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = sp_cur →
      (sf.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v →
      sf.readReg64 (Reg.gpr 19#5) = x19_v →
      (sf.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v →
      sf.readReg64 (Reg.gpr 20#5) = x20_v →
      (sf.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v →
      (sf.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v →
      sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) →
      sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) →
      sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) →
      sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) →
      sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) →
      sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
      sf.readReg64 (Reg.gpr 29#5) = sp_cur →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.trace = s0.trace →
      SepWP prog target_pc sf (stackAt sp_cur pqxdhHookStackExt ∗ R_rest) post) :
    SepWP prog target_pc s (stackAt sp_cur pqxdhHookStackExt ∗ R_rest) post := by
  have hal : s.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  refine SepWP.call_subroutine_frame hbb (x := s.readReg64 .x0) (F := R_rest)
    hpc hrun hal hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hret_pc hret_run hsp_sf0 hcs => ?_)
  · intro R hm
    rw [sepConj_assoc] at hm
    simp only [blackBoxU8SpecExt, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, hm⟩
  · dsimp only [blackBoxU8SpecExt]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hx0_sf, htr_sf⟩ => ?_
    have hsp_sf : sf.sp = sp_cur := hsp_sf0.trans hsp
    have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = x19_v := hcs.1.trans hx19
    have hx19_8_sf : (sf.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v := by
      change (sf.readReg64 .x19).setWidth 8 = x19_8_v
      rw [hcs.1]; exact hx19_8
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = x20_v := hcs.2.1.trans hx20
    have hx21_8_sf : (sf.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v := by
      change (sf.readReg64 .x21).setWidth 8 = x21_8_v
      rw [hcs.2.2.1]; exact hx21_8
    have hx22_8_sf : (sf.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v := by
      change (sf.readReg64 .x22).setWidth 8 = x22_8_v
      rw [hcs.2.2.2.1]; exact hx22_8
    have hx23_sf : sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) := hcs.2.2.2.2.1.trans hx23
    have hx24_sf : sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) := hcs.2.2.2.2.2.1.trans hx24
    have hx25_sf : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := hcs.2.2.2.2.2.2.1.trans hx25
    have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := hcs.2.2.2.2.2.2.2.1.trans hx26
    have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := hcs.2.2.2.2.2.2.2.2.1.trans hx27
    have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := hcs.2.2.2.2.2.2.2.2.2.1.trans hx28
    have hx29_sf : sf.readReg64 (Reg.gpr 29#5) = sp_cur := hcs.2.2.2.2.2.2.2.2.2.2.1.trans hx29
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := hcs.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
    exact hnext sf hret_pc hret_run hsp_sf
      (hx0_sf.trans hx0) hx19_sf hx19_8_sf hx20_sf hx21_8_sf hx22_8_sf
      hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf hvregs_sf
      (htr_sf.trans htr)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
private theorem step_blackBox_tail_ext
    {prog : Program} {entry_bb : BitVec 64}
    {s0 s : State} {x0_v x0_target : BitVec 8}
    {v0 v1 v2 v3 v4 v5 : BitVec 64}
    {R_slices S1 S2 R0 : SepProp}
    (hbb : subroutine_ok prog entry_bb blackBoxU8SpecExt)
    (hal_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hlr : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5))
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5))
    (hx20 : s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5))
    (hx21 : s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5))
    (hx22 : s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hx0_eq : x0_v = x0_target)
    (h_slices : R_slices = S1 ∗ S2) :
    SepWP prog (s0.readReg64 .lr) s
      (stackAt (s0.sp - 48#64) pqxdhHookStackExt ∗
        ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
        ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5) ∗
        R_slices)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R0 →
          sf.mem ⊨
            (⌜(sf.readReg64 .x0).setWidth 8 = x0_target ∧ sf.trace = s0.trace⌝ ∗
              S1 ∗ S2 ∗
              cells (s0.sp - 48#64) 6 ∗
              stackAt (s0.sp - 48#64) pqxdhHookStackExt) ∗ R0) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hal : s.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  refine SepWP.call_subroutine_frame hbb (x := s.readReg64 .x0)
    (F := memRegion (s0.sp - 16432#64) 48 ∗ R_slices)
    hpc hrun hal hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hret_pc hret_run hsp_sf0 hcs => ?_)
  · intro R hm
    have hm1 : s.mem ⊨
        (cells (s0.sp - 48#64) 6 ∗
          stackAt (s0.sp - 48#64) pqxdhHookStackExt) ∗ (R_slices ∗ R) := by
      have hrearr :
          (stackAt (s0.sp - 48#64) pqxdhHookStackExt ∗
            ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
            ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5) ∗
            R_slices) ∗ R =
          (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
            ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
          (stackAt (s0.sp - 48#64) pqxdhHookStackExt ∗ (R_slices ∗ R)) := by ac_rfl
      rw [hrearr] at hm
      have hm' := Satisfies.mono (sepConj_mono_left (ctEqCells_entails_ext s0.sp v0 v1 v2 v3 v4 v5)) hm
      rwa [← sepConj_assoc] at hm'
    rw [ctEqCells_sepConj_stackAt_ext s0.sp, sepConj_assoc] at hm1
    simp only [blackBoxU8SpecExt, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, by simpa only [sepConj_assoc] using hm1⟩
  · dsimp only [blackBoxU8SpecExt]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hx0_sf, htr_sf⟩ => ?_
    have hrearr_post :
        stackAt s0.sp pqxdhHookStackExt ∗ (memRegion (s0.sp - 16432#64) 48 ∗ R_slices) =
        S1 ∗ S2 ∗ cells (s0.sp - 48#64) 6 ∗ stackAt (s0.sp - 48#64) pqxdhHookStackExt := by
      rw [← sepConj_assoc, ← ctEqCells_sepConj_stackAt_ext s0.sp, h_slices]
      ac_rfl
    rw [hrearr_post]
    apply SepWP.done hret_pc hret_run
    refine ⟨?_, hsp_sf0.trans hsp,
      ⟨hcs.1.trans hx19, hcs.2.1.trans hx20, hcs.2.2.1.trans hx21, hcs.2.2.2.1.trans hx22,
       hcs.2.2.2.2.1.trans hx23, hcs.2.2.2.2.2.1.trans hx24, hcs.2.2.2.2.2.2.1.trans hx25,
       hcs.2.2.2.2.2.2.2.1.trans hx26, hcs.2.2.2.2.2.2.2.2.1.trans hx27,
       hcs.2.2.2.2.2.2.2.2.2.1.trans hx28, hcs.2.2.2.2.2.2.2.2.2.2.1.trans hx29,
       hcs.2.2.2.2.2.2.2.2.2.2.2.trans hvregs⟩⟩
    intro hm_R0
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm_R0 ⊢
    exact ⟨⟨(hx0_sf.trans hx0).trans hx0_eq, htr_sf.trans htr⟩, hm_R0⟩

private theorem ctEq_pre_rearrange_ext (S1 S2 C0 C1 C2 C3 C4 C5 Stk : SepProp) :
    S1 ∗ S2 ∗ C0 ∗ C1 ∗ C2 ∗ C3 ∗ C4 ∗ C5 ∗ Stk =
      Stk ∗ C0 ∗ C1 ∗ C2 ∗ C3 ∗ C4 ∗ C5 ∗ (S1 ∗ S2) := by
  ac_rfl

private theorem sp_sub48_aligned_ext {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_bits

set_option hygiene false in
local macro "wp_black_box_ext " hbb:ident hal:ident : tactic =>
  `(tactic| (
    refine step_blackBox_ext $hbb $hal
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ?_
    try clear hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb s_bb
    intro s_bb hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb
  ))

end WithProgramExt
end CryptoVerification.E2E.Pqxdh.Shared
