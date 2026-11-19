/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Common.Spec.Curve25519 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import ProofLib.Hoare.LibcHooks
import ProofLib.Process.FsLemmas
import LibsignalBinary.Proofs.E2E.HooksE.Common
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.VariableBaseMul

/-!
# Pure `5×51`-Bit Point Packing, Ghost Hook Specs, and Pure Fallback Soundness

Placement-free pure fallback functions (`dalek*Fallback`), `dalekPrimsReal`, stack-parametric
ghost-hook specifications (`dalek*Spec`), and `HookOk` / `PureFallbackPreserved` / `HookFsTraced`
proofs for the 6 `dalekCliMultiLib` Curve25519/Edwards25519 symbols. Factored below
`ExtraGhostSpecs` so `CryptoDalekRowSpecs` and `Phase4GhostHooks` share these definitions
without import cycles.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open ProofLib SepProp
open VerifiedLibraries.Common (EdPoint EdExtPoint p25519 edOrderL edZero edSmul edExtZero
  edExtOfAffine edExtToAffine encodeEd fpMul)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.E2E (readVecN)
open CryptoVerification.E2E.HooksE.HooksOkAux (keepsFrozen_write64_of_pointsTo64 satisfies_write64_of_pointsTo64)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (withStack pureByteFunctionSpec inputAfter)
open LibsignalBinary.Heap (FdsHiFrame VmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
  (scalarModHook scalarWideHook toEdwardsHook compressHook torsionFreeHook dsmbHook)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase
  (basepointOrderBytes fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (packFe51Bytes
  fe51ValOfBytes_packFe51Bytes fe51LimbsBounded_packFe51Bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (fe51LimbsBounded)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (montToEdwards
  fe51LimbsBoundedAt fe51Point4Bounded fe51ValAt edExtOfBytes edPointEq edVarBaseMul
  edProjectiveToExtended edDoubleScalarMulBasepoint readLE_slice_eq)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
  (basepointOrderBytes_length basepointOrderBytes_val basepointOrderBytes_getD31)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges
  (specSimulates_keepsFs dalekScalarModVec dalekScalarWideVec dalekEdNegVec fe51Point4Bounded_mono)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge
  (DalekPrims montLiftEd montLiftEd_eq_montToEdwards sign_and_one_eq_iff natToLeBytes_len)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Field (p25519_gt_one fpPow_lt)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards
  (EdExtValid edExtValid_edExtZero edExtToAffine_edExtZero)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1 (edPointEq_eq_beq_toAffine)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.VariableBaseMul (edVarBaseMul_spec)

/-! ## 1. Canonical `5×51`-Bit Point Packing (`fe51OfNat51`, `edExtToBytes51`) & Pure Fallbacks -/

@[expose] def fe51OfNat51 (n : Nat) : List (BitVec 8) :=
  let v := n % p25519
  packFe51Bytes (BitVec.ofNat 64 (v % (2 ^ 51))) (BitVec.ofNat 64 ((v / (2 ^ 51)) % (2 ^ 51)))
    (BitVec.ofNat 64 ((v / (2 ^ 102)) % (2 ^ 51))) (BitVec.ofNat 64 ((v / (2 ^ 153)) % (2 ^ 51)))
    (BitVec.ofNat 64 ((v / (2 ^ 204)) % (2 ^ 51)))

@[simp] theorem fe51OfNat51_length (n : Nat) : (fe51OfNat51 n).length = 40 := rfl

private theorem p25519_lt_two_pow_255 : p25519 < 2 ^ 255 := by unfold p25519; decide
private theorem p25519_pos : 0 < p25519 := by unfold p25519; decide

private theorem bv64_ofNat_mod_2_51_toNat (x : Nat) :
    (BitVec.ofNat 64 (x % (2 ^ 51))).toNat = x % (2 ^ 51) := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt x (by decide)) (by decide))

theorem fe51OfNat51_bounded51 (n : Nat) : fe51LimbsBounded (fe51OfNat51 n) (2 ^ 51) := by
  unfold fe51OfNat51; apply fe51LimbsBounded_packFe51Bytes <;>
    (rw [bv64_ofNat_mod_2_51_toNat]; exact Nat.mod_lt _ (by decide))

theorem fe51OfNat51_bounded (n : Nat) : fe51LimbsBounded (fe51OfNat51 n) (2 ^ 52) := by
  unfold fe51OfNat51; apply fe51LimbsBounded_packFe51Bytes <;>
    (rw [bv64_ofNat_mod_2_51_toNat]; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

@[simp] theorem fe51ValOfBytes_fe51OfNat51 (n : Nat) : fe51ValOfBytes (fe51OfNat51 n) = n % p25519 := by
  unfold fe51OfNat51; dsimp only; rw [fe51ValOfBytes_packFe51Bytes]; unfold fe51Val
  simp only [bv64_ofNat_mod_2_51_toNat]
  have := Nat.lt_trans (Nat.mod_lt n p25519_pos) p25519_lt_two_pow_255; omega

@[expose] def edExtToBytes51 (P : EdExtPoint) : List (BitVec 8) :=
  fe51OfNat51 P.X ++ fe51OfNat51 P.Y ++ fe51OfNat51 P.Z ++ fe51OfNat51 P.T

@[simp] theorem edExtToBytes51_length (P : EdExtPoint) : (edExtToBytes51 P).length = 160 := by
  simp [edExtToBytes51, fe51OfNat51_length]

private theorem slice_append4_0 {a b c d : List (BitVec 8)} (ha : a.length = 40) :
    ProofLib.ByteSlice.slice (a ++ b ++ c ++ d) 0 40 = a := by
  unfold ProofLib.ByteSlice.slice; simp only [List.append_assoc, List.drop_zero]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

private theorem slice_append4_40 {a b c d : List (BitVec 8)} (ha : a.length = 40) (hb : b.length = 40) :
    ProofLib.ByteSlice.slice (a ++ b ++ c ++ d) 40 40 = b := by
  unfold ProofLib.ByteSlice.slice; simp only [List.append_assoc]
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, show 40 - a.length = 0 by omega,
      List.drop_zero, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

private theorem slice_append4_80 {a b c d : List (BitVec 8)}
    (ha : a.length = 40) (hb : b.length = 40) (hc : c.length = 40) :
    ProofLib.ByteSlice.slice (a ++ b ++ c ++ d) 80 40 = c := by
  unfold ProofLib.ByteSlice.slice; have hab : (a ++ b).length = 80 := by simp [ha, hb]
  rw [show a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) by simp [List.append_assoc],
      List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, show 80 - (a ++ b).length = 0 by omega,
      List.drop_zero, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

private theorem slice_append4_120 {a b c d : List (BitVec 8)}
    (ha : a.length = 40) (hb : b.length = 40) (hc : c.length = 40) (hd : d.length = 40) :
    ProofLib.ByteSlice.slice (a ++ b ++ c ++ d) 120 40 = d := by
  unfold ProofLib.ByteSlice.slice; have habc : (a ++ b ++ c).length = 120 := by simp [ha, hb, hc]
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show 120 - (a ++ b ++ c).length = 0 by omega, List.drop_zero, List.take_of_length_le (by omega)]

private theorem fe51LimbsBoundedAt_eq_slice (bs : List (BitVec 8)) (off bound : Nat)
    (hsl : (ProofLib.ByteSlice.slice bs off 40).length = 40) :
    fe51LimbsBoundedAt bs off bound ↔ fe51LimbsBounded (ProofLib.ByteSlice.slice bs off 40) bound := by
  unfold fe51LimbsBoundedAt fe51LimbsBounded
  simp (disch := decide) only [readLE_slice_eq, Nat.add_zero, hsl, true_and]

private theorem fe51ValAt_eq_slice (bs : List (BitVec 8)) (off : Nat) :
    fe51ValAt bs off = fe51ValOfBytes (ProofLib.ByteSlice.slice bs off 40) := by
  unfold fe51ValAt fe51ValOfBytes
  simp (disch := decide) only [readLE_slice_eq, Nat.add_zero]

theorem edExtToBytes51_bounded51 (P : EdExtPoint) : fe51Point4Bounded (edExtToBytes51 P) (2 ^ 51) := by
  have hL := fe51OfNat51_length; refine ⟨edExtToBytes51_length P, ?_, ?_, ?_, ?_⟩
  · rw [fe51LimbsBoundedAt_eq_slice _ 0 _ (by rw [edExtToBytes51, slice_append4_0 (hL _)]; rfl),
        edExtToBytes51, slice_append4_0 (hL _)]; exact fe51OfNat51_bounded51 P.X
  · rw [fe51LimbsBoundedAt_eq_slice _ 40 _ (by rw [edExtToBytes51, slice_append4_40 (hL _) (hL _)]; rfl),
        edExtToBytes51, slice_append4_40 (hL _) (hL _)]; exact fe51OfNat51_bounded51 P.Y
  · rw [fe51LimbsBoundedAt_eq_slice _ 80 _ (by rw [edExtToBytes51, slice_append4_80 (hL _) (hL _) (hL _)]; rfl),
        edExtToBytes51, slice_append4_80 (hL _) (hL _) (hL _)]; exact fe51OfNat51_bounded51 P.Z
  · rw [fe51LimbsBoundedAt_eq_slice _ 120 _ (by rw [edExtToBytes51, slice_append4_120 (hL _) (hL _) (hL _) (hL _)]; rfl),
        edExtToBytes51, slice_append4_120 (hL _) (hL _) (hL _) (hL _)]; exact fe51OfNat51_bounded51 P.T

theorem edExtToBytes51_bounded (P : EdExtPoint) : fe51Point4Bounded (edExtToBytes51 P) (2 ^ 52) :=
  fe51Point4Bounded_mono (edExtToBytes51_bounded51 P) (by decide)

theorem edExtOfBytes_edExtToBytes51_mod (P : EdExtPoint) :
    edExtOfBytes (edExtToBytes51 P) = ⟨P.X % p25519, P.Y % p25519, P.Z % p25519, P.T % p25519⟩ := by
  have hL := fe51OfNat51_length; unfold edExtOfBytes edExtToBytes51
  rw [fe51ValAt_eq_slice _ 0, fe51ValAt_eq_slice _ 40, fe51ValAt_eq_slice _ 80, fe51ValAt_eq_slice _ 120,
      slice_append4_0 (hL _), slice_append4_40 (hL _) (hL _),
      slice_append4_80 (hL _) (hL _) (hL _), slice_append4_120 (hL _) (hL _) (hL _) (hL _)]
  simp only [fe51ValOfBytes_fe51OfNat51, Nat.mod_mod]

theorem edExtOfBytes_edExtToBytes51 {P : EdExtPoint}
    (h : P.X < p25519 ∧ P.Y < p25519 ∧ P.Z < p25519 ∧ P.T < p25519) :
    edExtOfBytes (edExtToBytes51 P) = P := by
  rcases h with ⟨hX, hY, hZ, hT⟩
  rw [edExtOfBytes_edExtToBytes51_mod, Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hY, Nat.mod_eq_of_lt hZ, Nat.mod_eq_of_lt hT]

@[simp] theorem edExtOfBytes_edExtToBytes51_edExtOfAffine (A : EdPoint) :
    edExtOfBytes (edExtToBytes51 (edExtOfAffine A)) = edExtOfAffine A := by
  apply edExtOfBytes_edExtToBytes51; unfold edExtOfAffine fpMul; dsimp only
  exact ⟨Nat.mod_lt _ p25519_pos, Nat.mod_lt _ p25519_pos, p25519_gt_one, Nat.mod_lt _ p25519_pos⟩

@[simp] theorem edExtOfBytes_edExtToBytes51_edProjectiveToExtended (P : EdExtPoint) :
    edExtOfBytes (edExtToBytes51 (edProjectiveToExtended P)) = edProjectiveToExtended P := by
  apply edExtOfBytes_edExtToBytes51; unfold edProjectiveToExtended fpMul; dsimp only
  exact ⟨Nat.mod_lt _ p25519_pos, Nat.mod_lt _ p25519_pos, fpPow_lt _ _, Nat.mod_lt _ p25519_pos⟩

@[simp] theorem edExtOfBytes_edExtToBytes51_dsmb (a_bs A_bs b_bs : List (BitVec 8)) :
    edExtOfBytes (edExtToBytes51 (edDoubleScalarMulBasepoint a_bs A_bs b_bs)) =
      edDoubleScalarMulBasepoint a_bs A_bs b_bs := by
  unfold edDoubleScalarMulBasepoint; exact edExtOfBytes_edExtToBytes51_edProjectiveToExtended _

attribute [local irreducible] edVarBaseMul edDoubleScalarMulBasepoint

@[expose] def dalekMontToEdVec (u : List.Vector (BitVec 8) 32) (sign : BitVec 8) : Option (List.Vector (BitVec 8) 160) :=
  (montToEdwards u.toList (if (sign &&& 1#8) == 1#8 then 1 else 0)).map fun A =>
    ⟨edExtToBytes51 (edExtOfAffine A), edExtToBytes51_length _⟩

@[expose] def dalekCompressVec (v : List.Vector (BitVec 8) 160) : List.Vector (BitVec 8) 32 :=
  ⟨encodeEd (edExtToAffine (edExtOfBytes v.toList)), by unfold encodeEd; exact natToLeBytes_len 32 _⟩

@[expose] def dalekTorsionFreeBool (v : List.Vector (BitVec 8) 160) : Bool :=
  edPointEq (edVarBaseMul v.toList basepointOrderBytes) edExtZero

@[expose] def dalekDsmbVec (a : List.Vector (BitVec 8) 32) (A : List.Vector (BitVec 8) 160)
    (b : List.Vector (BitVec 8) 32) : List.Vector (BitVec 8) 160 :=
  ⟨edExtToBytes51 (edDoubleScalarMulBasepoint a.toList A.toList b.toList), edExtToBytes51_length _⟩

@[expose] def dalekPrimsReal : DalekPrims :=
  ⟨dalekMontToEdVec, dalekCompressVec, dalekEdNegVec, dalekTorsionFreeBool, dalekDsmbVec, dalekScalarModVec, dalekScalarWideVec⟩

@[expose] def dalekScalarModFallback : State → State := scalarModHook dalekScalarModVec
@[expose] def dalekScalarWideFallback : State → State := scalarWideHook dalekScalarWideVec
@[expose] def dalekMontToEdFallback : State → State := toEdwardsHook dalekMontToEdVec
@[expose] def dalekCompressFallback : State → State := compressHook dalekCompressVec
@[expose] def dalekTorsionFreeFallback : State → State := torsionFreeHook dalekTorsionFreeBool
@[expose] def dalekDsmbFallback : State → State := dsmbHook dalekDsmbVec

@[expose] def PureFallbackPreserved (fb : State → State) : Prop :=
  ∀ s : State, VmPreserved s (fb s) ∧ (fb s).fs = s.fs ∧ (fb s).trace = s.trace ∧
    (fb s).tpidrEl0 = s.tpidrEl0 ∧ (fb s).oracle = s.oracle

private theorem preserved_of_retMem {fb : State → State}
    (h : ∀ s : State, ∃ m : Memory,
      fb s = CryptoVerification.LibsignalAesCbc.returnToLinkRegister (s.setMem m) ∧ m.perm = s.mem.perm) :
    PureFallbackPreserved fb := fun s => by
  obtain ⟨m, hfb, hp⟩ := h s; rw [hfb]
  exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl, congrFun hp, FdsHiFrame.of_fs_eq rfl⟩, rfl, rfl, rfl, rfl⟩

theorem dalekScalarModFallback_preserved : PureFallbackPreserved dalekScalarModFallback :=
  preserved_of_retMem fun s => ⟨_, rfl, Memory.perm_writeBytes s.mem _ _⟩

theorem dalekScalarWideFallback_preserved : PureFallbackPreserved dalekScalarWideFallback :=
  preserved_of_retMem fun s => ⟨_, rfl, Memory.perm_writeBytes s.mem _ _⟩

theorem dalekMontToEdFallback_preserved : PureFallbackPreserved dalekMontToEdFallback :=
  preserved_of_retMem fun s => ⟨_, rfl, by
    split
    · exact (Memory.perm_writeBytes _ _ _).trans (Memory.perm_write64 s.mem _ _)
    · exact Memory.perm_write64 s.mem _ _⟩

theorem dalekCompressFallback_preserved : PureFallbackPreserved dalekCompressFallback :=
  preserved_of_retMem fun s => ⟨_, rfl, Memory.perm_writeBytes s.mem _ _⟩

theorem dalekTorsionFreeFallback_preserved : PureFallbackPreserved dalekTorsionFreeFallback := fun s => by
  unfold dalekTorsionFreeFallback torsionFreeHook CryptoVerification.LibsignalAesCbc.returnToLinkRegister
  cases s; dsimp only [State.writeReg64, State.setPC]
  exact ⟨⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩, rfl, rfl, rfl, rfl⟩

theorem dalekDsmbFallback_preserved : PureFallbackPreserved dalekDsmbFallback :=
  preserved_of_retMem fun s => ⟨_, rfl, Memory.perm_writeBytes s.mem _ _⟩

private theorem fsT_of_preserved {fb : State → State} (hp : PureFallbackPreserved fb) :
    HookFsTraced IsFsC fb :=
  fun s => FsTraced.of_eq (hp s).2.2.1 (congrArg FsState.files (hp s).2.1)

theorem dalekScalarModFallback_fsT : HookFsTraced IsFsC dalekScalarModFallback := fsT_of_preserved dalekScalarModFallback_preserved
theorem dalekScalarWideFallback_fsT : HookFsTraced IsFsC dalekScalarWideFallback := fsT_of_preserved dalekScalarWideFallback_preserved
theorem dalekMontToEdFallback_fsT : HookFsTraced IsFsC dalekMontToEdFallback := fsT_of_preserved dalekMontToEdFallback_preserved
theorem dalekCompressFallback_fsT : HookFsTraced IsFsC dalekCompressFallback := fsT_of_preserved dalekCompressFallback_preserved
theorem dalekTorsionFreeFallback_fsT : HookFsTraced IsFsC dalekTorsionFreeFallback := fsT_of_preserved dalekTorsionFreeFallback_preserved
theorem dalekDsmbFallback_fsT : HookFsTraced IsFsC dalekDsmbFallback := fsT_of_preserved dalekDsmbFallback_preserved

/-! ## 2. Stack-Parametric Ghost Specs & Pure Fallback `HookOk` -/

@[expose] def dalekHookStack : Nat := 5120

private theorem satisfies_prepend_pure {m : Memory} {P : Prop} {Q : SepProp} (hP : P) (hQ : m ⊨ Q) :
    m ⊨ ⌜P⌝ ∗ Q := (satisfies_pure_sepConj P Q m).mpr ⟨hP, hQ⟩

private theorem hookOk_keepsFs {α : Type} {fb : State → State} {spec : Spec α}
    (hok : HookOk fb spec) (hfs : ∀ s : State, (fb s).fs = s.fs)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) : HookOk fb (keepsFs spec) :=
  fun x R s0 hrun hpre hsp => by
    obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp; refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [keepsFs]; rw [sepConj_assoc]; exact satisfies_prepend_pure (hfs s0) hpost
    · rw [hpan] at hp; exact (not_satisfies_false_sepConj hp).elim
    · rw [hex] at he; exact (not_satisfies_false_sepConj he).elim
    · rw [hoom] at ho; exact (not_satisfies_false_sepConj ho).elim

private theorem hookOk_of_simulates_local {α β : Type} {fb : State → State}
    {s₁ : Spec α} {s₂ : Spec β} (hsim : SpecSimulates s₁ s₂) (hok : HookOk fb s₁) : HookOk fb s₂ :=
  fun y R s0 hrun hpre hsp => by
    obtain ⟨x, R₁, hpre₁, hmap⟩ := hsim y R s0 hpre
    obtain ⟨hkf, hsym, hout₁⟩ := hok x R₁ s0 hrun hpre₁ hsp
    exact ⟨hkf, hsym, hmap (fb s0) hout₁⟩

/-! ### 2.1 `B01` (`lsScalarModSymCli`) & `B02` (`lsScalarWideSymCli`) -/

@[expose] def dalekPureLeafCore {m n : Nat}
    (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n) (byVal : Bool) :
    Spec (BitVec 64 × List.Vector (BitVec 8) m × BitVec 64) where
  pre := fun (inA, v, ret) s =>
    ⌜s.readReg64 .x0 = inA ∧ s.readReg64 .x8 = ret⌝ ∗ (inA ↦ₛ v.toList) ∗ memRegion ret n
  post := fun (inA, v, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ inputAfter byVal inA v ∗ (ret ↦ₛ (f v).toList)

@[expose] def dalekScalarModSpec (stk : Nat := dalekHookStack) (byVal : Bool := false) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) :=
  withStack (dalekPureLeafCore dalekScalarModVec byVal) stk

@[expose] def dalekScalarWideSpec (stk : Nat := dalekHookStack) (byVal : Bool := false) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 64 × BitVec 64) :=
  withStack (dalekPureLeafCore dalekScalarWideVec byVal) stk

theorem dalekScalarModSpec_eq_cliExt (byVal : Bool) :
    dalekScalarModSpec extHookStack byVal = pureByteFunctionSpec dalekScalarModVec byVal := rfl

theorem dalekScalarWideSpec_eq_cliExt (byVal : Bool) :
    dalekScalarWideSpec extHookStack byVal = pureByteFunctionSpec dalekScalarWideVec byVal := rfl

theorem dalekPureLeaf_byVal_sim {m n : Nat}
    (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n) (stk : Nat) (byVal : Bool) :
    SpecSimulates (withStack (dalekPureLeafCore f false) stk) (withStack (dalekPureLeafCore f byVal) stk) := by
  refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ⟨⟨inA, v, ret⟩, R, hpre, fun sf _ _ hpost => ?_⟩
  cases byVal
  · exact hpost
  · simp only [withStack, dalekPureLeafCore, inputAfter, Bool.false_eq_true, ↓reduceIte] at hpost ⊢
    have hreord : sf.mem ⊨ (inA ↦ₛ v.toList) ∗ (⌜sf.trace = s0.trace⌝ ∗ (ret ↦ₛ (f v).toList) ∗ stackAt s0.sp stk ∗ R) :=
      Satisfies.mono (by sep_entail) hpost
    exact Satisfies.mono (by sep_entail)
      (Satisfies.mono (sepConj_mono (pointsToBytes_entails_memRegion_of_length v.2) (Entails.refl _)) hreord)

theorem dalekPureLeaf_fallback_ok {m n : Nat} (hn : n ≤ 2 ^ 64)
    (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n) (stk : Nat) :
    HookOk (fun s => CryptoVerification.LibsignalAesCbc.returnToLinkRegister
      (s.setMem (s.mem.writeBytes (s.readReg64 .x8) (f (readVecN s.mem (s.readReg64 .x0) m)).toList)))
      (keepsFs (withStack (dalekPureLeafCore f false) stk)) := by
  refine hookOk_keepsFs ?_ (fun _ => rfl)
  change HookOk (retHook fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (f (readVecN s.mem (s.readReg64 .x0) m)).toList)) (withStack (dalekPureLeafCore f false) stk)
  refine retHook_ok fun ⟨inA, v, ret⟩ R s0 hrun hpre _ => ?_
  simp only [withStack, dalekPureLeafCore, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  have hv := CryptoVerification.E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  have hlen : (f v).toList.length ≤ 2 ^ 64 := by rw [List.Vector.toList_length]; exact hn
  have hmem_out : s0.mem ⊨ memRegion ret (f v).toList.length ∗ ((inA ↦ₛ v.toList) ∗ stackAt s0.sp stk ∗ R) := by
    rw [List.Vector.toList_length]; ac_nf at hmem ⊢
  refine ⟨by simp only [State.setMem, hx0, hx8, hv]; exact keepsFrozen_writeBytes_of_memRegion _ hlen hmem_out,
    rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  have hw := satisfies_writeBytes _ hlen hmem_out
  simp only [withStack, dalekPureLeafCore, inputAfter, Bool.false_eq_true, ↓reduceIte,
    retHook, State.trace_setPC, State.setMem, hx0, hx8, hv, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨trivial, ?_⟩; ac_nf at hw ⊢

theorem dalekScalarModFallback_ok (stk : Nat) : HookOk dalekScalarModFallback (keepsFs (dalekScalarModSpec stk false)) :=
  dalekPureLeaf_fallback_ok (by decide) dalekScalarModVec stk

theorem dalekScalarWideFallback_ok (stk : Nat) : HookOk dalekScalarWideFallback (keepsFs (dalekScalarWideSpec stk false)) :=
  dalekPureLeaf_fallback_ok (by decide) dalekScalarWideVec stk

theorem dalekPureLeaf_post_fsT {m n : Nat}
    (f : List.Vector (BitVec 8) m → List.Vector (BitVec 8) n) (stk : Nat) :
    ∀ x (R : SepProp) (s0 sf : State),
      sf.mem ⊨ (keepsFs (withStack (dalekPureLeafCore f false) stk)).post x s0 sf ∗ R →
        sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  rintro ⟨inA, v, ret⟩ R s0 sf hp; dsimp only [keepsFs, withStack, dalekPureLeafCore] at hp
  simp only [sepConj_assoc] at hp; rw [satisfies_pure_sepConj] at hp; obtain ⟨hfs, hp⟩ := hp
  rw [satisfies_pure_sepConj] at hp; exact ⟨hfs, hp.1⟩

/-! ### 2.2 `B08` (`lsToEdwardsSymCli`) -/

@[expose] def dalekOptionEdwardsAt (r : BitVec 64) : Option EdPoint → SepProp
  | none => (r ↦₆₄ 0#64) ∗ memRegion (r + 8#64) 160
  | some P => ∃∗ pt_bs : List (BitVec 8),
      ⌜fe51Point4Bounded pt_bs (2 ^ 52) ∧ edExtOfBytes pt_bs = edExtOfAffine P⌝ ∗
        (r ↦₆₄ 1#64) ∗ ((r + 8#64) ↦ₛ pt_bs)

@[expose] def dalekMontToEdCore : Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 8 × BitVec 64) where
  pre := fun (uA, u, sign, ret) s =>
    ⌜s.readReg64 .x0 = uA ∧ (s.readReg64 .x1).setWidth 8 = sign ∧ s.readReg64 .x8 = ret⌝ ∗
      (uA ↦ₛ u.toList) ∗ memRegion ret 168
  post := fun (uA, u, sign, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (uA ↦ₛ u.toList) ∗ dalekOptionEdwardsAt ret (montToEdwards u.toList (sign.toNat % 2))

@[expose] def dalekMontToEdSpec (stk : Nat := dalekHookStack) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 8 × BitVec 64) :=
  withStack dalekMontToEdCore stk

theorem montToEdwards_mod2_eq_montLiftEd (u : List.Vector (BitVec 8) 32) (sign : BitVec 8) :
    montToEdwards u.toList (sign.toNat % 2) = montLiftEd u sign := by
  have ha : (sign &&& 1#8) &&& 1#8 = sign &&& 1#8 := by rw [BitVec.and_assoc]; rfl
  have hml : montLiftEd u (sign &&& 1#8) = montLiftEd u sign := by unfold montLiftEd; rw [ha]
  have hand : (sign &&& 1#8).toNat = sign.toNat % 2 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod sign.toNat 1
  rw [← hml, montLiftEd_eq_montToEdwards u (sign &&& 1#8), hand]

private theorem sign_mask_ite_eq_mod2 (sign : BitVec 8) :
    (if ((sign &&& 1#8) &&& 1#8) == 1#8 then 1 else 0) = sign.toNat % 2 := by
  have ha : (sign &&& 1#8) &&& 1#8 = sign &&& 1#8 := by rw [BitVec.and_assoc]; rfl
  rw [ha, sign_and_one_eq_iff]; have := Nat.mod_lt sign.toNat (by decide : 0 < 2)
  by_cases h1 : sign.toNat % 2 = 1
  · simp [h1]
  · have h0 : sign.toNat % 2 = 0 := by omega
    simp [h0]

theorem dalekMontToEd_post_fsT (stk : Nat) :
    ∀ x (R : SepProp) (s0 sf : State),
      sf.mem ⊨ (keepsFs (dalekMontToEdSpec stk)).post x s0 sf ∗ R →
        sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  rintro ⟨uA, u, sign, ret⟩ R s0 sf hp; dsimp only [keepsFs, dalekMontToEdSpec, withStack, dalekMontToEdCore] at hp
  simp only [sepConj_assoc] at hp; rw [satisfies_pure_sepConj] at hp; obtain ⟨hfs, hp⟩ := hp
  rw [satisfies_pure_sepConj] at hp; exact ⟨hfs, hp.1⟩

theorem dalekMontToEdFallback_ok (stk : Nat) : HookOk dalekMontToEdFallback (keepsFs (dalekMontToEdSpec stk)) := by
  refine hookOk_keepsFs ?_ (fun _ => rfl)
  change HookOk (retHook fun s =>
    let r := s.readReg64 .x8
    s.setMem (match dalekMontToEdVec (readVecN s.mem (s.readReg64 .x0) 32) ((s.readReg64 .x1).setWidth 8 &&& 1#8) with
      | some p => (s.mem.write64 r 1#64).writeBytes (r + 8#64) p.toList
      | none => s.mem.write64 r 0#64)) (dalekMontToEdSpec stk)
  refine retHook_ok fun ⟨uA, u, sign, ret⟩ R s0 hrun hpre _ => ?_
  simp only [dalekMontToEdSpec, withStack, dalekMontToEdCore, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  have hu := CryptoVerification.E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  rw [memRegion_split ret 8 160 (by decide), ProofLib.memRegion_eight ret] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, hmem⟩
  have hmem0 : s0.mem ⊨ (ret ↦₆₄ w0) ∗ (memRegion (ret + 8#64) 160 ∗ (uA ↦ₛ u.toList) ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hmem ⊢
  have hvec : dalekMontToEdVec u (sign &&& 1#8) = (montToEdwards u.toList (sign.toNat % 2)).map
      (fun A => ⟨edExtToBytes51 (edExtOfAffine A), edExtToBytes51_length _⟩) := by
    unfold dalekMontToEdVec; rw [sign_mask_ite_eq_mod2]
  rcases hres : montToEdwards u.toList (sign.toNat % 2) with _ | P
  · have hv0 : dalekMontToEdVec u (sign &&& 1#8) = none := by rw [hvec, hres]; rfl
    have hw1 := satisfies_write64_of_pointsTo64 0#64 hmem0
    refine ⟨by dsimp only; rw [hx0, hx1, hx8, hu, hv0]; exact keepsFrozen_write64_of_pointsTo64 0#64 hmem0,
      rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [dalekMontToEdSpec, withStack, dalekMontToEdCore, retHook, State.setMem]; rw [hx0, hx1, hx8, hu, hv0, hres]
    simp only [dalekOptionEdwardsAt, State.trace_setPC, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨trivial, ?_⟩; ac_nf at hw1 ⊢
  · let pt : List.Vector (BitVec 8) 160 := ⟨edExtToBytes51 (edExtOfAffine P), edExtToBytes51_length _⟩
    have hv1 : dalekMontToEdVec u (sign &&& 1#8) = some pt := by rw [hvec, hres]; rfl
    have hw1 := satisfies_write64_of_pointsTo64 1#64 hmem0
    have hmem1 : (s0.mem.write64 ret 1#64) ⊨ memRegion (ret + 8#64) pt.toList.length ∗
        ((ret ↦₆₄ 1#64) ∗ (uA ↦ₛ u.toList) ∗ stackAt s0.sp stk ∗ R) := by rw [List.Vector.toList_length]; ac_nf at hw1 ⊢
    have hlen : pt.toList.length ≤ 2 ^ 64 := by rw [List.Vector.toList_length]; decide
    have hw2 := satisfies_writeBytes pt.toList hlen hmem1
    refine ⟨by dsimp only; rw [hx0, hx1, hx8, hu, hv1]
               exact (keepsFrozen_write64_of_pointsTo64 1#64 hmem0).trans (keepsFrozen_writeBytes_of_memRegion pt.toList hlen hmem1),
      rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [dalekMontToEdSpec, withStack, dalekMontToEdCore, retHook, State.setMem]; rw [hx0, hx1, hx8, hu, hv1, hres]
    simp only [dalekOptionEdwardsAt, State.trace_setPC, Arm64.pure_true, Arm64.emp_sepConj,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨pt.toList, ?_⟩; simp only [sepConj_assoc]
    have hpt : fe51Point4Bounded pt.toList (2 ^ 52) ∧ edExtOfBytes pt.toList = edExtOfAffine P :=
      ⟨edExtToBytes51_bounded (edExtOfAffine P), edExtOfBytes_edExtToBytes51_edExtOfAffine P⟩
    exact Satisfies.mono (by sep_entail) (satisfies_prepend_pure hpt hw2)

/-! ### 2.3 `B14` (`lsCompressSymCli`) -/

@[expose] def dalekCompressCore (byVal : Bool := false) (bound : Nat := 2 ^ 54) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) where
  pre := fun (inA, v, ret) s =>
    ⌜s.readReg64 .x0 = inA ∧ s.readReg64 .x8 = ret ∧ fe51Point4Bounded v.toList bound⌝ ∗
      (inA ↦ₛ v.toList) ∗ memRegion ret 32
  post := fun (inA, v, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ inputAfter byVal inA v ∗ (ret ↦ₛ (dalekCompressVec v).toList)

@[expose] def dalekCompressSpec (stk : Nat := dalekHookStack) (byVal : Bool := false) (bound : Nat := 2 ^ 54) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) :=
  withStack (dalekCompressCore byVal bound) stk

theorem dalekCompress_post_fsT (stk : Nat) :
    ∀ x (R : SepProp) (s0 sf : State),
      sf.mem ⊨ (keepsFs (dalekCompressSpec stk false (2 ^ 54))).post x s0 sf ∗ R →
        sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  rintro ⟨inA, v, ret⟩ R s0 sf hp; dsimp only [keepsFs, dalekCompressSpec, withStack, dalekCompressCore] at hp
  simp only [sepConj_assoc] at hp; rw [satisfies_pure_sepConj] at hp; obtain ⟨hfs, hp⟩ := hp
  rw [satisfies_pure_sepConj] at hp; exact ⟨hfs, hp.1⟩

theorem dalekCompress_byVal_bound_sim (stk : Nat) (byVal : Bool) {bound : Nat} (hb : bound ≤ 2 ^ 54) :
    SpecSimulates (dalekCompressSpec stk false (2 ^ 54)) (dalekCompressSpec stk byVal bound) := by
  refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
  dsimp only [dalekCompressSpec, withStack, dalekCompressCore] at hpre
  simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre; obtain ⟨⟨hx0, hx8, hvb⟩, hmem⟩ := hpre
  refine ⟨⟨inA, v, ret⟩, R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [dalekCompressSpec, withStack, dalekCompressCore]; simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, fe51Point4Bounded_mono hvb hb⟩, hmem⟩
  · cases byVal
    · exact hpost
    · simp only [dalekCompressSpec, withStack, dalekCompressCore, inputAfter, Bool.false_eq_true, ↓reduceIte] at hpost ⊢
      have hreord : sf.mem ⊨ (inA ↦ₛ v.toList) ∗
          (⌜sf.trace = s0.trace⌝ ∗ (ret ↦ₛ (dalekCompressVec v).toList) ∗ stackAt s0.sp stk ∗ R) :=
        Satisfies.mono (by sep_entail) hpost
      exact Satisfies.mono (by sep_entail)
        (Satisfies.mono (sepConj_mono (pointsToBytes_entails_memRegion_of_length v.2) (Entails.refl _)) hreord)

theorem dalekCompressFallback_ok : HookOk dalekCompressFallback (keepsFs (dalekCompressSpec 1552 false (2 ^ 54))) := by
  have hsim : SpecSimulates (withStack (dalekPureLeafCore dalekCompressVec false) 1552) (dalekCompressSpec 1552 false (2 ^ 54)) := by
    refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
    dsimp only [dalekCompressSpec, withStack, dalekCompressCore] at hpre
    simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre; obtain ⟨⟨hx0, hx8, _⟩, hmem⟩ := hpre
    refine ⟨⟨inA, v, ret⟩, R, ?_, fun _ _ _ hp => hp⟩
    dsimp only [withStack, dalekPureLeafCore]; simp only [sepConj_assoc]; rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8⟩, hmem⟩
  exact hookOk_of_simulates_local (specSimulates_keepsFs hsim) (dalekPureLeaf_fallback_ok (by decide) dalekCompressVec 1552)

/-! ### 2.4 `B19` (`lsTorsionFreeSymCli`) -/

theorem dalekTorsionFreeBool_eq_of_valid {p : List.Vector (BitVec 8) 160}
    (hV : EdExtValid (edExtOfBytes p.toList)) :
    dalekTorsionFreeBool p = (edSmul edOrderL (edExtToAffine (edExtOfBytes p.toList)) == edZero) := by
  unfold dalekTorsionFreeBool
  obtain ⟨hW_v, hW_aff⟩ := edVarBaseMul_spec hV basepointOrderBytes_length (by rw [basepointOrderBytes_getD31]; decide)
  rw [edPointEq_eq_beq_toAffine hW_v edExtValid_edExtZero, hW_aff, basepointOrderBytes_val, edExtToAffine_edExtZero]

@[expose] def dalekTorsionFreeCore (bound : Nat := 2 ^ 53) : Spec (BitVec 64 × List.Vector (BitVec 8) 160) where
  pre := fun (pA, p) s => ⌜s.readReg64 .x0 = pA ∧ fe51Point4Bounded p.toList bound⌝ ∗ (pA ↦ₛ p.toList)
  post := fun (pA, p) s0 sf =>
    ⌜sf.trace = s0.trace ∧ (sf.readReg64 .x0).setWidth 32 = (if dalekTorsionFreeBool p then 1#32 else 0#32) ∧
      (EdExtValid (edExtOfBytes p.toList) → (sf.readReg64 .x0).setWidth 32 =
        if edSmul edOrderL (edExtToAffine (edExtOfBytes p.toList)) == edZero then 1#32 else 0#32)⌝ ∗ (pA ↦ₛ p.toList)

@[expose] def dalekTorsionFreeSpec (stk : Nat := dalekHookStack) (bound : Nat := 2 ^ 53) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 160) :=
  withStack (dalekTorsionFreeCore bound) stk

theorem dalekTorsionFree_post_fsT (stk : Nat) :
    ∀ x (R : SepProp) (s0 sf : State),
      sf.mem ⊨ (keepsFs (dalekTorsionFreeSpec stk (2 ^ 53))).post x s0 sf ∗ R →
        sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  rintro ⟨pA, p⟩ R s0 sf hp; dsimp only [keepsFs, dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore] at hp
  simp only [sepConj_assoc] at hp; rw [satisfies_pure_sepConj] at hp; obtain ⟨hfs, hp⟩ := hp
  rw [satisfies_pure_sepConj] at hp; exact ⟨hfs, hp.1.1⟩

theorem dalekTorsionFree_bound_sim (stk : Nat) {bound : Nat} (hb : bound ≤ 2 ^ 53) :
    SpecSimulates (dalekTorsionFreeSpec stk (2 ^ 53)) (dalekTorsionFreeSpec stk bound) := by
  refine SpecSimulates.of_map fun ⟨pA, p⟩ R s0 hpre => ?_
  dsimp only [dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore] at hpre
  simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre; obtain ⟨⟨hx0, hpb⟩, hmem⟩ := hpre
  refine ⟨⟨pA, p⟩, R, ?_, fun _ _ _ hp => hp⟩
  dsimp only [dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore]; simp only [sepConj_assoc]
  rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, fe51Point4Bounded_mono hpb hb⟩, hmem⟩

private theorem torsionFreeHook_eq_retHook (f : List.Vector (BitVec 8) 160 → Bool) :
    torsionFreeHook f = retHook fun s => s.writeReg64 .x0 (if f (readVecN s.mem (s.readReg64 .x0) 160) then 1#64 else 0#64) := by
  funext s; simp [torsionFreeHook, CryptoVerification.LibsignalAesCbc.returnToLinkRegister, retHook]

theorem dalekTorsionFreeFallback_ok : HookOk dalekTorsionFreeFallback (keepsFs (dalekTorsionFreeSpec 4848 (2 ^ 53))) := by
  refine hookOk_keepsFs ?_ (fun _ => rfl); unfold dalekTorsionFreeFallback; rw [torsionFreeHook_eq_retHook]
  refine retHook_ok fun ⟨pA, p⟩ R s0 hrun hpre _ => ?_
  dsimp only [dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore] at hpre
  simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, _⟩, hmem⟩
  have hp := CryptoVerification.E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [dalekTorsionFreeSpec, withStack, dalekTorsionFreeCore]; simp only [sepConj_assoc]; rw [satisfies_pure_sepConj]
  have hw0 : (retHook (fun s => s.writeReg64 .x0 (if dalekTorsionFreeBool (readVecN s.mem (s.readReg64 .x0) 160) then 1#64 else 0#64)) s0).readReg64 .x0 =
      if dalekTorsionFreeBool p then 1#64 else 0#64 := by rw [retHook_writeReg64_x0, hx0, hp]
  have hw32 : BitVec.setWidth 32 (if dalekTorsionFreeBool p then 1#64 else 0#64) =
      if dalekTorsionFreeBool p then 1#32 else 0#32 := by cases dalekTorsionFreeBool p <;> rfl
  exact ⟨⟨State.trace_setPC _ _, by rw [hw0, hw32], fun hV => by rw [hw0, hw32, dalekTorsionFreeBool_eq_of_valid hV]⟩, hmem⟩

/-! ### 2.5 `B17` (`lsDsmbSymCli`) -/

@[expose] def dalekDsmbCore :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 160 ×
      BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) where
  pre := fun (aA, a, pA, p, bA, b, ret) s =>
    ⌜s.readReg64 .x0 = aA ∧ s.readReg64 .x1 = pA ∧ s.readReg64 .x2 = bA ∧ s.readReg64 .x8 = ret ∧
      fe51Point4Bounded p.toList (2 ^ 52)⌝ ∗
      (aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗ (bA ↦ₛ b.toList) ∗ memRegion ret 160
  post := fun (aA, a, pA, p, bA, b, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗ (bA ↦ₛ b.toList) ∗
      (∃∗ res_bs : List (BitVec 8), ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
        edExtOfBytes res_bs = edDoubleScalarMulBasepoint a.toList p.toList b.toList⌝ ∗ (ret ↦ₛ res_bs))

@[expose] def dalekDsmbSpec (stk : Nat := dalekHookStack) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 160 ×
      BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) :=
  withStack dalekDsmbCore stk

theorem dalekDsmb_post_fsT (stk : Nat) :
    ∀ x (R : SepProp) (s0 sf : State),
      sf.mem ⊨ (keepsFs (dalekDsmbSpec stk)).post x s0 sf ∗ R →
        sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  rintro ⟨aA, a, pA, p, bA, b, ret⟩ R s0 sf hp; dsimp only [keepsFs, dalekDsmbSpec, withStack, dalekDsmbCore] at hp
  simp only [sepConj_assoc] at hp; rw [satisfies_pure_sepConj] at hp; obtain ⟨hfs, hp⟩ := hp
  rw [satisfies_pure_sepConj] at hp; exact ⟨hfs, hp.1⟩

private theorem dsmbHook_eq_retHook
    (f : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160) :
    dsmbHook f = retHook fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (f (readVecN s.mem (s.readReg64 .x0) 32) (readVecN s.mem (s.readReg64 .x1) 160)
        (readVecN s.mem (s.readReg64 .x2) 32)).toList) := by
  funext _; rfl

theorem dalekDsmbFallback_ok (stk : Nat) : HookOk dalekDsmbFallback (keepsFs (dalekDsmbSpec stk)) := by
  refine hookOk_keepsFs ?_ (fun _ => rfl); unfold dalekDsmbFallback; rw [dsmbHook_eq_retHook]
  refine retHook_ok fun ⟨aA, a, pA, p, bA, b, ret⟩ R s0 hrun hpre _ => ?_
  dsimp only [dalekDsmbSpec, withStack, dalekDsmbCore] at hpre
  simp only [sepConj_assoc] at hpre; rw [satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx1, hx2, hx8, _⟩, hmem⟩
  have ha := CryptoVerification.E2E.Pqxdh.readVecN_eq_of_pointsToBytes hmem
  have hp := CryptoVerification.E2E.Pqxdh.readVecN_eq_of_pointsToBytes
    (Satisfies.mono (show _ ⊢ (pA ↦ₛ p.toList) ∗ ((aA ↦ₛ a.toList) ∗ (bA ↦ₛ b.toList) ∗ memRegion ret 160 ∗ stackAt s0.sp stk ∗ R) by sep_entail) hmem)
  have hb := CryptoVerification.E2E.Pqxdh.readVecN_eq_of_pointsToBytes
    (Satisfies.mono (show _ ⊢ (bA ↦ₛ b.toList) ∗ ((aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗ memRegion ret 160 ∗ stackAt s0.sp stk ∗ R) by sep_entail) hmem)
  let out := (dalekDsmbVec a p b).toList
  have hout_len : out.length = 160 := List.Vector.toList_length (dalekDsmbVec a p b)
  have hlen : out.length ≤ 2 ^ 64 := by rw [hout_len]; decide
  have hmem_out : s0.mem ⊨ memRegion ret out.length ∗
      ((aA ↦ₛ a.toList) ∗ (pA ↦ₛ p.toList) ∗ (bA ↦ₛ b.toList) ∗ stackAt s0.sp stk ∗ R) := by
    rw [hout_len]; exact Satisfies.mono (by sep_entail) hmem
  refine ⟨by dsimp only [State.setMem]; rw [hx0, hx1, hx2, hx8, ha, hp, hb]; exact keepsFrozen_writeBytes_of_memRegion out hlen hmem_out,
    rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  have hw := satisfies_writeBytes out hlen hmem_out
  dsimp only [dalekDsmbSpec, withStack, dalekDsmbCore, retHook, State.setMem]; rw [hx0, hx1, hx2, hx8, ha, hp, hb]
  simp only [State.trace_setPC, Arm64.pure_true, Arm64.emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨out, ?_⟩; simp only [sepConj_assoc]
  have hout_prop : fe51Point4Bounded out (2 ^ 52) ∧
      edExtOfBytes out = edDoubleScalarMulBasepoint a.toList p.toList b.toList :=
    ⟨edExtToBytes51_bounded _, edExtOfBytes_edExtToBytes51_dsmb a.toList p.toList b.toList⟩
  exact Satisfies.mono (by sep_entail) (satisfies_prepend_pure hout_prop hw)

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks
