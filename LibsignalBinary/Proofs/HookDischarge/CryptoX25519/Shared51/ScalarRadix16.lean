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
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `Scalar::as_radix_16` Machine-Code Proof

Machine-code verification of `Scalar::as_radix_16` (`x25519CliMultiLib` block `03`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.ScalarRadix16

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl X25519Base x25519Leaf_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  scalarRadix16Digits scalarAsRadix16Spec ScalarAsRadix16Ok)

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 03 x25519CliMultiLib X25519CliPlacement 173 rebase rho sub

private theorem exists_bytes32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
      b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8,
      bs = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
            b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] := by
  have h0 : (bs.take 16).length = 16 := by simp [h]
  have h1 : (bs.drop 16).length = 16 := by simp [h]
  have h00 : ((bs.take 16).take 8).length = 8 := by simp [h0]
  have h01 : ((bs.take 16).drop 8).length = 8 := by simp [h0]
  have h10 : ((bs.drop 16).take 8).length = 8 := by simp [h1]
  have h11 : ((bs.drop 16).drop 8).length = 8 := by simp [h]
  rcases h00_eq : (bs.take 16).take 8 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [h00_eq] at h00; simp at h00; done)
  rcases h01_eq : (bs.take 16).drop 8 with _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [h01_eq] at h01; simp at h01; done)
  rcases h10_eq : (bs.drop 16).take 8 with _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [h10_eq] at h10; simp at h10; done)
  rcases h11_eq : (bs.drop 16).drop 8 with _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [h11_eq] at h11; simp at h11; done)
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
          b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, ?_⟩
  have ht16 : bs.take 16 = (bs.take 16).take 8 ++ (bs.take 16).drop 8 := (List.take_append_drop 8 _).symm
  have hd16 : bs.drop 16 = (bs.drop 16).take 8 ++ (bs.drop 16).drop 8 := (List.take_append_drop 8 _).symm
  have hbs : bs = bs.take 16 ++ bs.drop 16 := (List.take_append_drop 16 bs).symm
  rw [hbs, ht16, hd16, h00_eq, h01_eq, h10_eq, h11_eq]
  rfl

private theorem pointsToBytes_sub1_cons2 (p : BitVec 64) (b0 b1 : BitVec 8) (bs : List (BitVec 8)) :
    ((p - 1#64) ↦ₛ (b0 :: b1 :: bs)) = (((p - 1#64) ↦₈ b0) ∗ ((p ↦₈ b1) ∗ ((p + 1#64) ↦ₛ bs))) := by
  rw [pointsToBytes_cons, show p - 1#64 + 1#64 = p by bv_omega, pointsToBytes_cons]
private def radix16SxtbAsr4 (d : BitVec 64) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 d + 8#32) >>> 0 &&& 255#64 |||
    (if (BitVec.setWidth 64 (BitVec.setWidth 32 d + 8#32)).getLsbD 7 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffffffffff00#64)).sshiftRight 4
private def radix16DigitHw (d : BitVec 64) : BitVec 8 :=
  BitVec.truncate 8 (BitVec.setWidth 32 d - BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 d + 8#32) &&& 1030792151280#64))
private theorem radix16SxtbAsr4_eq : ∀ dNat ≤ 16, radix16SxtbAsr4 (BitVec.ofNat 64 dNat) = BitVec.ofNat 32 ((dNat + 8) / 16) := by decide
private theorem radix16DigitHw_eq : ∀ dNat ≤ 16, radix16DigitHw (BitVec.ofNat 64 dNat) = BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16) := by decide
private theorem radix16NextReg_eq (b1 : BitVec 8) : ∀ c ≤ 1, b1.toNat < 16 → BitVec.setWidth 64 (BitVec.zeroExtend 32 b1 + BitVec.ofNat 32 c) = BitVec.ofNat 64 (b1.toNat + c) := by
  revert b1; decide
private theorem radix16NextByte_eq (b1 : BitVec 8) : ∀ c ≤ 1, b1.toNat < 16 → b1 + BitVec.truncate 8 (BitVec.ofNat 32 c) = BitVec.ofNat 8 (b1.toNat + c) := by
  revert b1; decide
private theorem radix16_iter [X25519CliPlacement] (b : BitVec 64) (_hb : X25519Base x25519CliPl03 b) (_hbase : x25519CliPl03.base = b) (target_pc : BitVec 64) (s : State) (R : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp) (p cnt : BitVec 64) (dNat : Nat) (b0 b1 : BitVec 8) (bs : List (BitVec 8))
    (hd : dNat ≤ 16) (hb1 : b1.toNat < 16) (hpc : s.pc = b + 648#64) (hrun : s.status = ExecStatus.Running)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = p) (hx8 : s.readReg64 (Reg.gpr 8#5) = cnt) (hx9 : s.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 dNat)
    (hnext : ∀ s' : State, s'.pc = (if (cnt != 1#64) = true then b + 648#64 else b + 688#64) → s'.status = ExecStatus.Running →
      s'.sp = s.sp → s'.readReg64 Reg.lr = s.readReg64 Reg.lr → CalleeSavedPreserved s s' → s'.readReg64 (Reg.gpr 0#5) = p + 1#64 →
      s'.readReg64 (Reg.gpr 8#5) = cnt - 1#64 → s'.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 (b1.toNat + (dNat + 8) / 16) →
      SepWP (x25519CliPC03.rebase b (fun _ => none)) target_pc s'
        ((((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ ((p ↦₈ BitVec.ofNat 8 (b1.toNat + (dNat + 8) / 16)) ∗ ((p + 1#64) ↦ₛ bs))) ∗ R) post oom) :
    SepWP (x25519CliPC03.rebase b (fun _ => none)) target_pc s (((p - 1#64) ↦ₛ (b0 :: b1 :: bs)) ∗ R) post oom := by
  rw [pointsToBytes_sub1_cons2]; wp_sym_steps 10
  change SepWP (x25519CliPC03.rebase b (fun _ => none)) target_pc _
    ((((p - 1#64) ↦₈ radix16DigitHw (BitVec.ofNat 64 dNat)) ∗ ((p ↦₈ (b1 + BitVec.truncate 8 (radix16SxtbAsr4 (BitVec.ofNat 64 dNat)))) ∗ ((p + 1#64) ↦ₛ bs))) ∗ R) post oom
  have hc : (dNat + 8) / 16 ≤ 1 := by omega
  rw [radix16DigitHw_eq dNat hd, radix16SxtbAsr4_eq dNat hd, radix16NextByte_eq b1 _ hc hb1]
  refine hnext _ rfl hrun rfl rfl ⟨by simp, by simp⟩ rfl rfl ?_
  change BitVec.setWidth 64 (BitVec.zeroExtend 32 b1 + radix16SxtbAsr4 (BitVec.ofNat 64 dNat)) = _; rw [radix16SxtbAsr4_eq dNat hd, radix16NextReg_eq b1 _ hc hb1]
private def recenterNibbles (d : Nat) : List (BitVec 8) → List (BitVec 8)
  | [] => [BitVec.ofNat 8 d]
  | b :: bs => BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16) :: recenterNibbles (b.toNat + (d + 8) / 16) bs
private def allNibbles : List (BitVec 8) → Prop | [] => True | x :: xs => x.toNat < 16 ∧ allNibbles xs
private theorem calleeSavedPreserved_trans {s1 s2 s3 : State} (h1 : CalleeSavedPreserved s1 s2) (h2 : CalleeSavedPreserved s2 s3) : CalleeSavedPreserved s1 s3 := by simp_all [CalleeSavedPreserved]
private theorem radix16_cnt_step : ∀ n < 63, (BitVec.ofNat 64 (n + 2) != 1#64) = true ∧ BitVec.ofNat 64 (n + 2) - 1#64 = BitVec.ofNat 64 (n + 1) := by decide
private theorem pointsToBytes_add1_sub1_cons (p : BitVec 64) (b0 : BitVec 8) (bs : List (BitVec 8)) :
    ((p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ bs)) = ((p + 1#64 - 1#64) ↦ₛ (b0 :: bs)) := by rw [show p + 1#64 - 1#64 = p by bv_omega, pointsToBytes_cons]
private theorem radix16_loop [X25519CliPlacement] (b : BitVec 64) (hb : X25519Base x25519CliPl03 b) (hbase : x25519CliPl03.base = b)
    (target_pc : BitVec 64) (post : State → SepProp → Prop) (oom : State → SepProp) (bs : List (BitVec 8)) :
    ∀ (s : State) (R : SepProp) (p : BitVec 64) (dNat : Nat) (b0 b1 : BitVec 8),
      dNat ≤ 16 → b1.toNat < 16 → allNibbles bs → bs.length < 63 → s.pc = b + 648#64 → s.status = ExecStatus.Running →
      s.readReg64 (Reg.gpr 0#5) = p → s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (bs.length + 1) → s.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 dNat →
      (∀ sf : State, sf.pc = b + 688#64 → sf.status = ExecStatus.Running → sf.sp = s.sp → sf.readReg64 Reg.lr = s.readReg64 Reg.lr →
        CalleeSavedPreserved s sf → SepWP (x25519CliPC03.rebase b (fun _ => none)) target_pc sf (((p - 1#64) ↦ₛ recenterNibbles dNat (b1 :: bs)) ∗ R) post oom) →
      SepWP (x25519CliPC03.rebase b (fun _ => none)) target_pc s (((p - 1#64) ↦ₛ (b0 :: b1 :: bs)) ∗ R) post oom := by
  induction bs with
  | nil =>
    intro s R p dNat b0 b1 hd hb1 _ _ hpc hrun hx0 hx8 hx9 hnext
    refine radix16_iter b hb hbase target_pc s R post oom p 1#64 dNat b0 b1 [] hd hb1 hpc hrun hx0 hx8 hx9 ?_
    intro s' hpc' hrun' hsp' hlr' hcs' _ _ _; rw [← pointsToBytes_sub1_cons2]; exact hnext s' hpc' hrun' hsp' hlr' hcs'
  | cons b2 bs' ih =>
    intro s R p dNat b0 b1 hd hb1 hbs hlen hpc hrun hx0 hx8 hx9 hnext; rcases hbs with ⟨hb2, hbs'⟩
    have hlen' : bs'.length < 63 := by simp at hlen; omega
    have ⟨hcnt_ne, hcnt_sub⟩ := radix16_cnt_step bs'.length hlen'
    refine radix16_iter b hb hbase target_pc s R post oom p (BitVec.ofNat 64 (bs'.length + 2)) dNat b0 b1 (b2 :: bs') hd hb1 hpc hrun hx0 hx8 hx9 ?_
    intro s' hpc' hrun' hsp' hlr' hcs' hx0' hx8' hx9'; rw [hcnt_ne] at hpc'; rw [hcnt_sub] at hx8'
    rw [pointsToBytes_add1_sub1_cons, show (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗
          ((p + 1#64 - 1#64) ↦ₛ (BitVec.ofNat 8 (b1.toNat + (dNat + 8) / 16) :: b2 :: bs'))) ∗ R =
        ((p + 1#64 - 1#64) ↦ₛ (BitVec.ofNat 8 (b1.toNat + (dNat + 8) / 16) :: b2 :: bs')) ∗
          (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ R) by sep_ac_rfl]
    refine ih s' (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ R)
      (p + 1#64) (b1.toNat + (dNat + 8) / 16) (BitVec.ofNat 8 (b1.toNat + (dNat + 8) / 16)) b2 (by omega) hb2 hbs' hlen' hpc' hrun' hx0' hx8' hx9' ?_
    intro sf hpcf hrunf hspf hlrf hcsf
    rw [show ((p + 1#64 - 1#64) ↦ₛ recenterNibbles (b1.toNat + (dNat + 8) / 16) (b2 :: bs')) ∗ (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ R) =
        (((p - 1#64) ↦₈ BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16)) ∗ ((p + 1#64 - 1#64) ↦ₛ recenterNibbles (b1.toNat + (dNat + 8) / 16) (b2 :: bs'))) ∗ R by sep_ac_rfl,
        show p + 1#64 - 1#64 = p - 1#64 + 1#64 by bv_omega, ← pointsToBytes_cons]
    exact hnext sf hpcf hrunf (hspf.trans hsp') (hlrf.trans hlr') (calleeSavedPreserved_trans hcs' hcsf)
private def nibbleAt (a_bs : List (BitVec 8)) (i : Nat) : BitVec 8 := if i % 2 == 0 then a_bs.getD (i / 2) 0#8 &&& 15#8 else a_bs.getD (i / 2) 0#8 >>> 4
private def nibblesFrom (a_bs : List (BitVec 8)) : Nat → List (BitVec 8) | 0 => [] | k + 1 => nibbleAt a_bs (63 - k) :: nibblesFrom a_bs k
private theorem nibbleAt_toNat_lt (a_bs : List (BitVec 8)) (i : Nat) : (nibbleAt a_bs i).toNat < 16 := by
  have h := (by decide : ∀ b : BitVec 8, (b &&& 15#8).toNat < 16 ∧ (b >>> 4).toNat < 16) (a_bs.getD (i / 2) 0#8); unfold nibbleAt; split <;> simp only [h.1, h.2]
private theorem nibblesFrom_allNibbles (a_bs : List (BitVec 8)) : ∀ k, allNibbles (nibblesFrom a_bs k)
  | 0 => trivial | k + 1 => ⟨nibbleAt_toNat_lt a_bs (63 - k), nibblesFrom_allNibbles a_bs k⟩
private theorem nibblesFrom_length (a_bs : List (BitVec 8)) : ∀ k, (nibblesFrom a_bs k).length = k
  | 0 => rfl | k + 1 => by simp [nibblesFrom, nibblesFrom_length a_bs k]
private theorem nibbleAt_toNat_int_eq (a_bs : List (BitVec 8)) (i : Nat) :
    (if i % 2 == 0 then Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat &&& 0x0f) else Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat >>> 4)) = Int.ofNat (nibbleAt a_bs i).toNat := by
  unfold nibbleAt; split <;> simp [BitVec.toNat_and, BitVec.toNat_ushiftRight]
private theorem scalarRadix16Digits_go_eq_recenterNibbles (a_bs : List (BitVec 8)) :
    ∀ (k : Nat) (_hk : k ≤ 63) (carry : Nat) (acc : List (BitVec 8)),
      scalarRadix16Digits.go a_bs (k + 1) (Int.ofNat carry) acc = acc.reverse ++ recenterNibbles ((nibbleAt a_bs (63 - k)).toNat + carry) (nibblesFrom a_bs k) := by
  intro k; induction k with
  | zero =>
    intro _ carry acc; rw [scalarRadix16Digits.go, nibbleAt_toNat_int_eq]
    change scalarRadix16Digits.go a_bs 0 0 (BitVec.ofNat 8 ((nibbleAt a_bs 63).toNat + carry) :: acc) = _
    rw [scalarRadix16Digits.go]; simp [nibblesFrom, recenterNibbles]
  | succ m ih =>
    intro hk carry acc; rw [scalarRadix16Digits.go, nibbleAt_toNat_int_eq]
    have hm : 63 - (m + 1) < 63 := by omega
    let dNat := (nibbleAt a_bs (63 - (m + 1))).toNat + carry
    change (if 63 - (m + 1) < 63 then scalarRadix16Digits.go a_bs (m + 1) (Int.ofNat ((dNat + 8) / 16)) (BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16) :: acc)
      else scalarRadix16Digits.go a_bs (m + 1) 0 (BitVec.ofInt 8 (Int.ofNat dNat) :: acc)) = _
    simp only [hm, ↓reduceIte]; rw [ih (by omega) ((dNat + 8) / 16)]; simp [nibblesFrom, recenterNibbles, dNat]
private theorem scalarRadix16Digits_eq_recenterNibbles (a_bs : List (BitVec 8)) :
    scalarRadix16Digits a_bs = recenterNibbles (nibbleAt a_bs 0).toNat (nibblesFrom a_bs 63) := by
  unfold scalarRadix16Digits; simpa using scalarRadix16Digits_go_eq_recenterNibbles a_bs 63 (by omega) 0 []
private theorem loNibble_hw_eq : ∀ b : BitVec 8, BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b &&& 64424509455#64) = b &&& 15#8 := by decide
private theorem zeroExtend64_eq_ofNat_toNat : ∀ b : BitVec 8, BitVec.zeroExtend 64 b = BitVec.ofNat 64 b.toNat := by decide
private theorem write8_zero_eq_cons (bs : List (BitVec 8)) (v : BitVec 8) : ByteSlice.write8 bs 0 v = v :: bs.drop 1 := rfl
private theorem write8_cons_zero (x v : BitVec 8) (xs : List (BitVec 8)) : ByteSlice.write8 (x :: xs) 0 v = v :: xs := rfl
private theorem write8_cons_succ (x v : BitVec 8) (xs : List (BitVec 8)) (k : Nat) : ByteSlice.write8 (x :: xs) (k + 1) v = x :: ByteSlice.write8 xs k v := rfl
private theorem write8_61_radix16_getD0 (bs : List (BitVec 8))
    (x0 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
     x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 : BitVec 8) :
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 x0) 2 x2) 4 x4) 3 x3) 5 x5) 6 x6) 7 x7) 8 x8) 9 x9) 10 x10) 11 x11) 12 x12) 13 x13) 14 x14) 15 x15)
      16 x16) 17 x17) 18 x18) 19 x19) 20 x20) 21 x21) 22 x22) 23 x23) 24 x24) 25 x25) 26 x26) 27 x27) 28 x28) 29 x29) 30 x30) 31 x31)
      32 x32) 33 x33) 34 x34) 35 x35) 36 x36) 37 x37) 38 x38) 39 x39) 40 x40) 41 x41) 42 x42) 43 x43) 44 x44) 45 x45) 46 x46) 47 x47)
      48 x48) 49 x49) 50 x50) 51 x51) 52 x52) 53 x53) 54 x54) 55 x55) 56 x56) 57 x57) 58 x58) 59 x59) 60 x60) 61 x61).getD 0 0#8 = x0 := by
  simp only [write8_zero_eq_cons, write8_cons_succ, List.getD_cons_zero]
set_option maxRecDepth 20000 in
private theorem write8_64_radix16_order (bs : List (BitVec 8)) (h : bs.length = 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
     x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : BitVec 8) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 x0) 2 x2) 4 x4) 3 x3) 5 x5) 6 x6) 7 x7) 8 x8) 9 x9) 10 x10) 11 x11) 12 x12) 13 x13) 14 x14) 15 x15)
      16 x16) 17 x17) 18 x18) 19 x19) 20 x20) 21 x21) 22 x22) 23 x23) 24 x24) 25 x25) 26 x26) 27 x27) 28 x28) 29 x29) 30 x30) 31 x31)
      32 x32) 33 x33) 34 x34) 35 x35) 36 x36) 37 x37) 38 x38) 39 x39) 40 x40) 41 x41) 42 x42) 43 x43) 44 x44) 45 x45) 46 x46) 47 x47)
      48 x48) 49 x49) 50 x50) 51 x51) 52 x52) 53 x53) 54 x54) 55 x55) 56 x56) 57 x57) 58 x58) 59 x59) 60 x60) 61 x61) 62 x62) 63 x63) 1 x1 =
    [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31,
     x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63] := by
  have h1 : (bs.take 32).length = 32 := by simp [h]
  have h2 : (bs.drop 32).length = 32 := by simp [h]
  rw [← List.take_append_drop 32 bs]
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, htake⟩ := exists_bytes32 h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, hdrop⟩ := exists_bytes32 h2
  rw [htake, hdrop]; simp only [List.cons_append, List.nil_append, write8_cons_zero, write8_cons_succ]

public section

set_option maxHeartbeats 800000 in
theorem scalar_as_radix_16_ok : ScalarAsRadix16Ok := by
  intro _; apply x25519Leaf_ok x25519CliPC03 x25519CliPl03; intro b hb hbase; wp_init; wp_sym_steps 162
  rw [write8_61_radix16_getD0, write8_64_radix16_order a_2 h_3]; simp only [loNibble_hw_eq]
  change SepWP (x25519CliPC03.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) _ (a ↦ₛ a_rest ∗ a_1 ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62)) _
  rw [show a ↦ₛ a_rest ∗ a_1 ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62) =
      ((a_1 + 1#64 - 1#64) ↦ₛ (nibbleAt a_rest 0 :: nibbleAt a_rest 1 :: nibblesFrom a_rest 62)) ∗ (a ↦ₛ a_rest) by rw [show a_1 + 1#64 - 1#64 = a_1 by bv_omega]; sep_ac_rfl]
  refine radix16_loop b hb hbase (s0.readReg64 Reg.lr) _ _ (nibblesFrom a_rest 62) _ (a ↦ₛ a_rest) (a_1 + 1#64) (nibbleAt a_rest 0).toNat (nibbleAt a_rest 0) (nibbleAt a_rest 1)
    (Nat.le_of_lt (nibbleAt_toNat_lt a_rest 0)) (nibbleAt_toNat_lt a_rest 1) (nibblesFrom_allNibbles a_rest 62)
    (by rw [nibblesFrom_length]; omega) rfl hrun rfl (by rw [nibblesFrom_length]; rfl)
    (by change BitVec.zeroExtend 64 (nibbleAt a_rest 0) = _; exact zeroExtend64_eq_ofNat_toNat (nibbleAt a_rest 0)) ?_
  intro sf hpcf hrunf hspf hlrf hcsf
  have hcs0 : CalleeSavedPreserved s0 sf := calleeSavedPreserved_trans (by simp [CalleeSavedPreserved]) hcsf
  have _hlr0 : sf.readReg64 Reg.lr = s0.readReg64 Reg.lr := hlrf; have hsp0 : sf.sp = s0.sp := hspf
  change SepWP (x25519CliPC03.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) sf (((a_1 + 1#64 - 1#64) ↦ₛ recenterNibbles (nibbleAt a_rest 0).toNat (nibblesFrom a_rest 63)) ∗ (a ↦ₛ a_rest)) _
  rw [show a_1 + 1#64 - 1#64 = a_1 by bv_omega, ← scalarRadix16Digits_eq_recenterNibbles]
  wp_sym_steps 1; refine SepWP.done rfl hrunf ⟨fun hmem => ?_, hsp0, hcs0⟩
  rwa [show (a ↦ₛ a_rest ∗ a_1 ↦ₛ scalarRadix16Digits a_rest) ∗ R = (a_1 ↦ₛ scalarRadix16Digits a_rest ∗ a ↦ₛ a_rest) ∗ R by sep_ac_rfl]

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.ScalarRadix16
