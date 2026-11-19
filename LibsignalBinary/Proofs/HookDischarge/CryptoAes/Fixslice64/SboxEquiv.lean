/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing

/-!
# Bitsliced S-Box and Inverse S-Box Equivalence (`Fixslice64.SboxEquiv`)

Proves `bv_decide`-free equivalence between the 64-lane bitsliced Boyar–Peralta–Calik `sub_bytes`
and `inv_sub_bytes` circuits in `Fixslice64.Model` and the FIPS 197 table-based `subBytes` and
`invSubBytes` transformations across all 4 lanes:
- `subBytesNots_subBytesFs_bitslice`:
  `subBytesNots (subBytesFs (bitslice bs)) = bitslice (bs.map subBytes)`
- `invSubBytesFs_subBytesNots_bitslice`:
  `invSubBytesFs (subBytesNots (bitslice bs)) = bitslice (bs.map invSubBytes)`
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxEquiv

open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
  (State sbox invSbox subBytes invSubBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (FsState Blocks4 notsMask subBytesNots bitslice SubBytesW1 SubBytesW2 SubBytesW3 SubBytesW4 subBytesFsStage1 subBytesFsStage2 subBytesFsStage3 subBytesFsStage4 subBytesFsStage5 subBytesFs InvSubBytesW1 InvSubBytesW2 InvSubBytesW3 InvSubBytesW4 InvSubBytesW5 invSubBytesFsStage1 invSubBytesFsStage2 invSubBytesFsStage3 invSubBytesFsStage4 invSubBytesFsStage5 invSubBytesFsStage6 invSubBytesFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing
  (getLsbD_bitslice eq_bitslice_of_getLsbD)

/-! ## Strict 1-Bit Boolean Evaluators and Coordinate Extraction -/

/-- Strict call-by-value boolean binder for linear-time kernel `decide` evaluation. -/
private def strictBool {α : Type} (v : Bool) (k : Bool → α) : α :=
  match v with
  | true => k true
  | false => k false

@[simp] private theorem strictBool_eq {α : Type} (v : Bool) (k : Bool → α) :
    strictBool v k = k v := by
  cases v <;> rfl

@[ext] private structure FsBool8 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  deriving DecidableEq, Repr

private def FsBool8.getBit (x : FsBool8) : Nat → Bool
  | 0 => x.b0 | 1 => x.b1 | 2 => x.b2 | 3 => x.b3
  | 4 => x.b4 | 5 => x.b5 | 6 => x.b6 | 7 => x.b7
  | _ => false

private def extractBool8 (st : FsState) (k : Nat) : FsBool8 :=
  ⟨st.s0.getLsbD k, st.s1.getLsbD k, st.s2.getLsbD k, st.s3.getLsbD k,
   st.s4.getLsbD k, st.s5.getLsbD k, st.s6.getLsbD k, st.s7.getLsbD k⟩

private theorem getBit_extractBool8 (st : FsState) (k p : Nat) (hp : p < 8) :
    (extractBool8 st k).getBit p = (st.getSlice p).getLsbD k := by
  match p, hp with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  | _ + 8, hp => omega

private def byteToBool8 (b : BitVec 8) : FsBool8 :=
  ⟨b.getLsbD 0, b.getLsbD 1, b.getLsbD 2, b.getLsbD 3,
   b.getLsbD 4, b.getLsbD 5, b.getLsbD 6, b.getLsbD 7⟩

private theorem getBit_byteToBool8 (b : BitVec 8) (p : Nat) (hp : p < 8) :
    (byteToBool8 b).getBit p = b.getLsbD p := by
  match p, hp with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  | _ + 8, hp => omega

private def notsBool8 (x : FsBool8) : FsBool8 :=
  ⟨!x.b0, !x.b1, x.b2, x.b3, x.b4, !x.b5, !x.b6, x.b7⟩

private theorem extract_subBytesNots (st : FsState) (k : Nat) (hk : k < 64) :
    extractBool8 (subBytesNots st) k = notsBool8 (extractBool8 st k) := by
  have h1 : (0xffffffffffffffff#64).getLsbD k = true := by
    have : 0xffffffffffffffff#64 = BitVec.allOnes 64 := rfl
    rw [this, BitVec.getLsbD_allOnes]
    simp [hk]
  ext1 <;> simp [extractBool8, subBytesNots, FsState.zipWith, notsMask, notsBool8,
    BitVec.getLsbD_xor, h1]

/-! ## Staged Coordinate Extraction for `subBytesFs` and `invSubBytesFs` -/

@[ext] private structure SubBytesB1 where
  t0 : Bool
  t14 : Bool
  t16 : Bool
  t2 : Bool
  t7 : Bool
  u0 : Bool
  u3 : Bool
  u6 : Bool
  u7 : Bool
  y10 : Bool
  y11 : Bool
  y12 : Bool
  y13 : Bool
  y14 : Bool
  y15 : Bool
  y16 : Bool
  y17 : Bool
  y18 : Bool
  y19 : Bool
  y20 : Bool
  y21 : Bool
  y6 : Bool
  y7 : Bool
  y8 : Bool
  y9 : Bool
  deriving DecidableEq, Repr

private def extractSubBytesW1 (w : SubBytesW1) (k : Nat) : SubBytesB1 :=
  ⟨w.t0.getLsbD k, w.t14.getLsbD k, w.t16.getLsbD k, w.t2.getLsbD k, w.t7.getLsbD k, w.u0.getLsbD k, w.u3.getLsbD k, w.u6.getLsbD k, w.u7.getLsbD k, w.y10.getLsbD k, w.y11.getLsbD k, w.y12.getLsbD k, w.y13.getLsbD k, w.y14.getLsbD k, w.y15.getLsbD k, w.y16.getLsbD k, w.y17.getLsbD k, w.y18.getLsbD k, w.y19.getLsbD k, w.y20.getLsbD k, w.y21.getLsbD k, w.y6.getLsbD k, w.y7.getLsbD k, w.y8.getLsbD k, w.y9.getLsbD k⟩

@[ext] private structure SubBytesB2 where
  t22 : Bool
  t23 : Bool
  t24 : Bool
  t25 : Bool
  t27 : Bool
  t31 : Bool
  u7 : Bool
  y1 : Bool
  y10 : Bool
  y11 : Bool
  y12 : Bool
  y13 : Bool
  y14 : Bool
  y15 : Bool
  y16 : Bool
  y17 : Bool
  y2 : Bool
  y3 : Bool
  y4 : Bool
  y5 : Bool
  y6 : Bool
  y7 : Bool
  y8 : Bool
  y9 : Bool
  deriving DecidableEq, Repr

private def extractSubBytesW2 (w : SubBytesW2) (k : Nat) : SubBytesB2 :=
  ⟨w.t22.getLsbD k, w.t23.getLsbD k, w.t24.getLsbD k, w.t25.getLsbD k, w.t27.getLsbD k, w.t31.getLsbD k, w.u7.getLsbD k, w.y1.getLsbD k, w.y10.getLsbD k, w.y11.getLsbD k, w.y12.getLsbD k, w.y13.getLsbD k, w.y14.getLsbD k, w.y15.getLsbD k, w.y16.getLsbD k, w.y17.getLsbD k, w.y2.getLsbD k, w.y3.getLsbD k, w.y4.getLsbD k, w.y5.getLsbD k, w.y6.getLsbD k, w.y7.getLsbD k, w.y8.getLsbD k, w.y9.getLsbD k⟩

@[ext] private structure SubBytesB3 where
  t29 : Bool
  t33 : Bool
  t37 : Bool
  t41 : Bool
  t44 : Bool
  tc12 : Bool
  tc6 : Bool
  u7 : Bool
  y11 : Bool
  y12 : Bool
  y14 : Bool
  y15 : Bool
  y17 : Bool
  y3 : Bool
  y4 : Bool
  y6 : Bool
  y9 : Bool
  z12 : Bool
  z13 : Bool
  z14 : Bool
  z17 : Bool
  z8 : Bool
  deriving DecidableEq, Repr

private def extractSubBytesW3 (w : SubBytesW3) (k : Nat) : SubBytesB3 :=
  ⟨w.t29.getLsbD k, w.t33.getLsbD k, w.t37.getLsbD k, w.t41.getLsbD k, w.t44.getLsbD k, w.tc12.getLsbD k, w.tc6.getLsbD k, w.u7.getLsbD k, w.y11.getLsbD k, w.y12.getLsbD k, w.y14.getLsbD k, w.y15.getLsbD k, w.y17.getLsbD k, w.y3.getLsbD k, w.y4.getLsbD k, w.y6.getLsbD k, w.y9.getLsbD k, w.z12.getLsbD k, w.z13.getLsbD k, w.z14.getLsbD k, w.z17.getLsbD k, w.z8.getLsbD k⟩

@[ext] private structure SubBytesB4 where
  s0 : Bool
  s1 : Bool
  s3 : Bool
  tc12 : Bool
  tc13 : Bool
  tc20 : Bool
  tc21 : Bool
  tc8 : Bool
  z0 : Bool
  z12 : Bool
  z14 : Bool
  z17 : Bool
  z2 : Bool
  z8 : Bool
  deriving DecidableEq, Repr

private def extractSubBytesW4 (w : SubBytesW4) (k : Nat) : SubBytesB4 :=
  ⟨w.s0.getLsbD k, w.s1.getLsbD k, w.s3.getLsbD k, w.tc12.getLsbD k, w.tc13.getLsbD k, w.tc20.getLsbD k, w.tc21.getLsbD k, w.tc8.getLsbD k, w.z0.getLsbD k, w.z12.getLsbD k, w.z14.getLsbD k, w.z17.getLsbD k, w.z2.getLsbD k, w.z8.getLsbD k⟩

private def subBytesBoolStage1 (inp : FsBool8) : SubBytesB1 :=
  strictBool inp.b0 fun u7 =>
  strictBool inp.b1 fun u6 =>
  strictBool inp.b2 fun u5 =>
  strictBool inp.b3 fun u4 =>
  strictBool inp.b4 fun u3 =>
  strictBool inp.b5 fun u2 =>
  strictBool inp.b6 fun u1 =>
  strictBool inp.b7 fun u0 =>
  strictBool (u3 ^^ u5) fun y14 =>
  strictBool (u0 ^^ u6) fun y13 =>
  strictBool (y13 ^^ y14) fun y12 =>
  strictBool (u4 ^^ y12) fun t1 =>
  strictBool (t1 ^^ u5) fun y15 =>
  strictBool (y12 && y15) fun t2 =>
  strictBool (y15 ^^ u7) fun y6 =>
  strictBool (t1 ^^ u1) fun y20 =>
  strictBool (u0 ^^ u3) fun y9 =>
  strictBool (y20 ^^ y9) fun y11 =>
  strictBool (y9 && y11) fun t12 =>
  strictBool (u7 ^^ y11) fun y7 =>
  strictBool (u0 ^^ u5) fun y8 =>
  strictBool (u1 ^^ u2) fun t0 =>
  strictBool (y15 ^^ t0) fun y10 =>
  strictBool (y10 ^^ y11) fun y17 =>
  strictBool (y14 && y17) fun t13 =>
  strictBool (t13 ^^ t12) fun t14 =>
  strictBool (y10 ^^ y8) fun y19 =>
  strictBool (y8 && y10) fun t15 =>
  strictBool (t15 ^^ t12) fun t16 =>
  strictBool (t0 ^^ y11) fun y16 =>
  strictBool (y13 ^^ y16) fun y21 =>
  strictBool (y13 && y16) fun t7 =>
  strictBool (u0 ^^ y16) fun y18 =>
  ⟨t0, t14, t16, t2, t7, u0, u3, u6, u7, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y6, y7, y8, y9⟩

private theorem extract_subBytesFsStage1 (inp : FsState) (k : Nat) :
    extractSubBytesW1 (subBytesFsStage1 inp) k = subBytesBoolStage1 (extractBool8 inp k) := by
  ext1 <;> simp only [extractSubBytesW1, subBytesFsStage1, subBytesBoolStage1, extractBool8, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def subBytesBoolStage2 (inp : SubBytesB1) : SubBytesB2 :=
  strictBool inp.t0 fun t0 =>
  strictBool inp.t14 fun t14 =>
  strictBool inp.t16 fun t16 =>
  strictBool inp.t2 fun t2 =>
  strictBool inp.t7 fun t7 =>
  strictBool inp.u0 fun u0 =>
  strictBool inp.u3 fun u3 =>
  strictBool inp.u6 fun u6 =>
  strictBool inp.u7 fun u7 =>
  strictBool inp.y10 fun y10 =>
  strictBool inp.y11 fun y11 =>
  strictBool inp.y12 fun y12 =>
  strictBool inp.y13 fun y13 =>
  strictBool inp.y14 fun y14 =>
  strictBool inp.y15 fun y15 =>
  strictBool inp.y16 fun y16 =>
  strictBool inp.y17 fun y17 =>
  strictBool inp.y18 fun y18 =>
  strictBool inp.y19 fun y19 =>
  strictBool inp.y20 fun y20 =>
  strictBool inp.y21 fun y21 =>
  strictBool inp.y6 fun y6 =>
  strictBool inp.y7 fun y7 =>
  strictBool inp.y8 fun y8 =>
  strictBool inp.y9 fun y9 =>
  strictBool (t0 ^^ u7) fun y1 =>
  strictBool (y1 ^^ u3) fun y4 =>
  strictBool (y4 && u7) fun t5 =>
  strictBool (t5 ^^ t2) fun t6 =>
  strictBool (t6 ^^ t16) fun t18 =>
  strictBool (t18 ^^ y19) fun t22 =>
  strictBool (y1 ^^ u0) fun y2 =>
  strictBool (y2 && y7) fun t10 =>
  strictBool (t10 ^^ t7) fun t11 =>
  strictBool (t11 ^^ t16) fun t20 =>
  strictBool (t20 ^^ y18) fun t24 =>
  strictBool (y1 ^^ u6) fun y5 =>
  strictBool (y5 && y1) fun t8 =>
  strictBool (t8 ^^ t7) fun t9 =>
  strictBool (t9 ^^ t14) fun t19 =>
  strictBool (t19 ^^ y21) fun t23 =>
  strictBool (y5 ^^ y8) fun y3 =>
  strictBool (y3 && y6) fun t3 =>
  strictBool (t3 ^^ t2) fun t4 =>
  strictBool (t4 ^^ y20) fun t17 =>
  strictBool (t17 ^^ t14) fun t21 =>
  strictBool (t21 && t23) fun t26 =>
  strictBool (t24 ^^ t26) fun t27 =>
  strictBool (t22 ^^ t26) fun t31 =>
  strictBool (t21 ^^ t22) fun t25 =>
  ⟨t22, t23, t24, t25, t27, t31, u7, y1, y10, y11, y12, y13, y14, y15, y16, y17, y2, y3, y4, y5, y6, y7, y8, y9⟩

private theorem extract_subBytesFsStage2 (inp : SubBytesW1) (k : Nat) :
    extractSubBytesW2 (subBytesFsStage2 inp) k = subBytesBoolStage2 (extractSubBytesW1 inp k) := by
  ext1 <;> simp only [extractSubBytesW2, subBytesFsStage2, subBytesBoolStage2, extractSubBytesW1, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def subBytesBoolStage3 (inp : SubBytesB2) : SubBytesB3 :=
  strictBool inp.t22 fun t22 =>
  strictBool inp.t23 fun t23 =>
  strictBool inp.t24 fun t24 =>
  strictBool inp.t25 fun t25 =>
  strictBool inp.t27 fun t27 =>
  strictBool inp.t31 fun t31 =>
  strictBool inp.u7 fun u7 =>
  strictBool inp.y1 fun y1 =>
  strictBool inp.y10 fun y10 =>
  strictBool inp.y11 fun y11 =>
  strictBool inp.y12 fun y12 =>
  strictBool inp.y13 fun y13 =>
  strictBool inp.y14 fun y14 =>
  strictBool inp.y15 fun y15 =>
  strictBool inp.y16 fun y16 =>
  strictBool inp.y17 fun y17 =>
  strictBool inp.y2 fun y2 =>
  strictBool inp.y3 fun y3 =>
  strictBool inp.y4 fun y4 =>
  strictBool inp.y5 fun y5 =>
  strictBool inp.y6 fun y6 =>
  strictBool inp.y7 fun y7 =>
  strictBool inp.y8 fun y8 =>
  strictBool inp.y9 fun y9 =>
  strictBool (t25 && t27) fun t28 =>
  strictBool (t28 ^^ t22) fun t29 =>
  strictBool (t29 && y2) fun z14 =>
  strictBool (t29 && y7) fun z5 =>
  strictBool (t23 ^^ t24) fun t30 =>
  strictBool (t31 && t30) fun t32 =>
  strictBool (t32 ^^ t24) fun t33 =>
  strictBool (t27 ^^ t33) fun t35 =>
  strictBool (t24 && t35) fun t36 =>
  strictBool (t27 ^^ t36) fun t38 =>
  strictBool (t29 && t38) fun t39 =>
  strictBool (t25 ^^ t39) fun t40 =>
  strictBool (t29 ^^ t40) fun t43 =>
  strictBool (t43 && y16) fun z3 =>
  strictBool (z3 ^^ z5) fun tc12 =>
  strictBool (t43 && y13) fun z12 =>
  strictBool (t40 && y5) fun z13 =>
  strictBool (t40 && y1) fun z4 =>
  strictBool (z3 ^^ z4) fun tc6 =>
  strictBool (t23 ^^ t33) fun t34 =>
  strictBool (t36 ^^ t34) fun t37 =>
  strictBool (t40 ^^ t37) fun t41 =>
  strictBool (t41 && y10) fun z8 =>
  strictBool (t41 && y8) fun z17 =>
  strictBool (t33 ^^ t37) fun t44 =>
  ⟨t29, t33, t37, t41, t44, tc12, tc6, u7, y11, y12, y14, y15, y17, y3, y4, y6, y9, z12, z13, z14, z17, z8⟩

private theorem extract_subBytesFsStage3 (inp : SubBytesW2) (k : Nat) :
    extractSubBytesW3 (subBytesFsStage3 inp) k = subBytesBoolStage3 (extractSubBytesW2 inp k) := by
  ext1 <;> simp only [extractSubBytesW3, subBytesFsStage3, subBytesBoolStage3, extractSubBytesW2, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def subBytesBoolStage4 (inp : SubBytesB3) : SubBytesB4 :=
  strictBool inp.t29 fun t29 =>
  strictBool inp.t33 fun t33 =>
  strictBool inp.t37 fun t37 =>
  strictBool inp.t41 fun t41 =>
  strictBool inp.t44 fun t44 =>
  strictBool inp.tc12 fun tc12 =>
  strictBool inp.tc6 fun tc6 =>
  strictBool inp.u7 fun u7 =>
  strictBool inp.y11 fun y11 =>
  strictBool inp.y12 fun y12 =>
  strictBool inp.y14 fun y14 =>
  strictBool inp.y15 fun y15 =>
  strictBool inp.y17 fun y17 =>
  strictBool inp.y3 fun y3 =>
  strictBool inp.y4 fun y4 =>
  strictBool inp.y6 fun y6 =>
  strictBool inp.y9 fun y9 =>
  strictBool inp.z12 fun z12 =>
  strictBool inp.z13 fun z13 =>
  strictBool inp.z14 fun z14 =>
  strictBool inp.z17 fun z17 =>
  strictBool inp.z8 fun z8 =>
  strictBool (t44 && y15) fun z0 =>
  strictBool (t44 && y12) fun z9 =>
  strictBool (t37 && y3) fun z10 =>
  strictBool (t37 && y6) fun z1 =>
  strictBool (z1 ^^ z0) fun tc5 =>
  strictBool (tc6 ^^ tc5) fun tc11 =>
  strictBool (t33 && y4) fun z11 =>
  strictBool (t29 ^^ t33) fun t42 =>
  strictBool (t42 ^^ t41) fun t45 =>
  strictBool (t45 && y17) fun z7 =>
  strictBool (z7 ^^ tc6) fun tc8 =>
  strictBool (t45 && y14) fun z16 =>
  strictBool (t42 && y11) fun z6 =>
  strictBool (z6 ^^ tc8) fun tc16 =>
  strictBool (t42 && y9) fun z15 =>
  strictBool (z15 ^^ tc16) fun tc20 =>
  strictBool (z15 ^^ z16) fun tc1 =>
  strictBool (z10 ^^ tc1) fun tc2 =>
  strictBool (tc2 ^^ z11) fun tc21 =>
  strictBool (z9 ^^ tc2) fun tc3 =>
  strictBool (tc3 ^^ tc16) fun s0 =>
  strictBool (tc3 ^^ tc11) fun s3 =>
  strictBool (s3 ^^ tc16) fun s1 =>
  strictBool (z13 ^^ tc1) fun tc13 =>
  strictBool (t33 && u7) fun z2 =>
  ⟨s0, s1, s3, tc12, tc13, tc20, tc21, tc8, z0, z12, z14, z17, z2, z8⟩

private theorem extract_subBytesFsStage4 (inp : SubBytesW3) (k : Nat) :
    extractSubBytesW4 (subBytesFsStage4 inp) k = subBytesBoolStage4 (extractSubBytesW3 inp k) := by
  ext1 <;> simp only [extractSubBytesW4, subBytesFsStage4, subBytesBoolStage4, extractSubBytesW3, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def subBytesBoolStage5 (inp : SubBytesB4) : FsBool8 :=
  strictBool inp.s0 fun s0 =>
  strictBool inp.s1 fun s1 =>
  strictBool inp.s3 fun s3 =>
  strictBool inp.tc12 fun tc12 =>
  strictBool inp.tc13 fun tc13 =>
  strictBool inp.tc20 fun tc20 =>
  strictBool inp.tc21 fun tc21 =>
  strictBool inp.tc8 fun tc8 =>
  strictBool inp.z0 fun z0 =>
  strictBool inp.z12 fun z12 =>
  strictBool inp.z14 fun z14 =>
  strictBool inp.z17 fun z17 =>
  strictBool inp.z2 fun z2 =>
  strictBool inp.z8 fun z8 =>
  strictBool (z0 ^^ z2) fun tc4 =>
  strictBool (z12 ^^ tc4) fun tc7 =>
  strictBool (z8 ^^ tc7) fun tc9 =>
  strictBool (tc8 ^^ tc9) fun tc10 =>
  strictBool (z14 ^^ tc10) fun tc17 =>
  strictBool (tc21 ^^ tc17) fun s5 =>
  strictBool (tc17 ^^ tc20) fun tc26 =>
  strictBool (tc26 ^^ z17) fun s2 =>
  strictBool (tc4 ^^ tc12) fun tc14 =>
  strictBool (tc13 ^^ tc14) fun tc18 =>
  strictBool (tc10 ^^ tc18) fun s6 =>
  strictBool (z12 ^^ tc18) fun s7 =>
  strictBool (tc14 ^^ s3) fun s4 =>
  ⟨s7, s6, s5, s4, s3, s2, s1, s0⟩

private theorem extract_subBytesFsStage5 (inp : SubBytesW4) (k : Nat) :
    extractBool8 (subBytesFsStage5 inp) k = subBytesBoolStage5 (extractSubBytesW4 inp k) := by
  ext1 <;> simp only [extractBool8, subBytesFsStage5, subBytesBoolStage5, extractSubBytesW4, strictBool_eq,
    BitVec.getLsbD_xor]

private def subBytesBool (st : FsBool8) : FsBool8 :=
  subBytesBoolStage5 (subBytesBoolStage4 (subBytesBoolStage3 (subBytesBoolStage2 (subBytesBoolStage1 st))))

private theorem extract_subBytesFs (st : FsState) (k : Nat) :
    extractBool8 (subBytesFs st) k = subBytesBool (extractBool8 st k) := by
  unfold subBytesFs subBytesBool
  rw [extract_subBytesFsStage5, extract_subBytesFsStage4, extract_subBytesFsStage3, extract_subBytesFsStage2, extract_subBytesFsStage1]

@[ext] private structure InvSubBytesB1 where
  m1 : Bool
  m14 : Bool
  m2 : Bool
  m7 : Bool
  m9 : Bool
  r13 : Bool
  t1 : Bool
  t10 : Bool
  t13 : Bool
  t17 : Bool
  t19 : Bool
  t2 : Bool
  t20 : Bool
  t22 : Bool
  t23 : Bool
  t24 : Bool
  t25 : Bool
  t3 : Bool
  t4 : Bool
  t6 : Bool
  t8 : Bool
  t9 : Bool
  u2 : Bool
  u4 : Bool
  u5 : Bool
  u6 : Bool
  y5 : Bool
  deriving DecidableEq, Repr

private def extractInvSubBytesW1 (w : InvSubBytesW1) (k : Nat) : InvSubBytesB1 :=
  ⟨w.m1.getLsbD k, w.m14.getLsbD k, w.m2.getLsbD k, w.m7.getLsbD k, w.m9.getLsbD k, w.r13.getLsbD k, w.t1.getLsbD k, w.t10.getLsbD k, w.t13.getLsbD k, w.t17.getLsbD k, w.t19.getLsbD k, w.t2.getLsbD k, w.t20.getLsbD k, w.t22.getLsbD k, w.t23.getLsbD k, w.t24.getLsbD k, w.t25.getLsbD k, w.t3.getLsbD k, w.t4.getLsbD k, w.t6.getLsbD k, w.t8.getLsbD k, w.t9.getLsbD k, w.u2.getLsbD k, w.u4.getLsbD k, w.u5.getLsbD k, w.u6.getLsbD k, w.y5.getLsbD k⟩

@[ext] private structure InvSubBytesB2 where
  m10 : Bool
  m15 : Bool
  m20 : Bool
  m21 : Bool
  m22 : Bool
  m25 : Bool
  m26 : Bool
  t1 : Bool
  t10 : Bool
  t13 : Bool
  t15 : Bool
  t16 : Bool
  t17 : Bool
  t19 : Bool
  t2 : Bool
  t20 : Bool
  t22 : Bool
  t23 : Bool
  t25 : Bool
  t27 : Bool
  t3 : Bool
  t4 : Bool
  t6 : Bool
  t8 : Bool
  t9 : Bool
  y5 : Bool
  deriving DecidableEq, Repr

private def extractInvSubBytesW2 (w : InvSubBytesW2) (k : Nat) : InvSubBytesB2 :=
  ⟨w.m10.getLsbD k, w.m15.getLsbD k, w.m20.getLsbD k, w.m21.getLsbD k, w.m22.getLsbD k, w.m25.getLsbD k, w.m26.getLsbD k, w.t1.getLsbD k, w.t10.getLsbD k, w.t13.getLsbD k, w.t15.getLsbD k, w.t16.getLsbD k, w.t17.getLsbD k, w.t19.getLsbD k, w.t2.getLsbD k, w.t20.getLsbD k, w.t22.getLsbD k, w.t23.getLsbD k, w.t25.getLsbD k, w.t27.getLsbD k, w.t3.getLsbD k, w.t4.getLsbD k, w.t6.getLsbD k, w.t8.getLsbD k, w.t9.getLsbD k, w.y5.getLsbD k⟩

@[ext] private structure InvSubBytesB3 where
  m21 : Bool
  m22 : Bool
  m24 : Bool
  m36 : Bool
  m38 : Bool
  m39 : Bool
  m42 : Bool
  m43 : Bool
  m48 : Bool
  m49 : Bool
  m51 : Bool
  m57 : Bool
  m60 : Bool
  p0 : Bool
  p16 : Bool
  t10 : Bool
  t13 : Bool
  t2 : Bool
  t22 : Bool
  t23 : Bool
  t27 : Bool
  t3 : Bool
  t4 : Bool
  t6 : Bool
  t8 : Bool
  t9 : Bool
  deriving DecidableEq, Repr

private def extractInvSubBytesW3 (w : InvSubBytesW3) (k : Nat) : InvSubBytesB3 :=
  ⟨w.m21.getLsbD k, w.m22.getLsbD k, w.m24.getLsbD k, w.m36.getLsbD k, w.m38.getLsbD k, w.m39.getLsbD k, w.m42.getLsbD k, w.m43.getLsbD k, w.m48.getLsbD k, w.m49.getLsbD k, w.m51.getLsbD k, w.m57.getLsbD k, w.m60.getLsbD k, w.p0.getLsbD k, w.p16.getLsbD k, w.t10.getLsbD k, w.t13.getLsbD k, w.t2.getLsbD k, w.t22.getLsbD k, w.t23.getLsbD k, w.t27.getLsbD k, w.t3.getLsbD k, w.t4.getLsbD k, w.t6.getLsbD k, w.t8.getLsbD k, w.t9.getLsbD k⟩

@[ext] private structure InvSubBytesB4 where
  m39 : Bool
  m40 : Bool
  m48 : Bool
  m50 : Bool
  m51 : Bool
  m57 : Bool
  m63 : Bool
  p0 : Bool
  p15 : Bool
  p16 : Bool
  p17 : Bool
  p2 : Bool
  p22 : Bool
  p23 : Bool
  p6 : Bool
  p7 : Bool
  s0 : Bool
  s6 : Bool
  t13 : Bool
  t23 : Bool
  t6 : Bool
  t8 : Bool
  deriving DecidableEq, Repr

private def extractInvSubBytesW4 (w : InvSubBytesW4) (k : Nat) : InvSubBytesB4 :=
  ⟨w.m39.getLsbD k, w.m40.getLsbD k, w.m48.getLsbD k, w.m50.getLsbD k, w.m51.getLsbD k, w.m57.getLsbD k, w.m63.getLsbD k, w.p0.getLsbD k, w.p15.getLsbD k, w.p16.getLsbD k, w.p17.getLsbD k, w.p2.getLsbD k, w.p22.getLsbD k, w.p23.getLsbD k, w.p6.getLsbD k, w.p7.getLsbD k, w.s0.getLsbD k, w.s6.getLsbD k, w.t13.getLsbD k, w.t23.getLsbD k, w.t6.getLsbD k, w.t8.getLsbD k⟩

@[ext] private structure InvSubBytesB5 where
  p11 : Bool
  p17 : Bool
  p25 : Bool
  s0 : Bool
  s1 : Bool
  s3 : Bool
  s4 : Bool
  s5 : Bool
  s6 : Bool
  s7 : Bool
  deriving DecidableEq, Repr

private def extractInvSubBytesW5 (w : InvSubBytesW5) (k : Nat) : InvSubBytesB5 :=
  ⟨w.p11.getLsbD k, w.p17.getLsbD k, w.p25.getLsbD k, w.s0.getLsbD k, w.s1.getLsbD k, w.s3.getLsbD k, w.s4.getLsbD k, w.s5.getLsbD k, w.s6.getLsbD k, w.s7.getLsbD k⟩

private def invSubBytesBoolStage1 (inp : FsBool8) : InvSubBytesB1 :=
  strictBool inp.b0 fun u7 =>
  strictBool inp.b1 fun u6 =>
  strictBool inp.b2 fun u5 =>
  strictBool inp.b3 fun u4 =>
  strictBool inp.b4 fun u3 =>
  strictBool inp.b5 fun u2 =>
  strictBool inp.b6 fun u1 =>
  strictBool inp.b7 fun u0 =>
  strictBool (u0 ^^ u3) fun t23 =>
  strictBool (u1 ^^ t23) fun t8 =>
  strictBool (t23 && t8) fun m2 =>
  strictBool (u4 ^^ t8) fun t4 =>
  strictBool (u1 ^^ u3) fun t22 =>
  strictBool (u0 ^^ u1) fun t2 =>
  strictBool (u3 ^^ u4) fun t1 =>
  strictBool (u7 ^^ t1) fun t9 =>
  strictBool (t22 && t9) fun m7 =>
  strictBool (u4 ^^ u7) fun t24 =>
  strictBool (t2 ^^ t24) fun t10 =>
  strictBool (t2 && t10) fun m14 =>
  strictBool (u6 ^^ u7) fun r5 =>
  strictBool (t1 ^^ r5) fun t3 =>
  strictBool (t2 ^^ r5) fun t13 =>
  strictBool (t22 ^^ r5) fun t19 =>
  strictBool (u2 ^^ t19) fun t17 =>
  strictBool (u2 ^^ t1) fun t25 =>
  strictBool (u1 ^^ u6) fun r13 =>
  strictBool (t24 ^^ r13) fun t20 =>
  strictBool (t20 && t17) fun m9 =>
  strictBool (u2 ^^ u5) fun r17 =>
  strictBool (t22 ^^ r17) fun t6 =>
  strictBool (t13 && t6) fun m1 =>
  strictBool (u0 ^^ r17) fun y5 =>
  ⟨m1, m14, m2, m7, m9, r13, t1, t10, t13, t17, t19, t2, t20, t22, t23, t24, t25, t3, t4, t6, t8, t9, u2, u4, u5, u6, y5⟩

private theorem extract_invSubBytesFsStage1 (inp : FsState) (k : Nat) :
    extractInvSubBytesW1 (invSubBytesFsStage1 inp) k = invSubBytesBoolStage1 (extractBool8 inp k) := by
  ext1 <;> simp only [extractInvSubBytesW1, invSubBytesFsStage1, invSubBytesBoolStage1, extractBool8, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def invSubBytesBoolStage2 (inp : InvSubBytesB1) : InvSubBytesB2 :=
  strictBool inp.m1 fun m1 =>
  strictBool inp.m14 fun m14 =>
  strictBool inp.m2 fun m2 =>
  strictBool inp.m7 fun m7 =>
  strictBool inp.m9 fun m9 =>
  strictBool inp.r13 fun r13 =>
  strictBool inp.t1 fun t1 =>
  strictBool inp.t10 fun t10 =>
  strictBool inp.t13 fun t13 =>
  strictBool inp.t17 fun t17 =>
  strictBool inp.t19 fun t19 =>
  strictBool inp.t2 fun t2 =>
  strictBool inp.t20 fun t20 =>
  strictBool inp.t22 fun t22 =>
  strictBool inp.t23 fun t23 =>
  strictBool inp.t24 fun t24 =>
  strictBool inp.t25 fun t25 =>
  strictBool inp.t3 fun t3 =>
  strictBool inp.t4 fun t4 =>
  strictBool inp.t6 fun t6 =>
  strictBool inp.t8 fun t8 =>
  strictBool inp.t9 fun t9 =>
  strictBool inp.u2 fun u2 =>
  strictBool inp.u4 fun u4 =>
  strictBool inp.u5 fun u5 =>
  strictBool inp.u6 fun u6 =>
  strictBool inp.y5 fun y5 =>
  strictBool (t19 && y5) fun m4 =>
  strictBool (m4 ^^ m1) fun m5 =>
  strictBool (m5 ^^ t24) fun m17 =>
  strictBool (u5 ^^ u6) fun r18 =>
  strictBool (t1 ^^ r18) fun t27 =>
  strictBool (t10 ^^ t27) fun t15 =>
  strictBool (t1 && t15) fun m11 =>
  strictBool (m14 ^^ m11) fun m15 =>
  strictBool (m17 ^^ m15) fun m21 =>
  strictBool (t4 && t27) fun m12 =>
  strictBool (m12 ^^ m11) fun m13 =>
  strictBool (t10 ^^ r18) fun t14 =>
  strictBool (t14 ^^ m1) fun m3 =>
  strictBool (m3 ^^ m2) fun m16 =>
  strictBool (m16 ^^ m13) fun m20 =>
  strictBool (u2 ^^ u4) fun r19 =>
  strictBool (r13 ^^ r19) fun t16 =>
  strictBool (t3 ^^ t16) fun t26 =>
  strictBool (t3 && t16) fun m6 =>
  strictBool (t26 ^^ m6) fun m8 =>
  strictBool (m8 ^^ m7) fun m18 =>
  strictBool (m18 ^^ m13) fun m22 =>
  strictBool (m22 && m20) fun m25 =>
  strictBool (m21 ^^ m25) fun m26 =>
  strictBool (m9 ^^ m6) fun m10 =>
  ⟨m10, m15, m20, m21, m22, m25, m26, t1, t10, t13, t15, t16, t17, t19, t2, t20, t22, t23, t25, t27, t3, t4, t6, t8, t9, y5⟩

private theorem extract_invSubBytesFsStage2 (inp : InvSubBytesW1) (k : Nat) :
    extractInvSubBytesW2 (invSubBytesFsStage2 inp) k = invSubBytesBoolStage2 (extractInvSubBytesW1 inp k) := by
  ext1 <;> simp only [extractInvSubBytesW2, invSubBytesFsStage2, invSubBytesBoolStage2, extractInvSubBytesW1, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def invSubBytesBoolStage3 (inp : InvSubBytesB2) : InvSubBytesB3 :=
  strictBool inp.m10 fun m10 =>
  strictBool inp.m15 fun m15 =>
  strictBool inp.m20 fun m20 =>
  strictBool inp.m21 fun m21 =>
  strictBool inp.m22 fun m22 =>
  strictBool inp.m25 fun m25 =>
  strictBool inp.m26 fun m26 =>
  strictBool inp.t1 fun t1 =>
  strictBool inp.t10 fun t10 =>
  strictBool inp.t13 fun t13 =>
  strictBool inp.t15 fun t15 =>
  strictBool inp.t16 fun t16 =>
  strictBool inp.t17 fun t17 =>
  strictBool inp.t19 fun t19 =>
  strictBool inp.t2 fun t2 =>
  strictBool inp.t20 fun t20 =>
  strictBool inp.t22 fun t22 =>
  strictBool inp.t23 fun t23 =>
  strictBool inp.t25 fun t25 =>
  strictBool inp.t27 fun t27 =>
  strictBool inp.t3 fun t3 =>
  strictBool inp.t4 fun t4 =>
  strictBool inp.t6 fun t6 =>
  strictBool inp.t8 fun t8 =>
  strictBool inp.t9 fun t9 =>
  strictBool inp.y5 fun y5 =>
  strictBool (m10 ^^ m15) fun m19 =>
  strictBool (m19 ^^ t25) fun m23 =>
  strictBool (m23 ^^ m25) fun m28 =>
  strictBool (m22 ^^ m23) fun m24 =>
  strictBool (m26 && m24) fun m30 =>
  strictBool (m23 ^^ m30) fun m39 =>
  strictBool (m39 && y5) fun m48 =>
  strictBool (m39 && t19) fun m57 =>
  strictBool (m24 ^^ m25) fun m36 =>
  strictBool (m20 && m23) fun m31 =>
  strictBool (m20 ^^ m21) fun m27 =>
  strictBool (m27 && m31) fun m32 =>
  strictBool (m28 && m27) fun m29 =>
  strictBool (m21 ^^ m29) fun m37 =>
  strictBool (m37 ^^ m39) fun m42 =>
  strictBool (m42 && t15) fun m52 =>
  strictBool (m42 && t1) fun m61 =>
  strictBool (m52 ^^ m61) fun p0 =>
  strictBool (m57 ^^ m61) fun p16 =>
  strictBool (m37 && t20) fun m60 =>
  strictBool (m37 && t17) fun m51 =>
  strictBool (m27 ^^ m25) fun m33 =>
  strictBool (m32 ^^ m33) fun m38 =>
  strictBool (m37 ^^ m38) fun m43 =>
  strictBool (m43 && t16) fun m49 =>
  ⟨m21, m22, m24, m36, m38, m39, m42, m43, m48, m49, m51, m57, m60, p0, p16, t10, t13, t2, t22, t23, t27, t3, t4, t6, t8, t9⟩

private theorem extract_invSubBytesFsStage3 (inp : InvSubBytesW2) (k : Nat) :
    extractInvSubBytesW3 (invSubBytesFsStage3 inp) k = invSubBytesBoolStage3 (extractInvSubBytesW2 inp k) := by
  ext1 <;> simp only [extractInvSubBytesW3, invSubBytesFsStage3, invSubBytesBoolStage3, extractInvSubBytesW2, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def invSubBytesBoolStage4 (inp : InvSubBytesB3) : InvSubBytesB4 :=
  strictBool inp.m21 fun m21 =>
  strictBool inp.m22 fun m22 =>
  strictBool inp.m24 fun m24 =>
  strictBool inp.m36 fun m36 =>
  strictBool inp.m38 fun m38 =>
  strictBool inp.m39 fun m39 =>
  strictBool inp.m42 fun m42 =>
  strictBool inp.m43 fun m43 =>
  strictBool inp.m48 fun m48 =>
  strictBool inp.m49 fun m49 =>
  strictBool inp.m51 fun m51 =>
  strictBool inp.m57 fun m57 =>
  strictBool inp.m60 fun m60 =>
  strictBool inp.p0 fun p0 =>
  strictBool inp.p16 fun p16 =>
  strictBool inp.t10 fun t10 =>
  strictBool inp.t13 fun t13 =>
  strictBool inp.t2 fun t2 =>
  strictBool inp.t22 fun t22 =>
  strictBool inp.t23 fun t23 =>
  strictBool inp.t27 fun t27 =>
  strictBool inp.t3 fun t3 =>
  strictBool inp.t4 fun t4 =>
  strictBool inp.t6 fun t6 =>
  strictBool inp.t8 fun t8 =>
  strictBool inp.t9 fun t9 =>
  strictBool (m49 ^^ m60) fun p6 =>
  strictBool (m49 ^^ m51) fun p13 =>
  strictBool (m43 && t3) fun m58 =>
  strictBool (m38 && t9) fun m50 =>
  strictBool (m38 && t22) fun m59 =>
  strictBool (m58 ^^ m59) fun p1 =>
  strictBool (p0 ^^ p1) fun p7 =>
  strictBool (m21 && m22) fun m34 =>
  strictBool (m24 && m34) fun m35 =>
  strictBool (m35 ^^ m36) fun m40 =>
  strictBool (m38 ^^ m40) fun m41 =>
  strictBool (m42 ^^ m41) fun m45 =>
  strictBool (m45 && t27) fun m53 =>
  strictBool (m50 ^^ m53) fun p8 =>
  strictBool (p7 ^^ p8) fun p23 =>
  strictBool (m45 && t4) fun m62 =>
  strictBool (m49 ^^ m62) fun p14 =>
  strictBool (p14 ^^ p23) fun s6 =>
  strictBool (m41 && t10) fun m54 =>
  strictBool (m54 ^^ m62) fun p2 =>
  strictBool (p2 ^^ p7) fun p22 =>
  strictBool (p13 ^^ p22) fun s0 =>
  strictBool (m58 ^^ p2) fun p17 =>
  strictBool (m54 ^^ m59) fun p15 =>
  strictBool (m41 && t2) fun m63 =>
  ⟨m39, m40, m48, m50, m51, m57, m63, p0, p15, p16, p17, p2, p22, p23, p6, p7, s0, s6, t13, t23, t6, t8⟩

private theorem extract_invSubBytesFsStage4 (inp : InvSubBytesW3) (k : Nat) :
    extractInvSubBytesW4 (invSubBytesFsStage4 inp) k = invSubBytesBoolStage4 (extractInvSubBytesW3 inp k) := by
  ext1 <;> simp only [extractInvSubBytesW4, invSubBytesFsStage4, invSubBytesBoolStage4, extractInvSubBytesW3, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def invSubBytesBoolStage5 (inp : InvSubBytesB4) : InvSubBytesB5 :=
  strictBool inp.m39 fun m39 =>
  strictBool inp.m40 fun m40 =>
  strictBool inp.m48 fun m48 =>
  strictBool inp.m50 fun m50 =>
  strictBool inp.m51 fun m51 =>
  strictBool inp.m57 fun m57 =>
  strictBool inp.m63 fun m63 =>
  strictBool inp.p0 fun p0 =>
  strictBool inp.p15 fun p15 =>
  strictBool inp.p16 fun p16 =>
  strictBool inp.p17 fun p17 =>
  strictBool inp.p2 fun p2 =>
  strictBool inp.p22 fun p22 =>
  strictBool inp.p23 fun p23 =>
  strictBool inp.p6 fun p6 =>
  strictBool inp.p7 fun p7 =>
  strictBool inp.s0 fun s0 =>
  strictBool inp.s6 fun s6 =>
  strictBool inp.t13 fun t13 =>
  strictBool inp.t23 fun t23 =>
  strictBool inp.t6 fun t6 =>
  strictBool inp.t8 fun t8 =>
  strictBool (m39 ^^ m40) fun m44 =>
  strictBool (m44 && t6) fun m46 =>
  strictBool (m46 ^^ m51) fun p5 =>
  strictBool (m63 ^^ p5) fun p18 =>
  strictBool (p5 ^^ p7) fun p24 =>
  strictBool (m46 ^^ m48) fun p12 =>
  strictBool (p12 ^^ p22) fun s3 =>
  strictBool (m44 && t13) fun m55 =>
  strictBool (m55 ^^ m63) fun p9 =>
  strictBool (p9 ^^ p16) fun s7 =>
  strictBool (m40 && t8) fun m47 =>
  strictBool (m47 ^^ m50) fun p3 =>
  strictBool (p2 ^^ p3) fun p19 =>
  strictBool (p19 ^^ p24) fun s5 =>
  strictBool (p0 ^^ p3) fun p11 =>
  strictBool (p9 ^^ p11) fun p26 =>
  strictBool (m40 && t23) fun m56 =>
  strictBool (m48 ^^ m56) fun p4 =>
  strictBool (p4 ^^ p6) fun p20 =>
  strictBool (p15 ^^ p20) fun p29 =>
  strictBool (p26 ^^ p29) fun s1 =>
  strictBool (m57 ^^ p4) fun p10 =>
  strictBool (p10 ^^ p18) fun p27 =>
  strictBool (p23 ^^ p27) fun s4 =>
  strictBool (p6 ^^ p10) fun p25 =>
  ⟨p11, p17, p25, s0, s1, s3, s4, s5, s6, s7⟩

private theorem extract_invSubBytesFsStage5 (inp : InvSubBytesW4) (k : Nat) :
    extractInvSubBytesW5 (invSubBytesFsStage5 inp) k = invSubBytesBoolStage5 (extractInvSubBytesW4 inp k) := by
  ext1 <;> simp only [extractInvSubBytesW5, invSubBytesFsStage5, invSubBytesBoolStage5, extractInvSubBytesW4, strictBool_eq,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]

private def invSubBytesBoolStage6 (inp : InvSubBytesB5) : FsBool8 :=
  strictBool inp.p11 fun p11 =>
  strictBool inp.p17 fun p17 =>
  strictBool inp.p25 fun p25 =>
  strictBool inp.s0 fun s0 =>
  strictBool inp.s1 fun s1 =>
  strictBool inp.s3 fun s3 =>
  strictBool inp.s4 fun s4 =>
  strictBool inp.s5 fun s5 =>
  strictBool inp.s6 fun s6 =>
  strictBool inp.s7 fun s7 =>
  strictBool (p11 ^^ p25) fun p28 =>
  strictBool (p17 ^^ p28) fun s2 =>
  ⟨s7, s6, s5, s4, s3, s2, s1, s0⟩

private theorem extract_invSubBytesFsStage6 (inp : InvSubBytesW5) (k : Nat) :
    extractBool8 (invSubBytesFsStage6 inp) k = invSubBytesBoolStage6 (extractInvSubBytesW5 inp k) := by
  ext1 <;> simp only [extractBool8, invSubBytesFsStage6, invSubBytesBoolStage6, extractInvSubBytesW5, strictBool_eq,
    BitVec.getLsbD_xor]

private def invSubBytesBool (st : FsBool8) : FsBool8 :=
  invSubBytesBoolStage6 (invSubBytesBoolStage5 (invSubBytesBoolStage4 (invSubBytesBoolStage3 (invSubBytesBoolStage2 (invSubBytesBoolStage1 st)))))

private theorem extract_invSubBytesFs (st : FsState) (k : Nat) :
    extractBool8 (invSubBytesFs st) k = invSubBytesBool (extractBool8 st k) := by
  unfold invSubBytesFs invSubBytesBool
  rw [extract_invSubBytesFsStage6, extract_invSubBytesFsStage5, extract_invSubBytesFsStage4, extract_invSubBytesFsStage3, extract_invSubBytesFsStage2, extract_invSubBytesFsStage1]

/-! ## Exhaustive 256-Input Scalar Verification (`by decide`) and 4-Lane Lifting -/

private theorem subBytesBool_eq_sbox :
    ∀ b : BitVec 8, notsBool8 (subBytesBool (byteToBool8 b)) = byteToBool8 (sbox b) := by
  decide

private theorem invSubBytesBool_eq_invSbox :
    ∀ b : BitVec 8, invSubBytesBool (notsBool8 (byteToBool8 b)) = byteToBool8 (invSbox b) := by
  decide

private theorem extractBool8_bitslice (bs : Blocks4) (r c lane : Nat)
    (hr : r < 4) (hc : c < 4) (hl : lane < 4) :
    extractBool8 (bitslice bs) (16 * r + 4 * c + lane) =
      byteToBool8 ((bs.getLane lane).getD (r + 4 * c) 0#8) := by
  ext1
  · exact getLsbD_bitslice bs 0 r c lane (by omega) hr hc hl
  · exact getLsbD_bitslice bs 1 r c lane (by omega) hr hc hl
  · exact getLsbD_bitslice bs 2 r c lane (by omega) hr hc hl
  · exact getLsbD_bitslice bs 3 r c lane (by omega) hr hc hl
  · exact getLsbD_bitslice bs 4 r c lane (by omega) hr hc hl
  · exact getLsbD_bitslice bs 5 r c lane (by omega) hr hc hl
  · exact getLsbD_bitslice bs 6 r c lane (by omega) hr hc hl
  · exact getLsbD_bitslice bs 7 r c lane (by omega) hr hc hl

private theorem getD_subBytes {s : State} (hs : s.length = 16) (j : Nat) (hj : j < 16) :
    (subBytes s).getD j 0#8 = sbox (s.getD j 0#8) := by
  have hj1 : j < s.length := by omega
  have hj2 : j < (subBytes s).length := by simp [subBytes, hs]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1]
  simp [subBytes]

private theorem getD_invSubBytes {s : State} (hs : s.length = 16) (j : Nat) (hj : j < 16) :
    (invSubBytes s).getD j 0#8 = invSbox (s.getD j 0#8) := by
  have hj1 : j < s.length := by omega
  have hj2 : j < (invSubBytes s).length := by simp [invSubBytes, hs]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1]
  simp [invSubBytes]

/-- `sub_bytes` followed by `sub_bytes_nots` equals 4-lane FIPS 197 `subBytes`. -/
theorem subBytesNots_subBytesFs_bitslice {bs : Blocks4} (hwf : Packing.Blocks4.Wf bs) :
    subBytesNots (subBytesFs (bitslice bs)) = bitslice (bs.map subBytes) := by
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  have hlane_len : (bs.getLane lane).length = 16 := by
    match lane, hl with
    | 0, _ => exact hwf.1
    | 1, _ => exact hwf.2.1
    | 2, _ => exact hwf.2.2.1
    | 3, _ => exact hwf.2.2.2
    | _ + 4, hl => omega
  have hmap_lane : (bs.map subBytes).getLane lane = subBytes (bs.getLane lane) := by
    match lane, hl with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
    | _ + 4, hl => omega
  rw [← getBit_extractBool8 _ _ p hp, extract_subBytesNots _ _ (by omega),
    extract_subBytesFs, extractBool8_bitslice bs r c lane hr hc hl,
    subBytesBool_eq_sbox, getBit_byteToBool8 _ p hp, hmap_lane,
    getD_subBytes hlane_len (r + 4 * c) (by omega)]

/-- `inv_sub_bytes` after `sub_bytes_nots` equals 4-lane FIPS 197 `invSubBytes`. -/
theorem invSubBytesFs_subBytesNots_bitslice {bs : Blocks4} (hwf : Packing.Blocks4.Wf bs) :
    invSubBytesFs (subBytesNots (bitslice bs)) = bitslice (bs.map invSubBytes) := by
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  have hlane_len : (bs.getLane lane).length = 16 := by
    match lane, hl with
    | 0, _ => exact hwf.1
    | 1, _ => exact hwf.2.1
    | 2, _ => exact hwf.2.2.1
    | 3, _ => exact hwf.2.2.2
    | _ + 4, hl => omega
  have hmap_lane : (bs.map invSubBytes).getLane lane = invSubBytes (bs.getLane lane) := by
    match lane, hl with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
    | _ + 4, hl => omega
  rw [← getBit_extractBool8 _ _ p hp, extract_invSubBytesFs,
    extract_subBytesNots _ _ (by omega), extractBool8_bitslice bs r c lane hr hc hl,
    invSubBytesBool_eq_invSbox, getBit_byteToBool8 _ p hp, hmap_lane,
    getD_invSubBytes hlane_len (r + 4 * c) (by omega)]

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.SboxEquiv
