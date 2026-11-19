/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import

/-!
# `encapsulate2` (`B20`) — Indexed & Flat 128-Bit Vector Array Memory (`VecMem`)

1. `Vec128At` and `VecRangeMem` (`PolyMem`, `SpillMem`, `PolyOctMem`) + `↦ₛ` bijection.
2. `SepLoad128` / `SepStore128` witnesses and `step_ldrQ128` / `step_strQ128` / `step_ldpQ128` / `step_stpQ128`.
3. Flat `O(1)` structures `Vec32`, `Spill13`, and `Oct8` eliminating `Function.update` nesting
   across straight-line `inv_ntt` and polynomial copy segments.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16
  bytesToPoly16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  PolyVec128
  getLsbD_readLE
  pack8x16
  polyVec128_bytesToPoly16
)

/-! ## 1. Indexed 128-Bit Vector Array Memory (`VecRangeMem`, `PolyMem`, `SpillMem`, `PolyOctMem`) -/

/-- Single 128-bit little-endian vector cell at `ptr`. -/
@[expose] def Vec128At (ptr : BitVec 64) (v : BitVec 128) : SepProp :=
  (ptr ↦₆₄ v.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v.extractLsb' 64 64)

/-- `n` contiguous 128-bit vector cells starting at `ptr` (`16 * n` bytes). -/
@[expose] def VecRangeMem : Nat → BitVec 64 → (Nat → BitVec 128) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, f => Vec128At ptr (f 0) ∗ VecRangeMem n (ptr + 16#64) (fun i => f (i + 1))

@[expose] def PolyMem (ptr : BitVec 64) (f : Nat → BitVec 128) : SepProp := VecRangeMem 32 ptr f
@[expose] def SpillMem (ptr : BitVec 64) (f : Nat → BitVec 128) : SepProp := VecRangeMem 13 ptr f
@[expose] def PolyOctMem (ptr : BitVec 64) (f : Nat → BitVec 128) : SepProp := VecRangeMem 8 ptr f

/-- `Nat`-indexed 128-bit vector view of a `Poly16` (`k ∈ 0..32`). -/
@[expose] def polyVecNat (p : Poly16) (k : Nat) : BitVec 128 :=
  pack8x16 fun lane => p.getD (8 * k + lane.val) 0#16

theorem polyVecNat_eq_polyVec128 (p : Poly16) (k : Nat) (hk : k < 32) :
    polyVecNat p k = PolyVec128 p ⟨k, hk⟩ := rfl

theorem vecRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < n → f i = g i) :
    VecRangeMem n ptr f = VecRangeMem n ptr g := by
  induction n generalizing ptr f g with
  | zero => rfl
  | succ n ih =>
    simp only [VecRangeMem, h 0 (Nat.zero_lt_succ n),
      ih (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

theorem append_extractLsb64 (v : BitVec 128) :
    v.extractLsb' 64 64 ++ v.extractLsb' 0 64 = v := by
  bv_bits

/-- Unpack a 128-bit vector into 16 little-endian bytes. -/
@[expose] def unpack128 (v : BitVec 128) : List (BitVec 8) :=
  unpack64 (v.extractLsb' 0 64) ++ unpack64 (v.extractLsb' 64 64)

@[simp] theorem unpack128_length (v : BitVec 128) : (unpack128 v).length = 16 := rfl

theorem vec128At_eq_pointsToBytes (ptr : BitVec 64) (v : BitVec 128) :
    Vec128At ptr v = (ptr ↦ₛ unpack128 v) := by
  unfold Vec128At unpack128
  rw [pointsToBytes_append, unpack64_length, pointsTo64_eq_pointsToBytes,
    pointsTo64_eq_pointsToBytes]

/-- Serialize `n` 128-bit vectors into `16 * n` little-endian bytes. -/
@[expose] def vecRangeBytes : Nat → (Nat → BitVec 128) → List (BitVec 8)
  | 0, _ => []
  | n + 1, f => unpack128 (f 0) ++ vecRangeBytes n (fun i => f (i + 1))

@[simp] theorem vecRangeBytes_length (n : Nat) (f : Nat → BitVec 128) :
    (vecRangeBytes n f).length = 16 * n := by
  induction n generalizing f with
  | zero => simp [vecRangeBytes]
  | succ n ih =>
    simp only [vecRangeBytes, List.length_append, unpack128_length, ih]
    omega

theorem vecRangeMem_eq_pointsToBytes (n : Nat) (ptr : BitVec 64) (f : Nat → BitVec 128) :
    VecRangeMem n ptr f = (ptr ↦ₛ vecRangeBytes n f) := by
  induction n generalizing ptr f with
  | zero =>
    simp [VecRangeMem, vecRangeBytes, pointsToBytes_nil]
  | succ n ih =>
    simp only [VecRangeMem, vecRangeBytes, vec128At_eq_pointsToBytes, ih,
      pointsToBytes_append, unpack128_length]

theorem vecRangeMem_entails_memRegion (n : Nat) (ptr : BitVec 64) (f : Nat → BitVec 128) :
    VecRangeMem n ptr f ⊢ memRegion ptr (16 * n) := by
  rw [vecRangeMem_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion ptr (vecRangeBytes n f)
  rwa [vecRangeBytes_length] at h

/-- Decode the `k`-th 128-bit little-endian vector of a byte list `bs`. -/
@[expose] def bytesToVecNat (bs : List (BitVec 8)) (k : Nat) : BitVec 128 :=
  ByteSlice.readLE bs (16 * k + 8) 8 ++ ByteSlice.readLE bs (16 * k) 8

private theorem unpack64_readLE_zero {bs : List (BitVec 8)} (h : bs.length = 8) :
    unpack64 (ByteSlice.readLE bs 0 8) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try solve | cases h
  rw [← ByteSlice.pack64_eq_readLE_8]
  exact unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7

private theorem extractLsb_lo_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_bits

private theorem extractLsb_hi_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_bits

private theorem readLE_drop (bs : List (BitVec 8)) (d off m : Nat) :
    ByteSlice.readLE (bs.drop d) off m = ByteSlice.readLE bs (d + off) m := by
  induction m generalizing off with
  | zero => simp [ByteSlice.readLE_zero]
  | succ m ih =>
    simp only [ByteSlice.readLE_succ, ih, List.getD_eq_getElem?_getD, List.getElem?_drop]
    have hidx : d + (off + m) = d + off + m := by omega
    rw [hidx]

private theorem readLE_take_8 {bs : List (BitVec 8)} (_h : 8 ≤ bs.length) :
    ByteSlice.readLE (bs.take 8) 0 8 = ByteSlice.readLE bs 0 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [getLsbD_readLE (bs.take 8) 0 8 b hb, getLsbD_readLE bs 0 8 b hb]
  by_cases h64 : b < 8 * 8
  · have hlt : b / 8 < 8 := by omega
    simp [h64, List.getD_eq_getElem?_getD, hlt]
  · simp [h64]

theorem vecRangeBytes_bytesToVecNat :
    ∀ (n : Nat) {bs : List (BitVec 8)}, bs.length = 16 * n →
      vecRangeBytes n (bytesToVecNat bs) = bs
  | 0, bs, h => by simp at h; exact h.symm
  | n + 1, bs, h => by
    have hlo_len : (bs.take 8).length = 8 := by simp [List.length_take_of_le (by omega : 8 ≤ bs.length)]
    have hhi_len : ((bs.drop 8).take 8).length = 8 := by
      simp [List.length_take_of_le (by simp; omega : 8 ≤ (bs.drop 8).length)]
    have hu0 : unpack128 (bytesToVecNat bs 0) = bs.take 16 := by
      unfold unpack128 bytesToVecNat
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [extractLsb_lo_append64, extractLsb_hi_append64]
      have hlo : unpack64 (ByteSlice.readLE bs 0 8) = bs.take 8 := by
        rw [← readLE_take_8 (by omega), unpack64_readLE_zero hlo_len]
      have hhi : unpack64 (ByteSlice.readLE bs 8 8) = (bs.drop 8).take 8 := by
        have hrd : ByteSlice.readLE bs 8 8 = ByteSlice.readLE ((bs.drop 8).take 8) 0 8 := by
          rw [readLE_take_8 (by simp; omega), readLE_drop, Nat.add_zero]
        rw [hrd, unpack64_readLE_zero hhi_len]
      rw [hlo, hhi]
      have htake16 : bs.take 16 = bs.take 8 ++ (bs.drop 8).take 8 := by
        rw [show (16 : Nat) = 8 + 8 from rfl, List.take_add]
      exact htake16.symm
    have htail : (fun i => bytesToVecNat bs (i + 1)) = bytesToVecNat (bs.drop 16) := by
      funext i
      unfold bytesToVecNat
      rw [readLE_drop, readLE_drop]
      have e1 : 16 + (16 * i + 8) = 16 * (i + 1) + 8 := by omega
      have e2 : 16 + 16 * i = 16 * (i + 1) := by omega
      rw [e1, e2]
    simp only [vecRangeBytes, hu0, htail,
      vecRangeBytes_bytesToVecNat n (bs := bs.drop 16) (by simp; omega),
      List.take_append_drop]

theorem pointsToBytes_eq_vecRangeMem (n : Nat) (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 16 * n) :
    (ptr ↦ₛ bs) = VecRangeMem n ptr (bytesToVecNat bs) := by
  rw [vecRangeMem_eq_pointsToBytes, vecRangeBytes_bytesToVecNat n h]

theorem polyMem_bytesToPoly16 (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 512) :
    (ptr ↦ₛ bs) = PolyMem ptr (polyVecNat (bytesToPoly16 bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 32 ptr h]
  exact vecRangeMem_congr fun i hi => by
    rw [polyVecNat_eq_polyVec128 _ i hi, polyVec128_bytesToPoly16]
    rfl

theorem SepWP.of_memRegion_vecRangeMem {prog : Program} {target_pc : BitVec 64}
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (n : Nat) (ptr : BitVec 64) (hn : 16 * n ≤ 2 ^ 64 := by decide)
    (hf : Full = memRegion ptr (16 * n) ∗ F := by sep_focus)
    (h : ∀ f : Nat → BitVec 128, SepWP prog target_pc s (VecRangeMem n ptr f ∗ F) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, memRegion_eq_exists_bytes ptr (16 * n) hn]
  apply SepWP.of_sepExists_left
  intro bs
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  intro hlen
  rw [pointsToBytes_eq_vecRangeMem n ptr hlen]
  exact h (bytesToVecNat bs)

/-! ## 2. 128-Bit `SepLoad128` / `SepStore128` Witnesses & `SepWP` Step Lemmas -/

structure SepLoad128 (ea : BitVec 64) (P : SepProp) (v : BitVec 128) : Prop where
  lo : SepLoad64 ea P (v.extractLsb' 0 64)
  hi : SepLoad64 (ea + 8#64) P (v.extractLsb' 64 64)

structure SepStore128 (ea : BitVec 64) (val : BitVec 128) (P P' : SepProp) : Prop where
  lo : ∃ Pm, SepStore64 ea (val.extractLsb' 0 64) P Pm ∧
    SepStore64 (ea + 8#64) (val.extractLsb' 64 64) Pm P'

theorem SepLoad128.left {ea : BitVec 64} {v : BitVec 128} {L R : SepProp}
    (h : SepLoad128 ea L v) : SepLoad128 ea (L ∗ R) v :=
  ⟨h.lo.left, h.hi.left⟩

theorem SepLoad128.right {ea : BitVec 64} {v : BitVec 128} {L R : SepProp}
    (h : SepLoad128 ea R v) : SepLoad128 ea (L ∗ R) v :=
  ⟨h.lo.right, h.hi.right⟩

theorem SepStore128.left {ea : BitVec 64} {val : BitVec 128} {L L' R : SepProp}
    (h : SepStore128 ea val L L') : SepStore128 ea val (L ∗ R) (L' ∗ R) := by
  rcases h.lo with ⟨Pm, h1, h2⟩
  exact ⟨Pm ∗ R, h1.left, h2.left⟩

theorem SepStore128.right {ea : BitVec 64} {val : BitVec 128} {L R R' : SepProp}
    (h : SepStore128 ea val R R') : SepStore128 ea val (L ∗ R) (L ∗ R') := by
  rcases h.lo with ⟨Pm, h1, h2⟩
  exact ⟨L ∗ Pm, h1.right, h2.right⟩

theorem SepLoad128.vec128At {ea ptr : BitVec 64} {v : BitVec 128} (ha : ptr = ea) :
    SepLoad128 ea (Vec128At ptr v) v := by
  subst ha
  exact ⟨(SepLoad64.here rfl).left, (SepLoad64.here rfl).right⟩

theorem SepStore128.vec128At {ea ptr : BitVec 64} {v val : BitVec 128} (ha : ptr = ea) :
    SepStore128 ea val (Vec128At ptr v) (Vec128At ptr val) := by
  subst ha
  exact ⟨(ptr ↦₆₄ val.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v.extractLsb' 64 64),
    (SepStore64.here rfl).left, (SepStore64.here rfl).right⟩

theorem SepLoad128.vecRange {n k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    (hk : k < n) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepLoad128 ea (VecRangeMem n ptr f) (f k) := by
  induction n generalizing k ptr f with
  | zero => omega
  | succ n ih =>
    rcases k with _ | k
    · simp only [Nat.mul_zero, BitVec.add_zero] at ha
      exact (SepLoad128.vec128At ha).left
    · have ha' : (ptr + 16#64) + BitVec.ofNat 64 (16 * k) = ea := by
        rw [← ha, BitVec.add_assoc]
        congr 1
        have hm : 16 * (k + 1) = 16 + 16 * k := by omega
        rw [hm, BitVec.ofNat_add]
      exact (ih (by omega) ha').right

theorem SepStore128.vecRange {n k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128}
    (hk : k < n) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (VecRangeMem n ptr f) (VecRangeMem n ptr (Function.update f k val)) := by
  induction n generalizing k ptr f with
  | zero => omega
  | succ n ih =>
    rcases k with _ | k
    · simp only [Nat.mul_zero, BitVec.add_zero] at ha
      have htail : VecRangeMem n (ptr + 16#64) (fun i => Function.update f 0 val (i + 1)) =
          VecRangeMem n (ptr + 16#64) (fun i => f (i + 1)) :=
        vecRangeMem_congr fun i _ => Function.update_of_ne (Nat.succ_ne_zero i) val f
      simp only [VecRangeMem, Function.update_self, htail]
      exact (SepStore128.vec128At ha).left
    · have ha' : (ptr + 16#64) + BitVec.ofNat 64 (16 * k) = ea := by
        rw [← ha, BitVec.add_assoc]
        congr 1
        have hm : 16 * (k + 1) = 16 + 16 * k := by omega
        rw [hm, BitVec.ofNat_add]
      have hhead : Function.update f (k + 1) val 0 = f 0 :=
        Function.update_of_ne (Nat.succ_ne_zero k).symm val f
      have htail : (fun i => Function.update f (k + 1) val (i + 1)) =
          Function.update (fun i => f (i + 1)) k val := by
        funext i
        by_cases h : i = k
        · subst h; simp
        · have h1 : i + 1 ≠ k + 1 := by omega
          simp [Function.update_of_ne h, Function.update_of_ne h1]
      simp only [VecRangeMem, hhead, htail]
      exact (ih (by omega) ha').right

theorem step_ldrQ128 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 128}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad128 ea P v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldrSimd128 hpc hrun hfetch hsp haddr rfl hload.lo hload.hi
    (by rw [append_extractLsb64]; exact hexec) hnext

theorem step_strQ128 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 128}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readVReg128 vt = val)
    (hstore : SepStore128 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  rcases hstore.lo with ⟨Pm, h1, h2⟩
  exact SepWP.step_strSimd128 hpc hrun hfetch hsp haddr rfl
    (by rw [hval]) (by rw [hval]) h1 h2 hexec hnext

theorem step_ldpQ128 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea16 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 128}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .Q128 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea16 : ea + 16#64 = ea16)
    (hload1 : SepLoad128 ea P v1)
    (hload2 : SepLoad128 ea16 P v2)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 v1).writeVReg128 vt2 v2).setPC
      (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldpSimd128 hpc hrun hfetch hsp haddr rfl hea16 rfl
    hload1.lo hload1.hi hload2.lo hload2.hi
    (by rw [append_extractLsb64, append_extractLsb64]; exact hexec) hnext

theorem step_stpQ128 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea16 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 128}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea16 : ea + 16#64 = ea16)
    (hv1 : s.readVReg128 vt1 = v1)
    (hv2 : s.readVReg128 vt2 = v2)
    (hstore1 : SepStore128 ea v1 P P1)
    (hstore2 : SepStore128 ea16 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  rcases hstore1.lo with ⟨Pm1, h1, h2⟩
  rcases hstore2.lo with ⟨Pm2, h3, h4⟩
  exact SepWP.step_stpSimd128 hpc hrun hfetch hsp haddr rfl hea16 rfl
    (by rw [hv1]) (by rw [hv1]) (by rw [hv2]) (by rw [hv2]) h1 h2 h3 h4 hexec hnext

/-! ## 3. Flat `O(1)` Structures (`Vec32`, `Spill13`, `Oct8`) Eliminating `Function.update` -/

structure Vec32 where
  (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 128)
  (v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 128)
  (v16 v17 v18 v19 v20 v21 v22 v23 : BitVec 128)
  (v24 v25 v26 v27 v28 v29 v30 v31 : BitVec 128)

@[expose] def Vec32.get (t : Vec32) : Nat → BitVec 128
  | 0 => t.v0 | 1 => t.v1 | 2 => t.v2 | 3 => t.v3 | 4 => t.v4 | 5 => t.v5 | 6 => t.v6 | 7 => t.v7
  | 8 => t.v8 | 9 => t.v9 | 10 => t.v10 | 11 => t.v11 | 12 => t.v12 | 13 => t.v13 | 14 => t.v14 | 15 => t.v15
  | 16 => t.v16 | 17 => t.v17 | 18 => t.v18 | 19 => t.v19 | 20 => t.v20 | 21 => t.v21 | 22 => t.v22 | 23 => t.v23
  | 24 => t.v24 | 25 => t.v25 | 26 => t.v26 | 27 => t.v27 | 28 => t.v28 | 29 => t.v29 | 30 => t.v30 | 31 => t.v31
  | _ => 0#128

@[expose] def Vec32.set (t : Vec32) (k : Nat) (x : BitVec 128) : Vec32 :=
  match k with
  | 0 => { t with v0 := x } | 1 => { t with v1 := x } | 2 => { t with v2 := x } | 3 => { t with v3 := x }
  | 4 => { t with v4 := x } | 5 => { t with v5 := x } | 6 => { t with v6 := x } | 7 => { t with v7 := x }
  | 8 => { t with v8 := x } | 9 => { t with v9 := x } | 10 => { t with v10 := x } | 11 => { t with v11 := x }
  | 12 => { t with v12 := x } | 13 => { t with v13 := x } | 14 => { t with v14 := x } | 15 => { t with v15 := x }
  | 16 => { t with v16 := x } | 17 => { t with v17 := x } | 18 => { t with v18 := x } | 19 => { t with v19 := x }
  | 20 => { t with v20 := x } | 21 => { t with v21 := x } | 22 => { t with v22 := x } | 23 => { t with v23 := x }
  | 24 => { t with v24 := x } | 25 => { t with v25 := x } | 26 => { t with v26 := x } | 27 => { t with v27 := x }
  | 28 => { t with v28 := x } | 29 => { t with v29 := x } | 30 => { t with v30 := x } | 31 => { t with v31 := x }
  | _ => t

@[expose] def Vec32.ofFn (f : Nat → BitVec 128) : Vec32 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7,
   f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15,
   f 16, f 17, f 18, f 19, f 20, f 21, f 22, f 23,
   f 24, f 25, f 26, f 27, f 28, f 29, f 30, f 31⟩

@[expose] def Vec32.zero : Vec32 := Vec32.ofFn (fun _ => 0#128)
@[expose] def Poly32Mem (ptr : BitVec 64) (t : Vec32) : SepProp := PolyMem ptr t.get

theorem vec32_ofFn_get (f : Nat → BitVec 128) (i : Nat) (hi : i < 32) :
    (Vec32.ofFn f).get i = f i := by
  match i with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl
  | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl
  | 24 => rfl | 25 => rfl | 26 => rfl | 27 => rfl | 28 => rfl | 29 => rfl | 30 => rfl | 31 => rfl
  | _ + 32 => omega

theorem poly32Mem_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    Poly32Mem ptr (Vec32.ofFn f) = PolyMem ptr f :=
  vecRangeMem_congr fun i hi => vec32_ofFn_get f i hi

theorem poly32Mem_eq_pointsToBytes (ptr : BitVec 64) (t : Vec32) :
    Poly32Mem ptr t = (ptr ↦ₛ vecRangeBytes 32 t.get) :=
  vecRangeMem_eq_pointsToBytes 32 ptr t.get

theorem poly32Mem_entails_memRegion (ptr : BitVec 64) (t : Vec32) :
    Poly32Mem ptr t ⊢ memRegion ptr 512 :=
  vecRangeMem_entails_memRegion 32 ptr t.get

private theorem vec32_set_eq_ofFn (t : Vec32) (k : Nat) (x : BitVec 128) (hk : k < 32) :
    t.set k x = Vec32.ofFn (fun j => if j = k then x else t.get j) := by
  match k with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl
  | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl
  | 24 => rfl | 25 => rfl | 26 => rfl | 27 => rfl | 28 => rfl | 29 => rfl | 30 => rfl | 31 => rfl
  | _ + 32 => omega

theorem vec32_set_get (t : Vec32) (k : Nat) (x : BitVec 128) (hk : k < 32)
    (i : Nat) (hi : i < 32) :
    Function.update t.get k x i = (t.set k x).get i := by
  rw [vec32_set_eq_ofFn t k x hk, vec32_ofFn_get _ i hi]
  by_cases h : i = k <;> simp [h]

theorem SepLoad128.vec32 {k : Nat} {ea ptr : BitVec 64} {t : Vec32} {v : BitVec 128}
    (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (hv : t.get k = v) :
    SepLoad128 ea (Poly32Mem ptr t) v := by
  rw [← hv]; exact SepLoad128.vecRange hk ha

theorem SepStore128.vec32 {k : Nat} {ea ptr : BitVec 64} {t t' : Vec32} {val : BitVec 128}
    (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (ht : t.set k val = t') :
    SepStore128 ea val (Poly32Mem ptr t) (Poly32Mem ptr t') := by
  rw [← ht]; unfold Poly32Mem PolyMem
  rw [← vecRangeMem_congr (vec32_set_get t k val hk)]
  exact SepStore128.vecRange hk ha

structure Spill13 where
  (s0 s1 s2 s3 s4 s5 s6 s7 : BitVec 128)
  (s8 s9 s10 s11 s12 : BitVec 128)

@[expose] def Spill13.get (t : Spill13) : Nat → BitVec 128
  | 0 => t.s0 | 1 => t.s1 | 2 => t.s2 | 3 => t.s3 | 4 => t.s4 | 5 => t.s5 | 6 => t.s6 | 7 => t.s7
  | 8 => t.s8 | 9 => t.s9 | 10 => t.s10 | 11 => t.s11 | 12 => t.s12
  | _ => 0#128

@[expose] def Spill13.set (t : Spill13) (k : Nat) (x : BitVec 128) : Spill13 :=
  match k with
  | 0 => { t with s0 := x } | 1 => { t with s1 := x } | 2 => { t with s2 := x } | 3 => { t with s3 := x }
  | 4 => { t with s4 := x } | 5 => { t with s5 := x } | 6 => { t with s6 := x } | 7 => { t with s7 := x }
  | 8 => { t with s8 := x } | 9 => { t with s9 := x } | 10 => { t with s10 := x } | 11 => { t with s11 := x }
  | 12 => { t with s12 := x }
  | _ => t

@[expose] def Spill13.ofFn (f : Nat → BitVec 128) : Spill13 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12⟩

@[expose] def Spill13.zero : Spill13 := Spill13.ofFn (fun _ => 0#128)
@[expose] def Spill13Mem (ptr : BitVec 64) (t : Spill13) : SepProp := SpillMem ptr t.get

theorem spill13_ofFn_get (f : Nat → BitVec 128) (i : Nat) (hi : i < 13) :
    (Spill13.ofFn f).get i = f i := by
  match i with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl | 12 => rfl
  | _ + 13 => omega

theorem spill13Mem_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    Spill13Mem ptr (Spill13.ofFn f) = SpillMem ptr f :=
  vecRangeMem_congr fun i hi => spill13_ofFn_get f i hi

theorem spill13Mem_entails_memRegion (ptr : BitVec 64) (t : Spill13) :
    Spill13Mem ptr t ⊢ memRegion ptr 208 :=
  vecRangeMem_entails_memRegion 13 ptr t.get

private theorem spill13_set_eq_ofFn (t : Spill13) (k : Nat) (x : BitVec 128) (hk : k < 13) :
    t.set k x = Spill13.ofFn (fun j => if j = k then x else t.get j) := by
  match k with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl | 12 => rfl
  | _ + 13 => omega

theorem spill13_set_get (t : Spill13) (k : Nat) (x : BitVec 128) (hk : k < 13)
    (i : Nat) (hi : i < 13) :
    Function.update t.get k x i = (t.set k x).get i := by
  rw [spill13_set_eq_ofFn t k x hk, spill13_ofFn_get _ i hi]
  by_cases h : i = k <;> simp [h]

theorem SepLoad128.spill13 {k : Nat} {ea ptr : BitVec 64} {t : Spill13} {v : BitVec 128}
    (hk : k < 13) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (hv : t.get k = v) :
    SepLoad128 ea (Spill13Mem ptr t) v := by
  rw [← hv]; exact SepLoad128.vecRange hk ha

theorem SepStore128.spill13 {k : Nat} {ea ptr : BitVec 64} {t t' : Spill13} {val : BitVec 128}
    (hk : k < 13) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (ht : t.set k val = t') :
    SepStore128 ea val (Spill13Mem ptr t) (Spill13Mem ptr t') := by
  rw [← ht]; unfold Spill13Mem SpillMem
  rw [← vecRangeMem_congr (spill13_set_get t k val hk)]
  exact SepStore128.vecRange hk ha

structure Oct8 where
  (o0 o1 o2 o3 o4 o5 o6 o7 : BitVec 128)

@[expose] def Oct8.get (t : Oct8) : Nat → BitVec 128
  | 0 => t.o0 | 1 => t.o1 | 2 => t.o2 | 3 => t.o3 | 4 => t.o4 | 5 => t.o5 | 6 => t.o6 | 7 => t.o7
  | _ => 0#128

@[expose] def Oct8.set (t : Oct8) (k : Nat) (x : BitVec 128) : Oct8 :=
  match k with
  | 0 => { t with o0 := x } | 1 => { t with o1 := x } | 2 => { t with o2 := x } | 3 => { t with o3 := x }
  | 4 => { t with o4 := x } | 5 => { t with o5 := x } | 6 => { t with o6 := x } | 7 => { t with o7 := x }
  | _ => t

@[expose] def Oct8.ofFn (f : Nat → BitVec 128) : Oct8 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩

@[expose] def Oct8.zero : Oct8 := Oct8.ofFn (fun _ => 0#128)
@[expose] def Oct8Mem (ptr : BitVec 64) (t : Oct8) : SepProp := PolyOctMem ptr t.get

theorem oct8_ofFn_get (f : Nat → BitVec 128) (i : Nat) (hi : i < 8) :
    (Oct8.ofFn f).get i = f i := by
  match i with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | _ + 8 => omega

theorem oct8Mem_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    Oct8Mem ptr (Oct8.ofFn f) = PolyOctMem ptr f :=
  vecRangeMem_congr fun i hi => oct8_ofFn_get f i hi

theorem oct8Mem_eq_pointsToBytes (ptr : BitVec 64) (t : Oct8) :
    Oct8Mem ptr t = (ptr ↦ₛ vecRangeBytes 8 t.get) :=
  vecRangeMem_eq_pointsToBytes 8 ptr t.get

theorem oct8Mem_entails_memRegion (ptr : BitVec 64) (t : Oct8) :
    Oct8Mem ptr t ⊢ memRegion ptr 128 :=
  vecRangeMem_entails_memRegion 8 ptr t.get

private theorem oct8_set_eq_ofFn (t : Oct8) (k : Nat) (x : BitVec 128) (hk : k < 8) :
    t.set k x = Oct8.ofFn (fun j => if j = k then x else t.get j) := by
  match k with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | _ + 8 => omega

theorem oct8_set_get (t : Oct8) (k : Nat) (x : BitVec 128) (hk : k < 8)
    (i : Nat) (hi : i < 8) :
    Function.update t.get k x i = (t.set k x).get i := by
  rw [oct8_set_eq_ofFn t k x hk, oct8_ofFn_get _ i hi]
  by_cases h : i = k <;> simp [h]

theorem SepLoad128.oct8 {k : Nat} {ea ptr : BitVec 64} {t : Oct8} {v : BitVec 128}
    (hk : k < 8) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (hv : t.get k = v) :
    SepLoad128 ea (Oct8Mem ptr t) v := by
  rw [← hv]; exact SepLoad128.vecRange hk ha

theorem SepStore128.oct8 {k : Nat} {ea ptr : BitVec 64} {t t' : Oct8} {val : BitVec 128}
    (hk : k < 8) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (ht : t.set k val = t') :
    SepStore128 ea val (Oct8Mem ptr t) (Oct8Mem ptr t') := by
  rw [← ht]; unfold Oct8Mem PolyOctMem
  rw [← vecRangeMem_congr (oct8_set_get t k val hk)]
  exact SepStore128.vecRange hk ha

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
