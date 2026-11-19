/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs

/-!
# `.rodata` Constant and Table Lookup Lemmas (`RoTables`)

`MlKemRoOk` read-only memory bundle, `decide +kernel` byte lengths, `ByteSlice.readLE` lookup
helpers for `ZETA_TABLE` (`256` bytes = `128` `i16` values) and `KECCAK_RC` (`192` bytes = `24`
`u64` round constants), and 128-bit vector values (`v2 ++ v1`) for `cst16.0`..`cst16.8`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemMultiLib
  mlkemData00Bytes
  mlkemData01Bytes
  mlkemData02Bytes
  mlkemData03Bytes
  mlkemData04Bytes
  mlkemData05Bytes
  mlkemData06Bytes
  mlkemData07Bytes
  mlkemData08Bytes
  mlkemData09Bytes
  mlkemData10Bytes
)

/-! ## 1. `MlKemRoOk` Read-Only `.rodata` Bundle & `InElf` Extraction -/

/-- All 11 read-only `.rodata` constants of `mlkemMultiLib` hold in memory `m` at their
    placement addresses `mpl.ρ sym` with permission `.ro`. -/
structure MlKemRoOk (mpl : MultiPlacement) (m : Memory) : Prop where
  zetaTable : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0") mlkemData00Bytes
  keccakRc  : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29") mlkemData01Bytes
  cst16_0   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.0") mlkemData02Bytes
  cst16_1   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.1") mlkemData03Bytes
  cst16_2   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.2") mlkemData04Bytes
  cst16_3   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.3") mlkemData05Bytes
  cst16_4   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.4") mlkemData06Bytes
  cst16_5   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.5") mlkemData07Bytes
  cst16_6   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.6") mlkemData08Bytes
  cst16_7   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.7") mlkemData09Bytes
  cst16_8   : RoDataAt m (mpl.ρ "libcrux_ml_kem:.rodata.cst16.8") mlkemData10Bytes

private theorem readBytes_eq_of_ro_keepsFrozen {m m' : Memory} (hkf : m.KeepsFrozen m') :
    ∀ (n : Nat) (addr : BitVec 64), n ≤ 2 ^ 64 → m.RO addr n →
      m'.readBytes addr n = m.readBytes addr n
  | 0, _, _, _ => rfl
  | n + 1, addr, hn, hro => by
    have h0 : InRegion addr (n + 1) addr := by
      unfold InRegion
      rw [BitVec.sub_self]
      exact Nat.zero_lt_succ n
    have hfz0 : m.Frozen addr := by
      unfold Memory.Frozen
      rw [(hro addr h0).1]
      rfl
    have hro' : m.RO (addr + 1#64) n := by
      intro a ha
      apply hro a
      unfold InRegion at ha ⊢
      have hsub : a - addr = (a - (addr + 1#64)) + 1#64 := by bv_omega
      rw [hsub, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat]
      omega
    simp only [Memory.readBytes, (hkf addr hfz0).1,
      readBytes_eq_of_ro_keepsFrozen hkf n (addr + 1#64) (by omega) hro']

/-- `RoDataAt` is preserved across any `KeepsFrozen` memory transition (for `bytes.length ≤ 2 ^ 64`). -/
theorem roDataAt_of_keepsFrozen {m m' : Memory} {addr : BitVec 64} {bytes : List (BitVec 8)}
    (hro : RoDataAt m addr bytes) (hkf : m.KeepsFrozen m')
    (hlen : bytes.length ≤ 2 ^ 64 := by decide) :
    RoDataAt m' addr bytes := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨hp, hlf⟩ := hro.1 a ha
    have hfz : m.Frozen a := by unfold Memory.Frozen; rw [hp]; rfl
    obtain ⟨_, hp', hlf', _⟩ := hkf a hfz
    exact ⟨hp'.trans hp, hlf'.trans hlf⟩
  · rw [readBytes_eq_of_ro_keepsFrozen hkf bytes.length addr hlen hro.1, hro.2]

theorem MlKemRoOk.of_keepsFrozen {mpl : MultiPlacement} {m m' : Memory}
    (h : MlKemRoOk mpl m) (hkf : m.KeepsFrozen m') : MlKemRoOk mpl m' where
  zetaTable := roDataAt_of_keepsFrozen h.zetaTable hkf (by decide +kernel)
  keccakRc  := roDataAt_of_keepsFrozen h.keccakRc hkf (by decide +kernel)
  cst16_0   := roDataAt_of_keepsFrozen h.cst16_0 hkf (by decide +kernel)
  cst16_1   := roDataAt_of_keepsFrozen h.cst16_1 hkf (by decide +kernel)
  cst16_2   := roDataAt_of_keepsFrozen h.cst16_2 hkf (by decide +kernel)
  cst16_3   := roDataAt_of_keepsFrozen h.cst16_3 hkf (by decide +kernel)
  cst16_4   := roDataAt_of_keepsFrozen h.cst16_4 hkf (by decide +kernel)
  cst16_5   := roDataAt_of_keepsFrozen h.cst16_5 hkf (by decide +kernel)
  cst16_6   := roDataAt_of_keepsFrozen h.cst16_6 hkf (by decide +kernel)
  cst16_7   := roDataAt_of_keepsFrozen h.cst16_7 hkf (by decide +kernel)
  cst16_8   := roDataAt_of_keepsFrozen h.cst16_8 hkf (by decide +kernel)

/-- Introduce `(addr ↦ᵣ bytes)` into a `SepWP` spatial context from a `RoDataAt` hypothesis. -/
theorem SepWP.roDataAt_intro {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {addr : BitVec 64} {bytes : List (BitVec 8)}
    (hro : RoDataAt s.mem addr bytes)
    (hlen : bytes.length ≤ 2 ^ 64 := by decide)
    (h : SepWP prog target_pc s ((addr ↦ᵣ bytes) ∗ P) post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at h ⊢
  intro R hm
  apply h R
  rw [sepConj_assoc]
  exact Satisfies.rodata_intro hro.1 hro.2 hlen hm

/-! ## 2. Byte Lengths of `.rodata` Constants -/

@[simp] theorem mlkemData00Bytes_length : mlkemData00Bytes.length = 256 := by decide +kernel
@[simp] theorem mlkemData01Bytes_length : mlkemData01Bytes.length = 192 := by decide +kernel
@[simp] theorem mlkemData02Bytes_length : mlkemData02Bytes.length = 16 := by decide +kernel
@[simp] theorem mlkemData03Bytes_length : mlkemData03Bytes.length = 16 := by decide +kernel
@[simp] theorem mlkemData04Bytes_length : mlkemData04Bytes.length = 16 := by decide +kernel
@[simp] theorem mlkemData05Bytes_length : mlkemData05Bytes.length = 16 := by decide +kernel
@[simp] theorem mlkemData06Bytes_length : mlkemData06Bytes.length = 16 := by decide +kernel
@[simp] theorem mlkemData07Bytes_length : mlkemData07Bytes.length = 16 := by decide +kernel
@[simp] theorem mlkemData08Bytes_length : mlkemData08Bytes.length = 16 := by decide +kernel
@[simp] theorem mlkemData09Bytes_length : mlkemData09Bytes.length = 16 := by decide +kernel
@[simp] theorem mlkemData10Bytes_length : mlkemData10Bytes.length = 16 := by decide +kernel

/-! ## 3. Generic Linear Table Lookup Checkers (16-Bit & 64-Bit Little-Endian) -/

theorem readLE_cons2 (b0 b1 : BitVec 8) (rest : List (BitVec 8)) (off n : Nat) :
    ByteSlice.readLE (b0 :: b1 :: rest) (off + 2) n = ByteSlice.readLE rest off n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih,
      show off + 2 + n = (off + n) + 2 by omega]
    rfl

theorem readLE_cons8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (rest : List (BitVec 8)) (off n : Nat) :
    ByteSlice.readLE (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) (off + 8) n =
    ByteSlice.readLE rest off n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih,
      show off + 8 + n = (off + n) + 8 by omega]
    rfl

def checkWords16 (bs : List (BitVec 8)) (expected : Nat → BitVec 16)
    (idx rem : Nat) : Bool :=
  match rem, bs with
  | 0, _ => true
  | rem + 1, b0 :: b1 :: rest =>
    ((b1 ++ b0) == expected idx) && checkWords16 rest expected (idx + 1) rem
  | _ + 1, _ => false

def checkWords64 (bs : List (BitVec 8)) (expected : Nat → BitVec 64)
    (idx rem : Nat) : Bool :=
  match rem, bs with
  | 0, _ => true
  | rem + 1, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7 == expected idx) &&
      checkWords64 rest expected (idx + 1) rem
  | _ + 1, _ => false

theorem of_checkWords16 {bs : List (BitVec 8)} {expected : Nat → BitVec 16} {idx rem k : Nat}
    (h : checkWords16 bs expected idx rem = true) (hk : k < rem) :
    (ByteSlice.readLE bs (2 * k) 2).setWidth 16 = expected (idx + k) := by
  induction rem generalizing bs idx k with
  | zero => omega
  | succ rem ih =>
    unfold checkWords16 at h
    rcases bs with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
    all_goals try contradiction
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases k with _ | k
    · rw [Nat.mul_zero, Nat.add_zero, ← h.1]
      simp only [ByteSlice.readLE_succ, ByteSlice.readLE_zero, Nat.add_zero,
        List.getD_cons_zero, List.getD_cons_succ]
      bv_bits
    · have hrec := @ih rest (idx + 1) k h.2 (by omega)
      rw [show idx + 1 + k = idx + (k + 1) by omega] at hrec
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, readLE_cons2]
      exact hrec

theorem of_checkWords64 {bs : List (BitVec 8)} {expected : Nat → BitVec 64} {idx rem k : Nat}
    (h : checkWords64 bs expected idx rem = true) (hk : k < rem) :
    ByteSlice.readLE bs (8 * k) 8 = expected (idx + k) := by
  induction rem generalizing bs idx k with
  | zero => omega
  | succ rem ih =>
    unfold checkWords64 at h
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals try contradiction
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases k with _ | k
    · rw [Nat.mul_zero, Nat.add_zero, ← ByteSlice.pack64_eq_readLE_8]
      exact h.1
    · have hrec := @ih rest (idx + 1) k h.2 (by omega)
      rw [show idx + 1 + k = idx + (k + 1) by omega] at hrec
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, readLE_cons8]
      exact hrec

/-! ## 4. Exact 64-Bit / 128-Bit Values of `.rodata.cst16.0`..`.rodata.cst16.8` -/

/-- Pack two 64-bit little-endian halves of a 16-byte constant into the 128-bit `LDR Qt` value. -/
@[expose] def cst16Vec (bs : List (BitVec 8)) : BitVec 128 :=
  ByteSlice.readLE bs 8 8 ++ ByteSlice.readLE bs 0 8

-- cst16.0: bytes `ff 00 00 ff ff ff ff ff ff ff ff ff ff ff ff ff` (Keccak block byte-mask)
theorem cst16_0_lo : ByteSlice.readLE mlkemData02Bytes 0 8 = 0xffffffffff0000ff#64 := by decide +kernel
theorem cst16_0_hi : ByteSlice.readLE mlkemData02Bytes 8 8 = 0xffffffffffffffff#64 := by decide +kernel
theorem cst16_0_vec : cst16Vec mlkemData02Bytes = 0xffffffffffffffffffffffffff0000ff#128 := by decide +kernel

-- cst16.1: bytes `00 01 1f 00 00 00 ...` = SHAKE128 block-index/pad `{0x00, 0x01, 0x1f, 0..}`
theorem cst16_1_lo : ByteSlice.readLE mlkemData03Bytes 0 8 = 0x00000000001f0100#64 := by decide +kernel
theorem cst16_1_hi : ByteSlice.readLE mlkemData03Bytes 8 8 = 0x0000000000000000#64 := by decide +kernel
theorem cst16_1_vec : cst16Vec mlkemData03Bytes = 0x000000000000000000000000001f0100#128 := by decide +kernel

-- cst16.2: bytes `00 02 1f 00 00 00 ...` = SHAKE128 block-index/pad `{0x00, 0x02, 0x1f, 0..}`
theorem cst16_2_lo : ByteSlice.readLE mlkemData04Bytes 0 8 = 0x00000000001f0200#64 := by decide +kernel
theorem cst16_2_hi : ByteSlice.readLE mlkemData04Bytes 8 8 = 0x0000000000000000#64 := by decide +kernel
theorem cst16_2_vec : cst16Vec mlkemData04Bytes = 0x000000000000000000000000001f0200#128 := by decide +kernel

-- cst16.3: bytes `00 01 01 02 03 04 04 05 06 07 07 08 09 0a 0a 0b` = `TBL` byte shuffle mask (`deserialize_12`)
theorem cst16_3_lo : ByteSlice.readLE mlkemData05Bytes 0 8 = 0x0504040302010100#64 := by decide +kernel
theorem cst16_3_hi : ByteSlice.readLE mlkemData05Bytes 8 8 = 0x0b0a0a0908070706#64 := by decide +kernel
theorem cst16_3_vec : cst16Vec mlkemData05Bytes = 0x0b0a0a09080707060504040302010100#128 := by decide +kernel

-- cst16.4: bytes `f1 ff f2 ff f3 ff f4 ff f5 ff f6 ff f7 ff f8 ff` = `i16x8` shift counts `[-15, -14, ..., -8]`
theorem cst16_4_lo : ByteSlice.readLE mlkemData06Bytes 0 8 = 0xfff4fff3fff2fff1#64 := by decide +kernel
theorem cst16_4_hi : ByteSlice.readLE mlkemData06Bytes 8 8 = 0xfff8fff7fff6fff5#64 := by decide +kernel
theorem cst16_4_vec : cst16Vec mlkemData06Bytes = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 := by decide +kernel

-- cst16.5: bytes `01 00 02 00 04 00 08 00 10 00 20 00 40 00 80 00` = `u16x8` bit masks `[1, 2, 4, 8, 16, 32, 64, 128]`
theorem cst16_5_lo : ByteSlice.readLE mlkemData07Bytes 0 8 = 0x0008000400020001#64 := by decide +kernel
theorem cst16_5_hi : ByteSlice.readLE mlkemData07Bytes 8 8 = 0x0080004000200010#64 := by decide +kernel
theorem cst16_5_vec : cst16Vec mlkemData07Bytes = 0x00800040002000100008000400020001#128 := by decide +kernel

-- cst16.6: bytes `00 00 ff 00 fe ff fd ff fc ff fb ff fa ff f9 ff` = `i16x8` lanes `[0, 255, -2, -3, -4, -5, -6, -7]` (low signed bytes `[0, -1, -2, -3, -4, -5, -6, -7]` for `SSHL`/`USHL`)
theorem cst16_6_lo : ByteSlice.readLE mlkemData08Bytes 0 8 = 0xfffdfffe00ff0000#64 := by decide +kernel
theorem cst16_6_hi : ByteSlice.readLE mlkemData08Bytes 8 8 = 0xfff9fffafffbfffc#64 := by decide +kernel
theorem cst16_6_vec : cst16Vec mlkemData08Bytes = 0xfff9fffafffbfffcfffdfffe00ff0000#128 := by decide +kernel

-- cst16.7: bytes `00 00 04 00 08 00 0c 00 00 00 04 00 08 00 0c 00` = `i16x8` shift counts `[0, 4, 8, 12, 0, 4, 8, 12]`
theorem cst16_7_lo : ByteSlice.readLE mlkemData09Bytes 0 8 = 0x000c000800040000#64 := by decide +kernel
theorem cst16_7_hi : ByteSlice.readLE mlkemData09Bytes 8 8 = 0x000c000800040000#64 := by decide +kernel
theorem cst16_7_vec : cst16Vec mlkemData09Bytes = 0x000c000800040000000c000800040000#128 := by decide +kernel

-- cst16.8: bytes `00 03 1f 00 00 00 ...` = SHAKE128 block-index/pad `{0x00, 0x03, 0x1f, 0..}`
theorem cst16_8_lo : ByteSlice.readLE mlkemData10Bytes 0 8 = 0x00000000001f0300#64 := by decide +kernel
theorem cst16_8_hi : ByteSlice.readLE mlkemData10Bytes 8 8 = 0x0000000000000000#64 := by decide +kernel
theorem cst16_8_vec : cst16Vec mlkemData10Bytes = 0x000000000000000000000000001f0300#128 := by decide +kernel

/-! ## 5. `KECCAK_RC` (`24` × `u64`) & `ZETA_TABLE` (`128` × `i16`) Lookup Functions -/

/-- Read the `r`-th 64-bit Keccak round constant (`r < 24`) directly from `mlkemData01Bytes`. -/
@[expose] def keccakRcAt (r : Nat) : BitVec 64 :=
  ByteSlice.readLE mlkemData01Bytes (8 * r) 8

/-- Read the `k`-th 16-bit NTT zeta entry (`k < 128`) directly from `mlkemData00Bytes`. -/
@[expose] def zetaTableAt (k : Nat) : BitVec 16 :=
  (ByteSlice.readLE mlkemData00Bytes (2 * k) 2).setWidth 16

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
