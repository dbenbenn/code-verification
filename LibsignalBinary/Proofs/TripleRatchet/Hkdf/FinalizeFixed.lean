/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Defs
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `<Hmac<Sha256> as FixedOutput>::finalize_fixed`

Proves `finalizeFixedSpec` for `Hmac<Sha256>::finalize_fixed` under `[LibsignalPlacement]`.
-/

public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## `tripleRatchetProgAtExt` Predicates, `HkdfHooks`, and Step Lemmas -/

@[expose] def FinalizeFixedOkExt (b : BitVec 64) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr finalizeFixedName)
    (finalizeFixedSpec C.F)

@[expose] def ExpandMultiInfoOkExt (b : BitVec 64) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr expandMultiInfoName)
    (expandMultiInfoSpec C.F)

/-- Packaged `RunsTo` contract for `finalize_fixed` on `tripleRatchetProgAtExt b ext`. -/
@[expose] def Fin.FinalizeFixedRunsToExt (b : BitVec 64) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {key msg : List (BitVec 8)} {s0 : State},
    FinalizeFixedProof.FinPre b C.F key msg s0 →
    RunsTo (tripleRatchetProgAtExt b ext) s0 (FinalizeFixedProof.FinPost C.F key msg s0)

/-- Minimal hook-table hypothesis for HKDF (`memset`, `memcpy`, and `sha2::sha256::compress256`). -/
class HkdfHooks (F : ShaCompress) (ext : String → Option (State → State)) : Prop where
  memset : Rust.withPanics ext "memset" = some memsetHook
  memcpy : Rust.withPanics ext "memcpy" = some memcpyHook
  compress256 : Rust.withPanics ext "sha2::sha256::compress256" = some (compress256Hook F)

instance instHkdfHooksTripleRatchetExterns_trap (C : Crypto)
    (abs : String → Option (State → State)) :
    HkdfHooks C.F (trTrapExterns C abs) where
  memset := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
      LibsignalSession.sessionExterns, hookMemset_eq_memsetHook]
  memcpy := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
      LibsignalSession.sessionExterns, hookMemcpy_eq_memcpyHook]
  compress256 := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
      LibsignalSession.sessionExterns]

instance instHkdfHooksTripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    HkdfHooks C.F (tripleRatchetExterns C ctl abs) where
  memset := by
    simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
      LibsignalSession.sessionExterns, hookMemset_eq_memsetHook]
  memcpy := by
    simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
      LibsignalSession.sessionExterns, hookMemcpy_eq_memcpyHook]
  compress256 := by
    simp [Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
      LibsignalSession.sessionExterns]

instance instHkdfHooksSessionExterns (F : ShaCompress)
    (abs : String → Option (State → State)) :
    HkdfHooks F (CryptoVerification.LibsignalSession.sessionExterns F abs) where
  memset := by
    simp [Rust.withPanics, Rust.isPanicSymbol,
      LibsignalSession.sessionExterns, hookMemset_eq_memsetHook]
  memcpy := by
    simp [Rust.withPanics, Rust.isPanicSymbol,
      LibsignalSession.sessionExterns, hookMemcpy_eq_memcpyHook]
  compress256 := by
    simp [Rust.withPanics, Rust.isPanicSymbol,
      LibsignalSession.sessionExterns]

theorem HkdfHooks.of_mono {F : ShaCompress} {ext1 ext2 : String → Option (State → State)}
    [h1 : HkdfHooks F ext1]
    (hle : ∀ n f, Rust.withPanics ext1 n = some f → Rust.withPanics ext2 n = some f) :
    HkdfHooks F ext2 where
  memset := hle "memset" memsetHook h1.memset
  memcpy := hle "memcpy" memcpyHook h1.memcpy
  compress256 := hle "sha2::sha256::compress256" (compress256Hook F) h1.compress256

theorem HkdfHooks.of_le_sessionExterns {F : ShaCompress}
    {abs ext : String → Option (State → State)}
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f) :
    HkdfHooks F ext :=
  HkdfHooks.of_mono (ext1 := CryptoVerification.LibsignalSession.sessionExterns F abs) hle

theorem HkdfHooks.of_le_tripleRatchetExterns {C : Crypto} {ctl : BitVec 64}
    {abs ext : String → Option (State → State)}
    (hle : ∀ n f, Rust.withPanics (tripleRatchetExterns C ctl abs) n = some f →
      Rust.withPanics ext n = some f) :
    HkdfHooks C.F ext :=
  HkdfHooks.of_mono (ext1 := tripleRatchetExterns C ctl abs) hle

/-! ## Arithmetic and Memory Helpers -/

private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

macro "solve_fin_saved" : tactic =>
  `(tactic| (
    try rw [mem_setMem]
    simp (config := { decide := true }) only [arm64_norm]))

macro "fin_reg" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

theorem xor_63_of_lt_64 {n : ℕ} (h : n < 64) :
    BitVec.ofNat 64 n ^^^ 63#64 = BitVec.ofNat 64 (63 - n) := by
  have hbv : BitVec.ofNat 64 n < 64#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    exact h
  have hsub : 63#64 - BitVec.ofNat 64 n = BitVec.ofNat 64 (63 - n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by bv_omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    change 63 - n % 18446744073709551616 = (63 - n) % 18446744073709551616
    omega
  rw [← hsub]
  bv_bits

theorem readBytes_64_after_pad_memset (m : Memory) (hm : BitVec 64) (msg : List (BitVec 8))
    (hmsg : m.readBytes hm msg.length = msg) (hlt : msg.length < 56) :
    ((m.write8 (hm + BitVec.ofNat 64 msg.length) 0x80#8).writeBytes
      (hm + BitVec.ofNat 64 msg.length + 1#64) (List.replicate (63 - msg.length) 0#8)).readBytes hm 64 =
      msg ++ [0x80#8] ++ List.replicate (63 - msg.length) 0#8 := by
  have hw8 : m.write8 (hm + BitVec.ofNat 64 msg.length) 0x80#8 =
      m.writeBytes (hm + BitVec.ofNat 64 msg.length) [0x80#8] := rfl
  have h1 : hm + BitVec.ofNat 64 msg.length + 1#64 =
      (hm + BitVec.ofNat 64 msg.length) + BitVec.ofNat 64 ([0x80#8] : List (BitVec 8)).length := rfl
  rw [hw8, h1, ← Bytes.writeBytes_append]
  set pad := [0x80#8] ++ List.replicate (63 - msg.length) 0#8
  have hpad_len : pad.length = 64 - msg.length := by simp [pad]; omega
  have hsplit : (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes hm 64 =
      (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes hm msg.length ++
      (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes
        (hm + BitVec.ofNat 64 msg.length) (64 - msg.length) := by
    rw [← Bytes.readBytes_add]
    congr 1
    omega
  rw [hsplit]
  have hleft : (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes hm msg.length = msg := by
    by_cases h0 : msg.length = 0
    · simp [h0] at hmsg ⊢; exact hmsg
    · rw [Bytes.readBytes_writeBytes_disjoint m hm msg.length (hm + BitVec.ofNat 64 msg.length) pad]
      · exact hmsg
      · rw [hpad_len]; unfold DisjointRegions; bv_omega
  have hright : (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes
      (hm + BitVec.ofNat 64 msg.length) (64 - msg.length) = pad := by
    rw [← hpad_len]
    exact Bytes.readBytes_writeBytes_same m _ pad (by omega)
  rw [hleft, hright]
  simp [pad, List.append_assoc]

theorem agreesOutside_pad_memset (m : Memory) (hm : BitVec 64) (msg : List (BitVec 8))
    (hlt : msg.length < 56) :
    AgreesOutside m
      ((m.write8 (hm + BitVec.ofNat 64 msg.length) 0x80#8).writeBytes
        (hm + BitVec.ofNat 64 msg.length + 1#64) (List.replicate (63 - msg.length) 0#8))
      hm 64 := by
  have hw8 : m.write8 (hm + BitVec.ofNat 64 msg.length) 0x80#8 =
      m.writeBytes (hm + BitVec.ofNat 64 msg.length) [0x80#8] := rfl
  have h1 : hm + BitVec.ofNat 64 msg.length + 1#64 =
      (hm + BitVec.ofNat 64 msg.length) + BitVec.ofNat 64 ([0x80#8] : List (BitVec 8)).length := rfl
  rw [hw8, h1, ← Bytes.writeBytes_append]
  refine ProofLib.AgreesOutside.writeBytes _
    (AgreesOutside.rfl' m hm 64) ?_
  simp only [List.length_append, List.length_singleton, List.length_replicate]
  bv_omega

theorem ult_7_of_lt_56 {n : ℕ} (h : n < 56) :
    (7#64).ult (BitVec.ofNat 64 (63 - n)) = true := by
  simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : 63 - n < 18446744073709551616)]
  omega

theorem bit_len_inner_eq {n : ℕ} (h : n < 56) :
    512#64 ||| (BitVec.ofNat 64 n <<< 3#64) = BitVec.ofNat 64 (8 * (64 + n)) ∧
    512#64 ||| (BitVec.ofNat 64 n <<< 3) = BitVec.ofNat 64 (8 * (64 + n)) := by
  have hbv : BitVec.ofNat 64 n < 64#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
    exact lt_trans h (by decide)
  have hor : 512#64 ||| (BitVec.ofNat 64 n <<< 3#64) = 512#64 + 8#64 * BitVec.ofNat 64 n := by
    bv_bits
  have h1 : 512#64 + 8#64 * BitVec.ofNat 64 n = BitVec.ofNat 64 (8 * (64 + n)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    change (512 + 8 * (n % 18446744073709551616) % 18446744073709551616) % 18446744073709551616 =
      (8 * (64 + n)) % 18446744073709551616
    omega
  exact ⟨hor.trans h1, hor.trans h1⟩

theorem readBytes_write64_4 (m : Memory) (a : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    ((((m.write64 a v0).write64 (a + 8#64) v1).write64 (a + 16#64) v2).write64
      (a + 24#64) v3).readBytes a 32 =
      toLEBytes 8 v0 ++ toLEBytes 8 v1 ++ toLEBytes 8 v2 ++ toLEBytes 8 v3 := by
  have hw : (((m.write64 a v0).write64 (a + 8#64) v1).write64 (a + 16#64) v2).write64 (a + 24#64) v3 =
      m.writeBytes a (toLEBytes 8 v0 ++ toLEBytes 8 v1 ++ toLEBytes 8 v2 ++ toLEBytes 8 v3) := by
    rw [Bytes.write64_eq_writeBytes, Bytes.write64_eq_writeBytes,
        Bytes.write64_eq_writeBytes, Bytes.write64_eq_writeBytes]
    simp only [Bytes.writeBytes_append, List.length_append, Bytes.toLEBytes_length, BitVec.add_assoc]
  rw [hw]
  exact Bytes.readBytes_writeBytes_same m a _ (by simp)

theorem readBytes_fsp_64_seg2 (m : Memory) (hm fsp : BitVec 64)
    (v0 v1 v2 v3 w56 v4 v5 v6 v7 : BitVec 64)
    (hd : DisjointRegions hm 64 fsp 64) :
    (((((((((m.write64 fsp v0).write64 (fsp + 8#64) v1).write64
      (fsp + 16#64) v2).write64 (fsp + 24#64) v3).write64
      (hm + 56#64) w56).write64
      (fsp + 32#64) v4).write64 (fsp + 40#64) v5).write64
      (fsp + 48#64) v6).write64 (fsp + 56#64) v7).readBytes fsp 64 =
      toLEBytes 8 v0 ++ toLEBytes 8 v1 ++ toLEBytes 8 v2 ++ toLEBytes 8 v3 ++
      toLEBytes 8 v4 ++ toLEBytes 8 v5 ++ toLEBytes 8 v6 ++ toLEBytes 8 v7 := by
  let m_lo := (((m.write64 fsp v0).write64 (fsp + 8#64) v1).write64
    (fsp + 16#64) v2).write64 (fsp + 24#64) v3
  let m_mid := m_lo.write64 (hm + 56#64) w56
  let m_hi := (((m_mid.write64 (fsp + 32#64) v4).write64 (fsp + 40#64) v5).write64
    (fsp + 48#64) v6).write64 (fsp + 56#64) v7
  change m_hi.readBytes fsp (32 + 32) = _
  rw [Bytes.readBytes_add m_hi fsp 32 32]
  have h_hi : m_hi.readBytes (fsp + 32#64) 32 =
      toLEBytes 8 v4 ++ toLEBytes 8 v5 ++ toLEBytes 8 v6 ++ toLEBytes 8 v7 := by
    have h1 : fsp + 40#64 = (fsp + 32#64) + 8#64 := by bv_lin
    have h2 : fsp + 48#64 = (fsp + 32#64) + 16#64 := by bv_lin
    have h3 : fsp + 56#64 = (fsp + 32#64) + 24#64 := by bv_lin
    dsimp only [m_hi]
    rw [h1, h2, h3, readBytes_write64_4]
  have hag_hi : AgreesOutside m_mid m_hi (fsp + 32#64) 32 := by
    dsimp only [m_hi]; agrees_outside_writes
  have hag_mid : AgreesOutside m_lo m_mid (hm + 56#64) 8 := by
    dsimp only [m_mid]; agrees_outside_writes
  have hd_mid : DisjointRegions (hm + 56#64) 8 fsp 32 :=
    (hd.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have h_lo_eq : m_hi.readBytes fsp 32 = m_lo.readBytes fsp 32 := by
    rw [hag_hi.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hag_mid.readBytes_eq hd_mid (by decide)]
  rw [h_lo_eq, readBytes_write64_4, h_hi]
  simp only [List.append_assoc]

theorem read64_seg2a_mid (m : Memory) (hm fsp : BitVec 64)
    (u0 u1 u2 u3 w56 off : BitVec 64)
    (hoff : off.toNat + 8 ≤ 56)
    (hd : DisjointRegions hm 64 fsp 64) :
    (((((m.write64 fsp u0).write64 (fsp + 8#64) u1).write64
      (fsp + 16#64) u2).write64 (fsp + 24#64) u3).write64
      (hm + 56#64) w56).read64 (hm + off) = m.read64 (hm + off) := by
  let m_lo := (((m.write64 fsp u0).write64 (fsp + 8#64) u1).write64
    (fsp + 16#64) u2).write64 (fsp + 24#64) u3
  let m_mid := m_lo.write64 (hm + 56#64) w56
  have hag_lo : AgreesOutside m m_lo fsp 32 := by
    dsimp only [m_lo]; agrees_outside_writes
  have hag_mid : AgreesOutside m_lo m_mid (hm + 56#64) 8 := by
    dsimp only [m_mid]; agrees_outside_writes
  have hd_mid : DisjointRegions (hm + 56#64) 8 (hm + off) 8 := by
    unfold DisjointRegions; bv_omega
  have hd_lo : DisjointRegions fsp 32 (hm + off) 8 :=
    (hd.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  change m_mid.read64 (hm + off) = _
  rw [hag_mid.read64_eq hd_mid, hag_lo.read64_eq hd_lo]

theorem readBytes_56_eq_append_8 (m : Memory) (hm : BitVec 64) :
    m.readBytes hm 8 ++ m.readBytes (hm + 8#64) 8 ++ m.readBytes (hm + 16#64) 8 ++
      m.readBytes (hm + 24#64) 8 ++ m.readBytes (hm + 32#64) 8 ++
      m.readBytes (hm + 40#64) 8 ++ m.readBytes (hm + 48#64) 8 =
      m.readBytes hm 56 := by
  have h1 := (Bytes.readBytes_add m hm 8 8).symm
  have h2 := (Bytes.readBytes_add m hm 16 8).symm
  have h3 := (Bytes.readBytes_add m hm 24 8).symm
  have h4 := (Bytes.readBytes_add m hm 32 8).symm
  have h5 := (Bytes.readBytes_add m hm 40 8).symm
  have h6 := (Bytes.readBytes_add m hm 48 8).symm
  rw [h1, h2, h3, h4, h5, h6]

theorem readBytes_56_of_buf_eq (m : Memory) (hm : BitVec 64) (msg : List (BitVec 8))
    (hbuf : m.readBytes hm 64 = msg ++ [0x80#8] ++ List.replicate (63 - msg.length) 0#8)
    (hlt : msg.length < 56) :
    m.readBytes hm 56 = msg ++ [0x80#8] ++ List.replicate (55 - msg.length) 0#8 := by
  have hsplit : m.readBytes hm 64 = m.readBytes hm 56 ++ m.readBytes (hm + 56#64) 8 :=
    Bytes.readBytes_add m hm 56 8
  have hrep : 63 - msg.length = (55 - msg.length) + 8 := by omega
  rw [hsplit, hrep, List.replicate_add, ← List.append_assoc] at hbuf
  have hlen_l : (m.readBytes hm 56).length = 56 := Memory.readBytes_length m hm 56
  have hlen_r : (msg ++ [0x80#8] ++ List.replicate (55 - msg.length) 0#8).length = 56 := by
    simp; omega
  have htake := congrArg (List.take 56) hbuf
  rw [List.take_left' hlen_l, List.take_left' hlen_r] at htake
  exact htake

theorem innerLastBlock_length {msg : List (BitVec 8)} (hlt : msg.length < 56) :
    (innerLastBlock msg).length = 64 := by
  unfold innerLastBlock
  simp [toBEBytes]
  omega

theorem agreesOutside_seg2a (m : Memory) (hm fsp : BitVec 64)
    (v0 v1 v2 v3 w56 v4 v5 v6 v7 : BitVec 64) :
    let m_lo := (((m.write64 fsp v0).write64 (fsp + 8#64) v1).write64
      (fsp + 16#64) v2).write64 (fsp + 24#64) v3
    let m_mid := m_lo.write64 (hm + 56#64) w56
    let m_hi := (((m_mid.write64 (fsp + 32#64) v4).write64 (fsp + 40#64) v5).write64
      (fsp + 48#64) v6).write64 (fsp + 56#64) v7
    AgreesOutside m m_lo fsp 64 ∧
    AgreesOutside m_lo m_mid hm 64 ∧
    AgreesOutside m_mid m_hi fsp 64 := by
  refine ⟨by agrees_outside_writes, by agrees_outside_writes, by agrees_outside_writes⟩

theorem frame_seg2a {m0 m1 m2 m3 m4 : Memory} {out hm fsp : BitVec 64}
    (hf : Frame m0 m1 [(out, 32), (hm, 0x90), (fsp, 144)])
    (hag1 : AgreesOutside m1 m2 fsp 64)
    (hag2 : AgreesOutside m2 m3 hm 64)
    (hag3 : AgreesOutside m3 m4 fsp 64) :
    Frame m0 m4 [(out, 32), (hm, 0x90), (fsp, 144)] := by
  have hf1 := Frame.trans_agreesOutside_sub hf (rbase := fsp) (rlen := 144) (by simp) (by bv_omega) hag1
  have hf2 := Frame.trans_agreesOutside_sub hf1 (rbase := hm) (rlen := 0x90) (by simp) (by bv_omega) hag2
  exact Frame.trans_agreesOutside_sub hf2 (rbase := fsp) (rlen := 144) (by simp) (by bv_omega) hag3

theorem read32_words_at_64_of_shaStateBytes (m : Memory) (hm : BitVec 64) (st : ShaState)
    (h : m.readBytes (hm + 0x40#64) 32 = shaStateBytes st) :
    m.read32 (hm + 64#64) = st.get 0 ∧
    m.read32 (hm + 68#64) = st.get 1 ∧
    m.read32 (hm + 72#64) = st.get 2 ∧
    m.read32 (hm + 76#64) = st.get 3 ∧
    m.read32 (hm + 80#64) = st.get 4 ∧
    m.read32 (hm + 84#64) = st.get 5 ∧
    m.read32 (hm + 88#64) = st.get 6 ∧
    m.read32 (hm + 92#64) = st.get 7 := by
  have hw := read32_words_of_shaStateBytes m (hm + 0x40#64) st h
  simpa [BitVec.add_assoc] using hw

theorem read32_words_at_104_of_shaStateBytes (m : Memory) (hm : BitVec 64) (st : ShaState)
    (h : m.readBytes (hm + 0x68#64) 32 = shaStateBytes st) :
    m.read32 (hm + 104#64) = st.get 0 ∧
    m.read32 (hm + 108#64) = st.get 1 ∧
    m.read32 (hm + 112#64) = st.get 2 ∧
    m.read32 (hm + 116#64) = st.get 3 ∧
    m.read32 (hm + 120#64) = st.get 4 ∧
    m.read32 (hm + 124#64) = st.get 5 ∧
    m.read32 (hm + 128#64) = st.get 6 ∧
    m.read32 (hm + 132#64) = st.get 7 := by
  have hw := read32_words_of_shaStateBytes m (hm + 0x68#64) st h
  simpa [BitVec.add_assoc] using hw

private theorem toLEBytes_8_append_32 (a b : BitVec 32) :
    toLEBytes 8 (a ++ b) = toLEBytes 4 b ++ toLEBytes 4 a := by
  rw [Bytes.toLEBytes_8_eq_list, Bytes.toLEBytes_4_eq_list, Bytes.toLEBytes_4_eq_list]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem toLEBytes_8_rev32_append (x0 x1 : BitVec 32) :
    toLEBytes 8 ((rev32_64 (x1.zeroExtend 64)).truncate 32 ++
      (rev32_64 (x0.zeroExtend 64)).truncate 32) =
      toBEBytes 4 x0 ++ toBEBytes 4 x1 := by
  rw [toLEBytes_8_append_32, toLEBytes_4_rev32, toLEBytes_4_rev32]

theorem read64_seg3a_pad_32 (m : Memory) (hm fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32)
    (u0 u1 u2 u3 : BitVec 64)
    (hd : DisjointRegions hm 64 fsp 64) :
    (((((((((((((((m.write8 (hm + 32#64) 128#8).write64 (hm + 41#64) 0#64).write32
      hm w0).write32 (hm + 4#64) w1).write32
      (hm + 8#64) w2).write32 (hm + 12#64) w3).write64
      (hm + 33#64) 0#64).write32
      (hm + 16#64) w4).write32 (hm + 20#64) w5).write32
      (hm + 24#64) w6).write32 (hm + 28#64) w7).write64
      fsp u0).write64 (fsp + 8#64) u1).write64
      (fsp + 16#64) u2).write64 (fsp + 24#64) u3).read64 (hm + 32#64) = 0x80#64 := by
  let m0 := (m.write8 (hm + 32#64) 128#8).write64 (hm + 41#64) 0#64
  let m1 := (((m0.write32 hm w0).write32 (hm + 4#64) w1).write32 (hm + 8#64) w2).write32 (hm + 12#64) w3
  let m2 := m1.write64 (hm + 33#64) 0#64
  let m3 := (((m2.write32 (hm + 16#64) w4).write32 (hm + 20#64) w5).write32 (hm + 24#64) w6).write32 (hm + 28#64) w7
  have hag_lo : AgreesOutside m3
      ((((m3.write64 fsp u0).write64 (fsp + 8#64) u1).write64
        (fsp + 16#64) u2).write64 (fsp + 24#64) u3) fsp 32 := by
    agrees_outside_writes
  have hag_w47 : AgreesOutside m2 m3 (hm + 16#64) 16 := by
    dsimp only [m3]; agrees_outside_writes
  have hd_lo : DisjointRegions fsp 32 (hm + 32#64) 8 :=
    (hd.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_w47 : DisjointRegions (hm + 16#64) 16 (hm + 32#64) 8 := by
    unfold DisjointRegions; bv_omega
  rw [hag_lo.read64_eq hd_lo, hag_w47.read64_eq hd_w47]
  dsimp only [m2, m1, m0, Memory.write64, Memory.write32, Memory.read64]
  simp (config := { decide := true }) only [arm64_norm]

theorem read64_seg3a_pad_40 (m : Memory) (hm fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32)
    (u0 u1 u2 u3 : BitVec 64)
    (hd : DisjointRegions hm 64 fsp 64) :
    (((((((((((((((m.write8 (hm + 32#64) 128#8).write64 (hm + 41#64) 0#64).write32
      hm w0).write32 (hm + 4#64) w1).write32
      (hm + 8#64) w2).write32 (hm + 12#64) w3).write64
      (hm + 33#64) 0#64).write32
      (hm + 16#64) w4).write32 (hm + 20#64) w5).write32
      (hm + 24#64) w6).write32 (hm + 28#64) w7).write64
      fsp u0).write64 (fsp + 8#64) u1).write64
      (fsp + 16#64) u2).write64 (fsp + 24#64) u3).read64 (hm + 40#64) = 0#64 := by
  let m0 := (m.write8 (hm + 32#64) 128#8).write64 (hm + 41#64) 0#64
  let m1 := (((m0.write32 hm w0).write32 (hm + 4#64) w1).write32 (hm + 8#64) w2).write32 (hm + 12#64) w3
  let m2 := m1.write64 (hm + 33#64) 0#64
  let m3 := (((m2.write32 (hm + 16#64) w4).write32 (hm + 20#64) w5).write32 (hm + 24#64) w6).write32 (hm + 28#64) w7
  have hag_lo : AgreesOutside m3
      ((((m3.write64 fsp u0).write64 (fsp + 8#64) u1).write64
        (fsp + 16#64) u2).write64 (fsp + 24#64) u3) fsp 32 := by
    agrees_outside_writes
  have hag_w47 : AgreesOutside m2 m3 (hm + 16#64) 16 := by
    dsimp only [m3]; agrees_outside_writes
  have hd_lo : DisjointRegions fsp 32 (hm + 40#64) 8 :=
    (hd.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_w47 : DisjointRegions (hm + 16#64) 16 (hm + 40#64) 8 := by
    unfold DisjointRegions; bv_omega
  rw [hag_lo.read64_eq hd_lo, hag_w47.read64_eq hd_w47]
  dsimp only [m2, m1, m0, Memory.write64, Memory.write32, Memory.read64]
  simp (config := { decide := true }) only [arm64_norm]

theorem readBytes_fsp_64_seg3 (m : Memory) (hm fsp : BitVec 64)
    (v0 v1 v2 v3 z0 z1 v4 v5 v6 v7 : BitVec 64)
    (hd : DisjointRegions hm 64 fsp 64) :
    ((((((((((m.write64 fsp v0).write64 (fsp + 8#64) v1).write64
      (fsp + 16#64) v2).write64 (fsp + 24#64) v3).write64
      (hm + 48#64) z0).write64 (hm + 56#64) z1).write64
      (fsp + 32#64) v4).write64 (fsp + 40#64) v5).write64
      (fsp + 48#64) v6).write64 (fsp + 56#64) v7).readBytes fsp 64 =
      toLEBytes 8 v0 ++ toLEBytes 8 v1 ++ toLEBytes 8 v2 ++ toLEBytes 8 v3 ++
      toLEBytes 8 v4 ++ toLEBytes 8 v5 ++ toLEBytes 8 v6 ++ toLEBytes 8 v7 := by
  let m_lo := (((m.write64 fsp v0).write64 (fsp + 8#64) v1).write64
    (fsp + 16#64) v2).write64 (fsp + 24#64) v3
  let m_mid := (m_lo.write64 (hm + 48#64) z0).write64 (hm + 56#64) z1
  let m_hi := (((m_mid.write64 (fsp + 32#64) v4).write64 (fsp + 40#64) v5).write64
    (fsp + 48#64) v6).write64 (fsp + 56#64) v7
  change m_hi.readBytes fsp (32 + 32) = _
  rw [Bytes.readBytes_add m_hi fsp 32 32]
  have h_hi : m_hi.readBytes (fsp + 32#64) 32 =
      toLEBytes 8 v4 ++ toLEBytes 8 v5 ++ toLEBytes 8 v6 ++ toLEBytes 8 v7 := by
    have h1 : fsp + 40#64 = (fsp + 32#64) + 8#64 := by bv_lin
    have h2 : fsp + 48#64 = (fsp + 32#64) + 16#64 := by bv_lin
    have h3 : fsp + 56#64 = (fsp + 32#64) + 24#64 := by bv_lin
    dsimp only [m_hi]
    rw [h1, h2, h3, readBytes_write64_4]
  have hag_hi : AgreesOutside m_mid m_hi (fsp + 32#64) 32 := by
    dsimp only [m_hi]; agrees_outside_writes
  have hag_mid : AgreesOutside m_lo m_mid (hm + 48#64) 16 := by
    dsimp only [m_mid]; agrees_outside_writes
  have hd_mid : DisjointRegions (hm + 48#64) 16 fsp 32 :=
    (hd.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have h_lo_eq : m_hi.readBytes fsp 32 = m_lo.readBytes fsp 32 := by
    rw [hag_hi.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hag_mid.readBytes_eq hd_mid (by decide)]
  rw [h_lo_eq, readBytes_write64_4, h_hi]
  simp only [List.append_assoc]

theorem outerBlock_digestBytes_length (st : ShaState) :
    (outerBlock (digestBytes st)).length = 64 := by
  unfold outerBlock
  simp [toBEBytes]

theorem agreesOutside_seg3a (m : Memory) (hm fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32)
    (v0 v1 v2 v3 z0 z1 v4 v5 v6 v7 : BitVec 64) :
    let m_pad := (((((((((((m.write8 (hm + 32#64) 128#8).write64
      (hm + 41#64) 0#64).write32
      hm w0).write32 (hm + 4#64) w1).write32
      (hm + 8#64) w2).write32 (hm + 12#64) w3).write64
      (hm + 33#64) 0#64).write32
      (hm + 16#64) w4).write32 (hm + 20#64) w5).write32
      (hm + 24#64) w6).write32 (hm + 28#64) w7)
    let m_lo := (((m_pad.write64 fsp v0).write64 (fsp + 8#64) v1).write64
      (fsp + 16#64) v2).write64 (fsp + 24#64) v3
    let m_mid := (m_lo.write64 (hm + 48#64) z0).write64 (hm + 56#64) z1
    let m_hi := (((m_mid.write64 (fsp + 32#64) v4).write64 (fsp + 40#64) v5).write64
      (fsp + 48#64) v6).write64 (fsp + 56#64) v7
    AgreesOutside m m_pad hm 64 ∧
    AgreesOutside m_pad m_lo fsp 64 ∧
    AgreesOutside m_lo m_mid hm 64 ∧
    AgreesOutside m_mid m_hi fsp 64 := by
  refine ⟨by agrees_outside_writes, by agrees_outside_writes,
          by agrees_outside_writes, by agrees_outside_writes⟩

theorem finSaved_seg3a {s0 : State} {m1 m2 m3 m4 m5 : Memory} {hm fsp : BitVec 64}
    (hs : FinSaved s0 fsp m1)
    (hag1 : AgreesOutside m1 m2 hm 64)
    (hag2 : AgreesOutside m2 m3 fsp 64)
    (hag3 : AgreesOutside m3 m4 hm 64)
    (hag4 : AgreesOutside m4 m5 fsp 64)
    (hd_hm : DisjointRegions hm 64 (fsp + 0x40#64) 0x50)
    (hd_fsp : DisjointRegions fsp 64 (fsp + 0x40#64) 0x50) :
    FinSaved s0 fsp m5 :=
  FinSaved.of_agreesOutside
    (FinSaved.of_agreesOutside
      (FinSaved.of_agreesOutside
        (FinSaved.of_agreesOutside hs hag1 hd_hm)
        hag2 hd_fsp)
      hag3 hd_hm)
    hag4 hd_fsp

theorem frame_seg3a {m0 m1 m2 m3 m4 m5 : Memory} {out hm fsp : BitVec 64}
    (hf : Frame m0 m1 [(out, 32), (hm, 0x90), (fsp, 144)])
    (hag1 : AgreesOutside m1 m2 hm 64)
    (hag2 : AgreesOutside m2 m3 fsp 64)
    (hag3 : AgreesOutside m3 m4 hm 64)
    (hag4 : AgreesOutside m4 m5 fsp 64) :
    Frame m0 m5 [(out, 32), (hm, 0x90), (fsp, 144)] := by
  have hf1 := Frame.trans_agreesOutside_sub hf (rbase := hm) (rlen := 0x90) (by simp) (by bv_omega) hag1
  have hf2 := Frame.trans_agreesOutside_sub hf1 (rbase := fsp) (rlen := 144) (by simp) (by bv_omega) hag2
  have hf3 := Frame.trans_agreesOutside_sub hf2 (rbase := hm) (rlen := 0x90) (by simp) (by bv_omega) hag3
  exact Frame.trans_agreesOutside_sub hf3 (rbase := fsp) (rlen := 144) (by simp) (by bv_omega) hag4

theorem ost_eq_seg3a {m1 m2 m3 m4 m5 : Memory} {hm fsp : BitVec 64} {rhs : List (BitVec 8)}
    (host : m1.readBytes (hm + 0x68#64) 32 = rhs)
    (hag1 : AgreesOutside m1 m2 hm 64)
    (hag2 : AgreesOutside m2 m3 fsp 64)
    (hag3 : AgreesOutside m3 m4 hm 64)
    (hag4 : AgreesOutside m4 m5 fsp 64)
    (hd_hm : DisjointRegions hm 64 (hm + 0x68#64) 32)
    (hd_fsp : DisjointRegions fsp 64 (hm + 0x68#64) 32) :
    m5.readBytes (hm + 0x68#64) 32 = rhs := by
  rw [hag4.readBytes_eq hd_fsp (by decide),
      hag3.readBytes_eq hd_hm (by decide),
      hag2.readBytes_eq hd_fsp (by decide),
      hag1.readBytes_eq hd_hm (by decide), host]

theorem write32_8_eq_writeBytes_digestBytes (m : Memory) (dst : BitVec 64) (st : ShaState)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 32)
    (h0 : toLEBytes 4 v0 = toBEBytes 4 (st.get 0))
    (h1 : toLEBytes 4 v1 = toBEBytes 4 (st.get 1))
    (h2 : toLEBytes 4 v2 = toBEBytes 4 (st.get 2))
    (h3 : toLEBytes 4 v3 = toBEBytes 4 (st.get 3))
    (h4 : toLEBytes 4 v4 = toBEBytes 4 (st.get 4))
    (h5 : toLEBytes 4 v5 = toBEBytes 4 (st.get 5))
    (h6 : toLEBytes 4 v6 = toBEBytes 4 (st.get 6))
    (h7 : toLEBytes 4 v7 = toBEBytes 4 (st.get 7)) :
    ((((((((m.write32 dst v0).write32 (dst + 4#64) v1).write32 (dst + 8#64) v2).write32
      (dst + 12#64) v3).write32 (dst + 16#64) v4).write32 (dst + 20#64) v5).write32
      (dst + 24#64) v6).write32 (dst + 28#64) v7) =
      m.writeBytes dst (digestBytes st) := by
  repeat rw [Bytes.write32_eq_writeBytes]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, digestBytes_eq_append]
  simp only [Bytes.writeBytes_append, toBEBytes_4_eq_list, List.length_cons, List.length_nil,
    BitVec.add_assoc]
  rfl

theorem readBytes_write32_8_digestBytes (m : Memory) (dst : BitVec 64) (st : ShaState)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 32)
    (h0 : toLEBytes 4 v0 = toBEBytes 4 (st.get 0))
    (h1 : toLEBytes 4 v1 = toBEBytes 4 (st.get 1))
    (h2 : toLEBytes 4 v2 = toBEBytes 4 (st.get 2))
    (h3 : toLEBytes 4 v3 = toBEBytes 4 (st.get 3))
    (h4 : toLEBytes 4 v4 = toBEBytes 4 (st.get 4))
    (h5 : toLEBytes 4 v5 = toBEBytes 4 (st.get 5))
    (h6 : toLEBytes 4 v6 = toBEBytes 4 (st.get 6))
    (h7 : toLEBytes 4 v7 = toBEBytes 4 (st.get 7)) :
    ((((((((m.write32 dst v0).write32 (dst + 4#64) v1).write32 (dst + 8#64) v2).write32
      (dst + 12#64) v3).write32 (dst + 16#64) v4).write32 (dst + 20#64) v5).write32
      (dst + 24#64) v6).write32 (dst + 28#64) v7).readBytes dst 32 =
      digestBytes st := by
  rw [write32_8_eq_writeBytes_digestBytes m dst st v0 v1 v2 v3 v4 v5 v6 v7 h0 h1 h2 h3 h4 h5 h6 h7]
  have hlen : (digestBytes st).length = 32 := digestBytes_length st
  rw [← hlen]
  exact Bytes.readBytes_writeBytes_same m dst _ (by rw [hlen]; decide)

theorem agreesOutside_seg4a (m : Memory) (out hm fsp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 32) :
    let m_63 := m.write8 (hm + 63#64) 0#8
    let m_fsp := (((((((m_63.write64 fsp 0#64).write64
      (fsp + 8#64) 0#64).write64 (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
      (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64 (fsp + 48#64) 0#64).write64
      (fsp + 56#64) 0#64
    let m_hm := (((((((m_fsp.write64 (hm + 48#64) 0#64).write64
      (hm + 56#64) 0#64).write64 (hm + 32#64) 0#64).write64 (hm + 40#64) 0#64).write64
      (hm + 16#64) 0#64).write64 (hm + 24#64) 0#64).write64 hm 0#64).write64
      (hm + 8#64) 0#64
    let m_out := (((((((m_hm.write32 out v0).write32 (out + 4#64) v1).write32
      (out + 8#64) v2).write32 (out + 12#64) v3).write32 (out + 16#64) v4).write32
      (out + 20#64) v5).write32 (out + 24#64) v6).write32 (out + 28#64) v7
    AgreesOutside m m_63 hm 0x90 ∧
    AgreesOutside m_63 m_fsp fsp 64 ∧
    AgreesOutside m_fsp m_hm hm 0x90 ∧
    AgreesOutside m_hm m_out out 32 := by
  refine ⟨by agrees_outside_writes, by agrees_outside_writes,
          by agrees_outside_writes, by agrees_outside_writes⟩

theorem finSaved_seg4a {s0 : State} {m1 m2 m3 m4 m5 : Memory} {out hm fsp : BitVec 64}
    (hs : FinSaved s0 fsp m1)
    (hag1 : AgreesOutside m1 m2 hm 0x90)
    (hag2 : AgreesOutside m2 m3 fsp 64)
    (hag3 : AgreesOutside m3 m4 hm 0x90)
    (hag4 : AgreesOutside m4 m5 out 32)
    (hd_hm : DisjointRegions hm 0x90 (fsp + 0x40#64) 0x50)
    (hd_fsp : DisjointRegions fsp 64 (fsp + 0x40#64) 0x50)
    (hd_out : DisjointRegions out 32 (fsp + 0x40#64) 0x50) :
    FinSaved s0 fsp m5 :=
  FinSaved.of_agreesOutside
    (FinSaved.of_agreesOutside
      (FinSaved.of_agreesOutside
        (FinSaved.of_agreesOutside hs hag1 hd_hm)
        hag2 hd_fsp)
      hag3 hd_hm)
    hag4 hd_out

theorem frame_seg4a {m0 m1 m2 m3 m4 m5 : Memory} {out hm fsp : BitVec 64}
    (hf : Frame m0 m1 [(out, 32), (hm, 0x90), (fsp, 144)])
    (hag1 : AgreesOutside m1 m2 hm 0x90)
    (hag2 : AgreesOutside m2 m3 fsp 64)
    (hag3 : AgreesOutside m3 m4 hm 0x90)
    (hag4 : AgreesOutside m4 m5 out 32) :
    Frame m0 m5 [(out, 32), (hm, 0x90), (fsp, 144)] := by
  have hf1 := Frame.trans_agreesOutside hf (by simp) hag1
  have hf2 := Frame.trans_agreesOutside_sub hf1 (rbase := fsp) (rlen := 144) (by simp) (by bv_omega) hag2
  have hf3 := Frame.trans_agreesOutside hf2 (by simp) hag3
  exact Frame.trans_agreesOutside hf3 (by simp) hag4

/-! ## Segment Proofs -/

namespace FinalizeFixedProof

variable {C : Crypto}

/-- Cut `F0p` at `+28` (7 steps after entry): prologue complete. -/
private structure StateF0p (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (offFinalizeFixed1 + 28)
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacSt s.mem (s0.readReg64 .x1) F key msg

/-- Cut `F1` at `+76` (after `memsetHook`): buffer `hm[0..64]` holds `msg ++ [0x80] ++ 0…0`. -/
private structure StateF1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (offFinalizeFixed1 + 76)
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 msg.length
  x24_eq  : s.readReg64 .x24 = 1#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 (63 - msg.length)
  buf_eq  : s.mem.readBytes (s0.readReg64 .x1) 64 =
    msg ++ [0x80#8] ++ List.replicate (63 - msg.length) 0#8
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

/-- Cut `F2` at `+176` (right before inner `bl compress256`). -/
private structure StateF2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (offFinalizeFixed1 + 176)
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlock msg
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

/-- Cut `F3` at `+180` (after inner `compress256Hook`). -/
private structure StateF3 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (offFinalizeFixed1 + 180)
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F (hmacInnerInit F key) (innerLastBlock msg))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private theorem finSaved_seg2a {s0 : State} {m1 m2 m3 m4 : Memory} {hm fsp : BitVec 64}
    (hs : FinSaved s0 fsp m1) (hag1 : AgreesOutside m1 m2 fsp 64)
    (hag2 : AgreesOutside m2 m3 hm 64) (hag3 : AgreesOutside m3 m4 fsp 64)
    (hd_fsp : DisjointRegions fsp 64 (fsp + 0x40#64) 0x50)
    (hd_hm : DisjointRegions hm 64 (fsp + 0x40#64) 0x50) :
    FinSaved s0 fsp m4 :=
  FinSaved.of_agreesOutside
    (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hs hag1 hd_fsp) hag2 hd_hm) hag3 hd_fsp

/-- Cut `F3b` at `+304` (right before outer `bl compress256`). -/
private structure StateF3b (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (offFinalizeFixed1 + 304)
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

/-- Cut `F4` at `+308` (after outer `compress256Hook`). -/
private structure StateF4 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (offFinalizeFixed1 + 308)
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)))))

/-- Cut `F5` at `+420` (right before the 7-instruction epilogue). -/
private structure StateF5 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = b + bv% (offFinalizeFixed1 + 420)
  common : FinCommon s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg

private theorem read32_seg4a_mid (m : Memory) (hm fsp off : BitVec 64) (w : BitVec 32)
    (hoff : off = 128#64 ∨ off = 132#64)
    (hd : DisjointRegions fsp 64 hm 0x90)
    (hw : m.read32 (hm + off) = w) :
    (((((((((m.write8 (hm + 63#64) 0#8).write64
      fsp 0#64).write64 (fsp + 8#64) 0#64).write64
      (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
      (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
      (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64).read32
      (hm + off) = w := by
  have hag_fsp : AgreesOutside (m.write8 (hm + 63#64) 0#8)
      (((((((((m.write8 (hm + 63#64) 0#8).write64
        fsp 0#64).write64 (fsp + 8#64) 0#64).write64
        (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
        (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
        (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64)
      fsp 64 := by agrees_outside_writes
  have hag_63 : AgreesOutside m (m.write8 (hm + 63#64) 0#8) (hm + 63#64) 1 := by
    agrees_outside_writes
  rcases hoff with rfl | rfl <;>
    rw [hag_fsp.read32_eq (hd.sub_right _ ⟨by decide, by bv_omega⟩),
        hag_63.read32_eq (by unfold DisjointRegions; bv_omega), hw]

private theorem seg4a_disj {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key msg : List (BitVec 8)} {s0 : State} (hpre : FinPre b F key msg s0) :
    DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 ∧
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
  ⟨hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩,
   hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩,
   by unfold DisjointRegions; bv_omega,
   hpre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩⟩

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

/-! ## Relocatable `[LibsignalPlacement]` Segment Proofs -/

section Placed

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

private theorem seg1a_placed_runsTo {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s0 (StateF0p finPlacedFakeB C.F key msg s0) := by
  have hpc := hpre.pc_eq
  have hstat := hpre.status
  have hal0 : (s0.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hrw_fsp : s0.mem.RW (s0.sp - 144#64) 144 := hpre.rw_fsp
  iterate 7 s2_step
  refine RunsTo.refl ?_
  have hag : AgreesOutside s0.mem
      (((((((((s0.mem.write64 (s0.sp - 144#64 + 64#64) (s0.readReg64 .x29)).write64
        (s0.sp - 144#64 + 72#64) (s0.readReg64 .lr)).write64
        (s0.sp - 144#64 + 80#64) (s0.readReg64 .x25)).write64
        (s0.sp - 144#64 + 96#64) (s0.readReg64 .x24)).write64
        (s0.sp - 144#64 + 104#64) (s0.readReg64 .x23)).write64
        (s0.sp - 144#64 + 112#64) (s0.readReg64 .x22)).write64
        (s0.sp - 144#64 + 120#64) (s0.readReg64 .x21)).write64
        (s0.sp - 144#64 + 128#64) (s0.readReg64 .x20)).write64
        (s0.sp - 144#64 + 136#64) (s0.readReg64 .x19))
      (s0.sp - 144#64) 144 := by
    agrees_outside_writes
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := ⟨by solve_fin_saved, by solve_fin_saved, by solve_fin_saved,
                    by solve_fin_saved, by solve_fin_saved, by solve_fin_saved,
                    by solve_fin_saved, by solve_fin_saved, by solve_fin_saved⟩
          frame := by rw [mem_setMem]; exact Frame.trans_agreesOutside (Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin_reg
      x1_eq := by fin_reg
      hmac_st := by rw [mem_setMem]; exact HmacSt.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem seg1b_placed_runsTo {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF0p finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF1 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 s2_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - msg.length)).toNat = 63 - msg.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrw_memset :
      (s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 128#8).RW
        (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length + 1#64) (63 - msg.length) := by
    refine Memory.RW.of_perm_eq (by simp) (fun _ => Memory.isLazyFree_write8_of_false _ _) (hrw_hm.sub ?_)
    have := hpre.msg_lt
    bv_omega
  refine s2_memset_step_placed C H
    (dst := s0.readReg64 .x1 + BitVec.ofNat 64 msg.length + 1#64)
    (lr := (blkPl_123).base + 76#64) (len := 63 - msg.length)
    hstat rfl
    (by simp only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm]) htoNat_sub rfl hrw_memset ?_
  refine RunsTo.refl ?_
  have hag := agreesOutside_pad_memset s.mem (s0.readReg64 .x1) msg hpre.msg_lt
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := FinSaved.of_agreesOutside hsaved hag hd_hm64_fsp
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag }
      x19_eq := by fin_reg, x20_eq := by fin_reg, x21_eq := by fin_reg,
      x22_eq := by fin_reg, x23_eq := by fin_reg, x24_eq := by fin_reg, x25_eq := by fin_reg
      buf_eq := readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) msg hmsg_eq hpre.msg_lt
      ist_eq := (hag.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq
      ost_eq := (hag.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq
      obl_eq := (hag.read64_eq hd_hm64_obl).trans hobl_eq }

private theorem seg2a_placed_runsTo {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF1 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF2 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hpre.msg_lt
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_inner_eq hpre.msg_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 6 s2_step
  have hread32 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 s2_step
  clear hread32 hread40 hread48
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg2a hsaved hag1 hag2 hag3 hd_fsp64_saved hd_hm64_saved
          frame := by rw [mem_setMem]; exact frame_seg2a hframe hag1 hag2 hag3 }
      x0_eq := by fin_reg, x1_eq := by fin_reg, x2_eq := by fin_reg,
      x19_eq := by fin_reg, x20_eq := by fin_reg, x21_eq := by fin_reg, x22_eq := by fin_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) msg hbuf hpre.msg_lt]
        rfl
      ist_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans hist))
      ost_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans host))
      obl_eq := by
        rw [mem_setMem]
        exact (hag3.read64_eq hd_fsp64_obl).trans
          ((hag2.read64_eq hd_hm64_obl).trans
            ((hag1.read64_eq hd_fsp64_obl).trans hobl)) }

private theorem seg2b_placed_runsTo {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF2 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF3 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_placed C H
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 180#64) (st := hmacInnerInit C.F key) (blk := innerLastBlock msg)
    hstat rfl
    (by fin_reg) (by fin_reg) (by fin_reg) rfl
    hist hblk (innerLastBlock_length hpre.msg_lt) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg, x20_eq := by fin_reg, x21_eq := by fin_reg, x22_eq := by fin_reg
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact Bytes.readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }

private theorem seg3a_placed_runsTo {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF3 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF3b finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = 0x0003000000000000#64 := by decide
  have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  iterate 31 s2_step
  clear hread32 hread40
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _ _ _ _ 0#64 0x0003000000000000#64 0x80#64 0#64 0#64 0x0003000000000000#64
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved
          frame := by rw [mem_setMem]; exact frame_seg3a hframe hag1 hag2 hag3 hag4 }
      x0_eq := by fin_reg, x1_eq := by fin_reg, x2_eq := by fin_reg,
      x19_eq := by fin_reg, x20_eq := by fin_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
            toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
        have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
            toLEBytes 8 (rev64 768#64) =
            [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
        unfold outerBlock
        rw [digestBytes_eq_append h_in]
        simp only [List.append_assoc] at htail ⊢
        rw [htail]; rfl
      ost_eq := by
        rw [mem_setMem]
        exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

private theorem seg3b_placed_runsTo {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF3b finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF4 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  s2_step
  refine s2_compress256_step_placed C H
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 308#64) (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
    hstat rfl
    (by fin_reg) (by fin_reg) (by fin_reg) rfl
    host hblk (outerBlock_digestBytes_length h_in) hrw_ost ?_
  refine RunsTo.refl ?_
  set blk_out := shaStateBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes h_in)))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out)
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have hlen : blk_out.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg, x20_eq := by fin_reg
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact Bytes.readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }

private theorem seg4a_placed_runsTo {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF4 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF5 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_of_perm_eq hframe.2 hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm := (seg4a_disj hpre).1
  have hread128 := read32_seg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_seg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
    (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 s2_step
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 s2_step
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
    (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := seg4a_disj hpre
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by rw [mem_setMem]; exact frame_seg4a hframe hag1 hag2 hag3 hag4 }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
          (hmacWith_short C.F key msg hpre.key_le hpre.msg_lt).symm }

private theorem seg4b_placed_runsTo {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF5 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (FinPost C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  rcases hsaved with ⟨hs29, hslr, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hs29' : s.mem.read64 (s0.sp - 144#64 + 64#64) = s0.readReg64 .x29 := hs29
  have hslr' : s.mem.read64 (s0.sp - 144#64 + 72#64) = s0.readReg64 .lr := hslr
  have hs25' : s.mem.read64 (s0.sp - 144#64 + 80#64) = s0.readReg64 .x25 := hs25
  have hs24' : s.mem.read64 (s0.sp - 144#64 + 96#64) = s0.readReg64 .x24 := hs24
  have hs23' : s.mem.read64 (s0.sp - 144#64 + 104#64) = s0.readReg64 .x23 := hs23
  have hs22' : s.mem.read64 (s0.sp - 144#64 + 112#64) = s0.readReg64 .x22 := hs22
  have hs21' : s.mem.read64 (s0.sp - 144#64 + 120#64) = s0.readReg64 .x21 := hs21
  have hs20' : s.mem.read64 (s0.sp - 144#64 + 128#64) = s0.readReg64 .x20 := hs20
  have hs19' : s.mem.read64 (s0.sp - 144#64 + 136#64) = s0.readReg64 .x19 := hs19
  iterate 7 s2_step
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
    ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arm64_norm, hx26, hx27, hx28]

theorem finalize_fixed_placed_runsTo {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s0 (FinPost C.F key msg s0) :=
  (seg1a_placed_runsTo hpre).trans fun _ hs1 =>
  (seg1b_placed_runsTo hpre hs1).trans fun _ hs2 =>
  (seg2a_placed_runsTo hpre hs2).trans fun _ hs3 =>
  (seg2b_placed_runsTo hpre hs3).trans fun _ hs4 =>
  (seg3a_placed_runsTo hpre hs4).trans fun _ hs5 =>
  (seg3b_placed_runsTo hpre hs5).trans fun _ hs6 =>
  (seg4a_placed_runsTo hpre hs6).trans fun _ hs7 =>
  seg4b_placed_runsTo hpre hs7

theorem finalize_fixed_placed_runsTo_of_other_block {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    {key msg : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPost C.F key msg s0) :=
  RunsTo.of_other_block hcl (finalize_fixed_placed_runsTo hpre) hi (by decide) (by decide)

end Placed

end FinalizeFixedProof

/-! ## Separation-Logic Contract -/

/-- Relocatable `[LibsignalPlacement]` contract predicate for `finalize_fixed`. -/
@[expose] def FinalizeFixedPlacedOk [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_123).rebase (blkPl_123).base H) (blkPl_123).base (finalizeFixedSpec C.F)

theorem finalize_fixed_placed_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    FinalizeFixedPlacedOk C H := by
  unfold FinalizeFixedPlacedOk
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [finalizeFixedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hkey_le, hmsg_lt⟩, hsep⟩
  have hmsg_lt64 : x.msg.length < 64 := by omega
  have hb_out := IsBlock.memRegion x.out 32
  have hb_hm := isBlock_hmacCoreAt C.F x.hm x.key x.msg hmsg_lt64
  have hb_stk := IsBlock.memRegion (s0.sp - 144#64) 144
  change s0.mem ⊨
    (memRegion x.out 32 ∗ hmacCoreAt C.F x.hm x.key x.msg ∗ memRegion (s0.sp - 144#64) 144) ∗ R at hsep
  have hsep_out : s0.mem ⊨ memRegion x.out 32 ∗
      (hmacCoreAt C.F x.hm x.key x.msg ∗ (memRegion (s0.sp - 144#64) 144 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_out_stk : s0.mem ⊨ memRegion x.out 32 ∗
      (memRegion (s0.sp - 144#64) 144 ∗ (hmacCoreAt C.F x.hm x.key x.msg ∗ R)) := by ac_nf at hsep ⊢
  have hsep_hm : s0.mem ⊨ hmacCoreAt C.F x.hm x.key x.msg ∗
      (memRegion x.out 32 ∗ (memRegion (s0.sp - 144#64) 144 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 144#64) 144 ∗
      (memRegion x.out 32 ∗ (hmacCoreAt C.F x.hm x.key x.msg ∗ R)) := by ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hm x.key x.msg ∗
      (memRegion (s0.sp - 144#64) 144 ∗ (memRegion x.out 32 ∗ R)) := by ac_nf at hsep ⊢
  have hhmac_st : HmacSt s0.mem x.hm C.F x.key x.msg := hb_hm.read hsep_hm
  have hrw_out : RW s0.mem x.out 32 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_hm : RW s0.mem x.hm 0x90 := fun a ha => hb_hm.permNoLazy_rw hsep_hm ha
  have hrw_stk : RW s0.mem (s0.sp - 144#64) 144 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hd_out_hm : DisjointRegions x.out 32 x.hm 0x90 :=
    hb_out.disjoint hb_hm (by decide) (by decide) hsep_out
  have hd_out_stk : DisjointRegions x.out 32 (s0.sp - 144#64) 144 :=
    hb_out.disjoint hb_stk (by decide) (by decide) hsep_out_stk
  have hd_hm_stk : DisjointRegions x.hm 0x90 (s0.sp - 144#64) 144 :=
    hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
  have hfin_pre : FinalizeFixedProof.FinPre finPlacedFakeB C.F x.key x.msg s0 :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hpc
      status := hrun
      key_le := hkey_le
      msg_lt := hmsg_lt
      hmac_st := by rw [hx1]; exact hhmac_st
      rw_out := by rw [hx0]; exact hrw_out
      rw_hm := by rw [hx1]; exact hrw_hm
      rw_fsp := hrw_stk
      disj_out_hm := by rw [hx0, hx1]; exact hd_out_hm
      disj_out_fsp := by rw [hx0]; exact hd_out_stk
      disj_hm_fsp := by rw [hx1]; exact hd_hm_stk
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine (FinalizeFixedProof.finalize_fixed_placed_runsTo (H := H) hfin_pre).to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  rw [finalizeFixedSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  rw [hx0] at hout_sf
  rw [hx0, hx1] at hframe_sf
  have hb_out' := IsBlock.pointsToBytes_len (a := x.out) (length_hmacWith C.F x.key x.msg)
  have hb_hm' := IsBlock.memRegion x.hm 0x90
  have hpost_sep : sf.mem ⊨ (x.out ↦ₛ hmacWith C.F x.key x.msg) ∗
      (memRegion x.hm 0x90 ∗ (memRegion (s0.sp - 144#64) 144 ∗ R)) :=
    Frame.update_three_blocks hb_out hb_out' hb_hm hb_hm' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial trivial
  change sf.mem ⊨
    ((x.out ↦ₛ hmacWith C.F x.key x.msg) ∗ memRegion x.hm 0x90 ∗ memRegion (s0.sp - 144#64) 144) ∗ R
  ac_nf at hpost_sep ⊢

theorem finalize_fixed_placed_ok_withLsCodeLoaded [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_123).rebase (blkPl_123).base H) (blkPl_123).base
      (withLsCodeLoaded lsmpl (finalizeFixedSpec C.F)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (finalize_fixed_placed_ok C H)

end CryptoVerification.LibsignalTripleRatchet
