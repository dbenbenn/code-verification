/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacStepsA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.CodeLayout

/-!
# `crypto::hmac_sha256` Symbolic-Offset Segments (`seg1b2` through `seg4b`)

Part B of the `RunsToE (tripleRatchetProgAtExt img.base ext)` segment proofs for
`libsignal_protocol::crypto::hmac_sha256` at `extHookStack` (`16384` B).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (session2MemsetExternSpec compress256ExternShaSpec)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

attribute [local arm64_norm]
  Memory.read128 Memory.write128 MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  read32_write8_base_off_disjoint

private theorem pc_setMem' (s : State) (m : Memory) :
    (s.setMem m).pc = s.pc := rfl

private theorem status_setMem' (s : State) (m : Memory) :
    (s.setMem m).status = s.status := rfl

private theorem sp_setMem' (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := rfl

private theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := rfl

private theorem read8_eq_of_readBytes_eq' {m₁ m₂ : Memory} {a₁ a₂ : BitVec 64} {n : ℕ}
    (h : m₁.readBytes a₁ n = m₂.readBytes a₂ n) {i : ℕ} (hi : i < n) :
    m₁.read8 (a₁ + BitVec.ofNat 64 i) = m₂.read8 (a₂ + BitVec.ofNat 64 i) := by
  have hget : (m₁.readBytes a₁ n)[i]? = (m₂.readBytes a₂ n)[i]? := by rw [h]
  simpa [Memory.readBytes, hi] using hget

private theorem read64_eq_writeBytes_146_62_of_s2Frame
    {m m' : Memory} {base : BitVec 64}
    (hrw : RW m (base + 144#64) 64)
    (hrep : m'.readBytes (base + 146#64) 62 = List.replicate 62 0#8)
    (hfr : S2Frame m m' [(base + 146#64, 62), (base - 16384#64, 16384)])
    (off : BitVec 64)
    (hoff : (off - 144#64).toNat + 8 ≤ 64 := by decide) :
    m'.read64 (base + off) =
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read64 (base + off) := by
  let mw := m.writeBytes (base + 146#64) (List.replicate 62 0#8)
  have hrep_w : mw.readBytes (base + 146#64) 62 = List.replicate 62 0#8 :=
    Layout.readBytes_writeBytes_eq m (base + 146#64) (List.replicate 62 0#8) 62 (by simp) (by decide)
  have hbyte (k : ℕ) (hk : k < 8) :
      m'.read8 ((base + off) + BitVec.ofNat 64 k) =
        mw.read8 ((base + off) + BitVec.ofNat 64 k) := by
    let a := (base + off) + BitVec.ofNat 64 k
    have hin64 : InRegion (base + 144#64) 64 a := by
      dsimp only [a]; unfold InRegion; clear * - hoff hk; bv_omega
    obtain ⟨hperm_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin64)
    have hr_a : (m.perm a).r = true := by
      rw [hperm_a]; rfl
    by_cases hin62 : InRegion (base + 146#64) 62 a
    · obtain ⟨i, hi, ha_eq⟩ := (inRegion_iff_exists_offset (base + 146#64) 62 a (by decide)).mp hin62
      change m'.read8 a = mw.read8 a
      rw [ha_eq]
      exact read8_eq_of_readBytes_eq' (hrep.trans hrep_w.symm) hi
    · have hout62 : OutsideRegion (base + 146#64) 62 a :=
        (outsideRegion_iff_not_inRegion (base + 146#64) 62 a).mpr hin62
      have hout_stk : OutsideRegion (base - 16384#64) 16384 a := by
        dsimp only [a]; unfold OutsideRegion; clear * - hoff hk; bv_omega
      have hm' : m'.read8 a = m.read8 a :=
        hfr.1 a hr_a hlf_a (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hout62
          · exact hout_stk)
      have hmw : mw.read8 a = m.read8 a :=
        (_root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.AgreesOutside.writeBytes_self
          m (base + 146#64) (List.replicate 62 0#8)).1 a
          (by simpa using hout62)
      exact hm'.trans hmw.symm
  have e0 := hbyte 0 (by decide)
  have e1 := hbyte 1 (by decide)
  have e2 := hbyte 2 (by decide)
  have e3 := hbyte 3 (by decide)
  have e4 := hbyte 4 (by decide)
  have e5 := hbyte 5 (by decide)
  have e6 := hbyte 6 (by decide)
  have e7 := hbyte 7 (by decide)
  change m'.read64 (base + off) = mw.read64 (base + off)
  dsimp only [Memory.read64]
  simp only [e0, e1, e2, e3, e4, e5, e6, e7]

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX
