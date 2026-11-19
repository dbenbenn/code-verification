/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsA

/-!
# Stage P2 Store-Error Unwind Arms 3–4

Proves `SepWPp` unwinds to `s0.readReg64 .x30` on `tripleRatchetProgAtExt img.base ext` for
Store-Error Arms 3 (`get_pre_key` at `+0x09c4`) and 4 (`get_identity_key_pair` at `+0x07bc`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

theorem p2_memRegion7_to_bytes7At (p : BitVec 64) :
    memRegion p 7 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
        bytes7At p b0 b1 b2 b3 b4 b5 b6 := by
  dsimp only [bytes7At]
  rw [memRegion_split p 1 6 (by decide), ProofLib.memRegion_one p]
  simp only [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b0
  rw [memRegion_split (p + 1#64) 1 5 (by decide), ProofLib.memRegion_one (p + 1#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b1
  rw [memRegion_split (p + 1#64 + 1#64) 1 4 (by decide), ProofLib.memRegion_one (p + 1#64 + 1#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b2
  rw [memRegion_split (p + 1#64 + 1#64 + 1#64) 1 3 (by decide),
      ProofLib.memRegion_one (p + 1#64 + 1#64 + 1#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b3
  rw [memRegion_split (p + 1#64 + 1#64 + 1#64 + 1#64) 1 2 (by decide),
      ProofLib.memRegion_one (p + 1#64 + 1#64 + 1#64 + 1#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b4
  rw [memRegion_split (p + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 1 (by decide),
      ProofLib.memRegion_one (p + 1#64 + 1#64 + 1#64 + 1#64 + 1#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b5
  rw [ProofLib.memRegion_one (p + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64)]
  simp only [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro b6
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right b0 (Entails.sepExists_right b1 (Entails.sepExists_right b2
    (Entails.sepExists_right b3 (Entails.sepExists_right b4 (Entails.sepExists_right b5
      (Entails.sepExists_right b6 (Entails.of_eq (by ac_rfl))))))))

theorem p2_bytes7At_to_memRegion7 (p : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    bytes7At p b0 b1 b2 b3 b4 b5 b6 ⊢ memRegion p 7 := by
  dsimp only [bytes7At]
  rw [memRegion_split p 1 6 (by decide),
      memRegion_split (p + 1#64) 1 5 (by decide),
      memRegion_split (p + 1#64 + 1#64) 1 4 (by decide),
      memRegion_split (p + 1#64 + 1#64 + 1#64) 1 3 (by decide),
      memRegion_split (p + 1#64 + 1#64 + 1#64 + 1#64) 1 2 (by decide),
      memRegion_split (p + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 1 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo8_entails_memRegion p b0)
    (sepConj_mono (pointsTo8_entails_memRegion (p + 1#64) b1)
      (sepConj_mono (pointsTo8_entails_memRegion (p + 2#64) b2)
        (sepConj_mono (pointsTo8_entails_memRegion (p + 3#64) b3)
          (sepConj_mono (pointsTo8_entails_memRegion (p + 4#64) b4)
            (sepConj_mono (pointsTo8_entails_memRegion (p + 5#64) b5)
              (pointsTo8_entails_memRegion (p + 6#64) b6))))))

theorem p2_kpPollErr_unpack {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (p : BitVec 64) (e : skit.KpErr) :
    kpPollOutAt skit p (.error e) ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
      ∃∗ w6 : BitVec 64, ∃∗ b63 : BitVec 8,
        (p ↦₈ 1#8) ∗
        keyPair64UnalignedAt (p + 1#64) b0 b1 b2 b3 b4 b5 b6
          (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
          (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) w6 b63 ∗
        memRegion (p + 0x41#64) 7 ∗
        skit.kpErr.heap e := by
  dsimp only [kpPollOutAt, speErrAt, speWordsAt, keyPair64UnalignedAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (p2_memRegion7_to_bytes7At (p + 1#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b0
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b3
  apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b6
  rw [memRegion_split (p + 0x38#64) 8 8 (by decide), ProofLib.memRegion_eight (p + 0x38#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w6
  rw [memRegion_split (p + 0x38#64 + 8#64) 1 7 (by decide),
      ProofLib.memRegion_one (p + 0x38#64 + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b63
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.sepExists_right b0 (Entails.sepExists_right b1 (Entails.sepExists_right b2
    (Entails.sepExists_right b3 (Entails.sepExists_right b4 (Entails.sepExists_right b5
      (Entails.sepExists_right b6 (Entails.sepExists_right w6 (Entails.sepExists_right b63
        (Entails.of_eq (by ac_rfl))))))))))

theorem p2_keyPair64Unaligned_to_memRegion72 (p : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    (p ↦₈ 1#8) ∗ keyPair64UnalignedAt (p + 1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
      memRegion (p + 0x41#64) 7 ⊢ memRegion p 72 := by
  dsimp only [keyPair64UnalignedAt]
  rw [memRegion_split p 1 71 (by decide),
      memRegion_split (p + 1#64) 7 64 (by decide),
      memRegion_split (p + 1#64 + 7#64) 8 56 (by decide),
      memRegion_split (p + 1#64 + 7#64 + 8#64) 8 48 (by decide),
      memRegion_split (p + 1#64 + 7#64 + 8#64 + 8#64) 8 40 (by decide),
      memRegion_split (p + 1#64 + 7#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      memRegion_split (p + 1#64 + 7#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      memRegion_split (p + 1#64 + 7#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      memRegion_split (p + 1#64 + 7#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
      memRegion_split (p + 1#64 + 7#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo8_entails_memRegion p 1#8)
    (sepConj_mono (p2_bytes7At_to_memRegion7 (p + 1#64) b0 b1 b2 b3 b4 b5 b6)
      (sepConj_mono (pointsTo64_entails_memRegion (p + 8#64) w0)
        (sepConj_mono (pointsTo64_entails_memRegion (p + 0x10#64) w1)
          (sepConj_mono (pointsTo64_entails_memRegion (p + 0x18#64) w2)
            (sepConj_mono (pointsTo64_entails_memRegion (p + 0x20#64) w3)
              (sepConj_mono (pointsTo64_entails_memRegion (p + 0x28#64) w4)
                (sepConj_mono (pointsTo64_entails_memRegion (p + 0x30#64) w5)
                  (sepConj_mono (pointsTo64_entails_memRegion (p + 0x38#64) w6)
                    (sepConj_mono (pointsTo8_entails_memRegion (p + 0x40#64) b63)
                      (Entails.refl _))))))))))

theorem p2_memRegion9_fp_unpack (fp : BitVec 64) :
    memRegion (fp + 0xffffffffffffff80#64) 9 ⊢
      ∃∗ u_fp80 : BitVec 64, ∃∗ b_fp78 : BitVec 8,
        ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗
        ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) := by
  rw [memRegion_split (fp + 0xffffffffffffff80#64) 8 1 (by decide),
      ProofLib.memRegion_eight (fp + 0xffffffffffffff80#64)]
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u_fp80
  rw [ProofLib.memRegion_one (fp + 0xffffffffffffff80#64 + 8#64)]
  simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro b_fp78
  exact Entails.sepExists_right u_fp80 (Entails.sepExists_right b_fp78 (Entails.refl _))

theorem p2_fp80_to_memRegion9 (fp u_fp80 : BitVec 64) (b_fp78 : BitVec 8) :
    ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗
      ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ⊢
      memRegion (fp + 0xffffffffffffff80#64) 9 := by
  rw [memRegion_split (fp + 0xffffffffffffff80#64) 8 1 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion (fp + 0xffffffffffffff80#64) u_fp80)
    (pointsTo8_entails_memRegion (fp + 0xffffffffffffff88#64) b_fp78)

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
