/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4Aux

/-!
# Stage P2 Substages 1–4 Unified Composition

Composes `stageP2_sub1_to_3_kits` with `stageP2_sub4_some_kits` (discharging Arm 3) and
`stageP2_sub4_none_kits`, reaching `+0x36ac` with a unified OPK keypair representation at
`coroPtr + 0x4b0..0x4f1`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_memRegion8_to_bytes7_1 (p : BitVec 64) :
    memRegion p 8 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
        bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (p + 7#64) 1 := by
  rw [ProofLib.memRegion_split p 7 1 (by decide)]
  refine Entails.trans (sepConj_mono_left (p2_memRegion7_to_bytes7At p)) ?_
  sep_norm
  exact Entails.refl _

theorem p2_bytes7_1_to_memRegion8 (p : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (p + 7#64) 1 ⊢ memRegion p 8 := by
  refine Entails.trans (sepConj_mono_left (p2_bytes7At_to_memRegion7 p b0 b1 b2 b3 b4 b5 b6)) ?_
  rw [← ProofLib.memRegion_split p 7 1 (by decide)]
  exact Entails.refl _

theorem p2_ac0_join_16_1 (sp : BitVec 64) :
    memRegion (sp + 0xac0#64) 16 ∗ memRegion (sp + 0xad0#64) 1 = memRegion (sp + 0xac0#64) 17 :=
  (ProofLib.memRegion_split' (b := sp + 0xac0#64) (n := 16) (k := 1)
    (b' := sp + 0xad0#64) rfl (by bv_omega) (by decide)).symm

theorem p2_memRegion64_to_keyPair64UnalignedAt (a : BitVec 64) :
    memRegion a 64 ⊢
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8, ∃∗ c63 : BitVec 8,
      ∃∗ cw0 : BitVec 64, ∃∗ cw1 : BitVec 64, ∃∗ cw2 : BitVec 64, ∃∗ cw3 : BitVec 64,
      ∃∗ cw4 : BitVec 64, ∃∗ cw5 : BitVec 64, ∃∗ cw6 : BitVec 64,
        keyPair64UnalignedAt a c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 :=
  memRegion64_entails_exists_keyPair64UnalignedAt_std3 a

theorem p2_pair64_4f8_to_cells2 (coroPtr u0 u1 : BitVec 64) :
    ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1) ⊢
      cells (coroPtr + 0x4f8#64) 2 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo64_entails_memRegion _ _)) ?_
  rw [← ProofLib.memRegion_split' (b := coroPtr + 0x4f8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x500#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (coroPtr + 0x4f8#64) 2 (by decide)]
  exact Entails.refl _

/-- `Option<PreKeyId>` tag word at `msgPtr + 0x78` (`1#32` when `some _`, `0#32` when `none`). -/
@[expose] def opkOptTag32 : Option (BitVec 32) → BitVec 32
  | some _ => 1#32
  | none => 0#32

/-- `Option` tag byte at `coroPtr + 0x4b0` (`1#8` when `some _`, `0#8` when `none`). -/
@[expose] def opkOptTag8 : Option (BitVec 32) → BitVec 8
  | some _ => 1#8
  | none => 0#8

/-- Optional OPK lookup witness (`PreKeyRecord` when `some opkId`, `Unit` when `none`). -/
@[expose] def OpkOkWitness : Option (BitVec 32) → Type
  | some _ => PreKeyRecord
  | none => Unit

@[expose] def opkOkRel {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b)
    (stPk : pkKit.PkState) : (opkId? : Option (BitVec 32)) → OpkOkWitness opkId? → Prop
  | some id, r => pkKit.getRel stPk id (.ok r) ∧ pkKit.RecOk r
  | none, () => True

@[expose] def opkOkUpdate {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b)
    (stPk : pkKit.PkState) : (opkId? : Option (BitVec 32)) → OpkOkWitness opkId? → pkKit.PkState
  | some id, r => pkKit.getUpdate stPk id (.ok r)
  | none, () => stPk

@[expose] def opkOkEvs {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b) :
    (opkId? : Option (BitVec 32)) → OpkOkWitness opkId? → List TraceEvent
  | some id, r => pkKit.getEvs id (.ok r)
  | none, () => []

@[expose] def opkOkKeyBytes : (opkId? : Option (BitVec 32)) → OpkOkWitness opkId? →
    List (BitVec 8) → List (BitVec 8) → Prop
  | some _, r, pkB, skB =>
      ∃ rawPriv : List (BitVec 8), rawPriv.length = 32 ∧
        r.preKey.publicKey = 5#8 :: pkB ∧ r.preKey.privateKey = rawPriv ∧
        skB = clampBv8List rawPriv
  | none, (), _, _ => True

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
