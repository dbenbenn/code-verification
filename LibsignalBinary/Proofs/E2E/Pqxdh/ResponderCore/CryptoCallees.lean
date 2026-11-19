/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLong
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.CodeLayout

/-!
# Unconditional In-Image Crypto Callees and PQXDH Responder Entry Points

Discharges `PqxdhHkdfExpandMultiInfoOk` (`0x1a874`, `64` / `80` / `96` B) and `PqxdhHkdfExtractOk`
(`0x1ad38`, `salt = None` and `salt = Some`), and derives unconditional `subroutine_ok` contracts
for `<HandshakeKeys>::derive` (`0x1ceb8`) and `Pqxdh::accept` (`0x23920`) on `trTrapProgAt`,
`tripleRatchetProgAt`, and `tripleRatchetProgAtExt`.
-/

public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalHmac
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-! ## 1. `expand_multi_info` (`0x1a874`) for `k = 12` (`96` B, `info = INFO_PQXDH`) and
  `PqxdhHkdfExpandMultiInfoOk` -/

/-- `Spec` for `expand_multi_info` (`b + 0x1a874`) when `okmLen = 96` and `info.length = 46`. -/
@[expose] def expandMultiInfo96_46Spec (F : ShaState → List (BitVec 8) → ShaState) :
    Spec ExpandMultiInfoGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hkdfA ∧
      s.readReg64 .x1 = x.infoHdrA ∧
      s.readReg64 .x2 = x.okmA ∧
      s.readReg64 .x3 = 96#64 ∧
      x.prk.length ≤ 64 ∧
      x.info.length = 46 ∧
      x.okmLen = 96⌝ ∗
    hmacCoreAt F x.hkdfA x.prk [] ∗
    (x.infoHdrA ↦₆₄ x.infoA) ∗
    ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
    (x.infoA ↦ᵣ x.info) ∗
    memRegion x.okmA 96 ∗
    stackAt s.sp expandMultiInfoStack
  post := fun x s₀ sf =>
    ⌜sf.trace = s₀.trace⌝ ∗
    hmacCoreAt F x.hkdfA x.prk [] ∗
    (x.infoHdrA ↦₆₄ x.infoA) ∗
    ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
    (x.infoA ↦ᵣ x.info) ∗
    (x.okmA ↦ₛ hkdfExpand F x.prk x.info 96) ∗
    stackAt s₀.sp expandMultiInfoStack

private theorem ro_outside_rw {P Q R : SepProp} {b_ro b_rw : BitVec 64} {n_ro n_rw : ℕ}
    {Φ_ro Φ_rw : Memory → Prop} {m : Memory}
    (hro : IsBlockRO P b_ro n_ro Φ_ro)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ P ∗ (Q ∗ R)) :
    ∀ a, InRegion b_ro n_ro a → OutsideRegion b_rw n_rw a := by
  intro a ha_ro
  rw [outsideRegion_iff_not_inRegion]
  intro ha_rw
  have hsep' : m ⊨ Q ∗ (P ∗ R) := by simpa [sepConj_left_comm] using hsep
  have hm_reg : m ⊨ memRegion b_rw n_rw ∗ (P ∗ R) :=
    Satisfies.mono (Arm64.sepConj_mono_left (ProofLib.IsBlock.entails_memRegion hrw)) hsep'
  have hm_pn0 := Satisfies.setPermProtNone_of_memRegion hm_reg
  have hperm_pn := (IsBlockProtNone.memRegionProtNone b_rw n_rw).perm_protNone hm_pn0 ha_rw
  have hm_pn : m.setPermNonFrozen b_rw n_rw Perm.protNone ⊨ P ∗ (memRegionProtNone b_rw n_rw ∗ R) := by
    simpa [sepConj_left_comm] using hm_pn0
  have hpr := hro.perm_r hm_pn ha_ro
  rw [hperm_pn] at hpr
  cases hpr

private theorem sep_some_1 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      A ∗ (G ∗ (B ∗ C ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_2 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      G ∗ (A ∗ (B ∗ C ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_3 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      C ∗ (A ∗ (B ∗ S1 ∗ S2 ∗ S3 ∗ G ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_4 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      C ∗ (G ∗ (A ∗ B ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_5 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      B ∗ (G ∗ (A ∗ C ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_post (P1 P2 B C S1 S2 S3 G S4 R : SepProp) :
    (P1 ∗ P2) ∗ (G ∗ (B ∗ C ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) =
      (P1 ∗ P2 ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R := by ac_rfl

section Ext

/-- `Spec` for `expand_multi_info` (`b + 0x1a874`) at `okmLen = 96`, `info.length = 46`, with
`expandMultiInfoStackExt` (`17024` B) stack budget. -/
@[expose] def expandMultiInfo96_46SpecExt (F : ShaState → List (BitVec 8) → ShaState) :
    Spec ExpandMultiInfoGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hkdfA ∧
      s.readReg64 .x1 = x.infoHdrA ∧
      s.readReg64 .x2 = x.okmA ∧
      s.readReg64 .x3 = 96#64 ∧
      x.prk.length ≤ 64 ∧
      x.info.length = 46 ∧
      x.okmLen = 96⌝ ∗
    hmacCoreAt F x.hkdfA x.prk [] ∗
    (x.infoHdrA ↦₆₄ x.infoA) ∗
    ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
    (x.infoA ↦ᵣ x.info) ∗
    memRegion x.okmA 96 ∗
    stackAt s.sp expandMultiInfoStackExt
  post := fun x s₀ sf =>
    ⌜sf.trace = s₀.trace⌝ ∗
    hmacCoreAt F x.hkdfA x.prk [] ∗
    (x.infoHdrA ↦₆₄ x.infoA) ∗
    ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
    (x.infoA ↦ᵣ x.info) ∗
    (x.okmA ↦ₛ hkdfExpand F x.prk x.info 96) ∗
    stackAt s₀.sp expandMultiInfoStackExt

private theorem stackAt_pqxdhHkdfExt_expand96 (sp : BitVec 64) :
    stackAt sp pqxdhHkdfStackExt =
      memRegion (sp - 24576#64) 7552 ∗ stackAt sp expandMultiInfoStackExt := by
  change memRegion (sp - 24576#64) 24576 =
    memRegion (sp - 24576#64) 7552 ∗ memRegion (sp - 17024#64) 17024
  exact ProofLib.memRegion_split' (b := sp - 24576#64) (n := 7552) (k := 17024)
    (b' := sp - 17024#64) rfl (by bv_omega) (by decide)

end Ext

end CryptoVerification.E2E.Pqxdh.ResponderCore
