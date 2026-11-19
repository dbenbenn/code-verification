/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs
import ProofLib.Hoare.Model
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Deserialize45
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Deserialize11

/-!
# Portable Deserialization (`B25`–`B27`)

Re-exports `blk25_deserialize4_RO_ok`, `blk26_deserialize5_RO_ok`, and `blk27_deserialize11_RO_ok`,
and lifts them to writable-input contracts (`blk25_deserialize4_RW_ok`, `blk26_deserialize5_RW_ok`,
`blk27_deserialize11_RW_ok`) via `Layer0.FrozenHeap.rw_to_ro_preserve`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockConstOk
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap (
  OnlyRW
  isROPair_pointsToBytes
  onlyRW_of_isBlock
  onlyRW_sepConj
  rw_to_ro_preserve
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  deserializeChunkBytes
  mlkemDeserialize11ROSpec
  mlkemDeserialize11RWSpec
  mlkemDeserialize4ROSpec
  mlkemDeserialize4RWSpec
  mlkemDeserialize5ROSpec
  mlkemDeserialize5RWSpec
  mlkemDeserializeROSpec
  mlkemDeserializeRWSpec
)

/-- `B25` (`PortableVector::deserialize_4`) read-only contract (`16`-byte stack). -/
theorem blk25_deserialize4_RO_ok : MlKemBlockConstOk 25 mlkemDeserialize4ROSpec :=
  Deserialize45.blk25_deserialize4_RO_ok

/-- `B26` (`PortableVector::deserialize_5`) read-only contract (`16`-byte stack). -/
theorem blk26_deserialize5_RO_ok : MlKemBlockConstOk 26 mlkemDeserialize5ROSpec :=
  Deserialize45.blk26_deserialize5_RO_ok

/-- `B27` (`PortableVector::deserialize_11`) read-only contract (`16`-byte stack). -/
theorem blk27_deserialize11_RO_ok : MlKemBlockConstOk 27 mlkemDeserialize11ROSpec :=
  Deserialize11.blk27_deserialize11_RO_ok

/-- Generic frozen-heap lift of `mlkemDeserializeROSpec d` to `mlkemDeserializeRWSpec d`,
    preserving `NonSyscallPreserved s0 sf ∧ sf.vregs = s0.vregs`. -/
theorem deserialize_RW_of_RO {j d : Nat}
    (hro : MlKemBlockConstOk j (mlkemDeserializeROSpec d)) :
    MlKemBlockConstOk j (mlkemDeserializeRWSpec d) := by
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro a R s0 hpc hrun hpre hsp hL1
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, mlkemDeserializeRWSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hpure, hspat⟩ := hpre_body
  have hspat' : s0.mem ⊨
      (a.inPtr ↦ₛ a.inBytes) ∗ ((memRegion a.outPtr 32 ∗ stackAt s0.sp 16) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  have hpair := isROPair_pointsToBytes a.inPtr a.inBytes
  have hWf : OnlyRW ((a.outPtr ↦ₛ deserializeChunkBytes d a.inBytes) ∗ stackAt s0.sp 16) :=
    onlyRW_sepConj (onlyRW_of_isBlock (IsBlock.pointsToBytes _ _))
      (onlyRW_of_isBlock (IsBlock.memRegion _ _))
  obtain ⟨R', hpre_ro, hrecover⟩ := rw_to_ro_preserve hpair hWf hspat'
  have hcallee_pre : s0.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl (mlkemDeserializeROSpec d)).pre a s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoaded, mlkemDeserializeROSpec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0, sepConj_assoc,
      pure_sepConj_of_true hpure]
    exact Satisfies.mono (by sep_frame) hpre_ro
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hro a R' s0 hpc hrun hcallee_pre hsp) hL1
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, mlkemDeserializeROSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hpure_post, hpost_ro⟩ := hpost
    have hpost_wf : sf.mem ⊨
        (a.inPtr ↦ᵣ a.inBytes) ∗
        (((a.outPtr ↦ₛ deserializeChunkBytes d a.inBytes) ∗ stackAt s0.sp 16) ∗ R') :=
      Satisfies.mono (by sep_frame) hpost_ro
    have hpost_rw := hrecover hpure_post.1 (Satisfies.of_sep_right hpost_wf)
    dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, mlkemDeserializeRWSpec]
    rw [sepConj_assoc, pure_sepConj_of_true hpure_post]
    exact Satisfies.mono (by sep_frame) hpost_rw
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- `B25` (`PortableVector::deserialize_4`) writable-input contract (`16`-byte stack). -/
theorem blk25_deserialize4_RW_ok : MlKemBlockConstOk 25 mlkemDeserialize4RWSpec :=
  deserialize_RW_of_RO blk25_deserialize4_RO_ok

/-- `B26` (`PortableVector::deserialize_5`) writable-input contract (`16`-byte stack). -/
theorem blk26_deserialize5_RW_ok : MlKemBlockConstOk 26 mlkemDeserialize5RWSpec :=
  deserialize_RW_of_RO blk26_deserialize5_RO_ok

/-- `B27` (`PortableVector::deserialize_11`) writable-input contract (`16`-byte stack). -/
theorem blk27_deserialize11_RW_ok : MlKemBlockConstOk 27 mlkemDeserialize11RWSpec :=
  deserialize_RW_of_RO blk27_deserialize11_RO_ok

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize
