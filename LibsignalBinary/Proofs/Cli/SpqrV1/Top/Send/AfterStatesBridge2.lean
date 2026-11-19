/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncode
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerDispatch
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeader
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
public section

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (ShaCompress)

open CryptoVerification

open CryptoVerification.CodeLayout

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.SpqrV1.ChainProofs

open CryptoVerification.SpqrV1.Top.ChainFrom

open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm

open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open CryptoVerification.SpqrV1.Top.MessageSerialize

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.Prost.EncodeToVec

/-! ## 1. Relocation and Decomposition Helpers (`+4000..+4364`) -/

private theorem call_memcpy_bytes_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {bs : List (BitVec 8)} {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs)) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VRegsAt s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      SepWP prog target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionSpec]; rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace)
      ⟨hcs_sf.2.2.2.2.2.2.2.2.2.2.2⟩
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1

private theorem call_memcpy_relocate_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {n : Nat} {F : BitVec 64 → SepProp}
    (hrel : States.Leaves.Relocatable n F)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VRegsAt s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (hrel src))) ?_
  wp_pull_exists; rename_i bs
  wp_focus_pure; intro hlen
  refine call_memcpy_bytes_bridge2 hcall dst src hlen hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
    (Frame := States.Leaves.relocatedHeap F bs ∗ Frame) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28
  have hrecomp := States.Leaves.relocatedHeap_recompose F bs dst
  have hsrc : (src ↦ₛ bs) ⊢ memRegion src n := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion src bs
  refine SepWP.weaken_pre ?_
    (hnext sf hpc_sf hrun_sf hsp_sf htr_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28)
  refine Entails.trans (Entails.of_eq (show
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (States.Leaves.relocatedHeap F bs ∗ Frame) =
    (((dst ↦ₛ bs) ∗ States.Leaves.relocatedHeap F bs) ∗ (src ↦ₛ bs)) ∗ Frame by ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono hrecomp hsrc)

/-! ## 2. `PqRatchetState` Copy and Assembly (`+4096 -> +4288 / +4364`) -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 3. Bridge 2 Composition (`+4000 -> +6216`) -/

end CryptoVerification.SpqrV1.Top.Send
