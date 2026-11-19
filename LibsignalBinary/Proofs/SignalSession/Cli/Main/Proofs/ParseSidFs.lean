/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# In-Image `ServiceId::parse_from_service_id_string` Preserving `fs` (`Spec.keepsFs`)

Proves `ServiceId::parse_from_service_id_string` satisfies
`(parseSidCodeStackSpec hookStack).keepsFs.inImage img` for any `hookStack ≥ uuidTryParseStack`,
deriving `hookStack ≤ 2 ^ 64` from stack-frame disjointness, plus call-site offset forms.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ParseServiceId
open CryptoVerification.SignalSession.Cli.MainHops.UuidFs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_local (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

private theorem hookStack_le_of_frame_disjoint {m : Memory} {sp : BitVec 64} {hookStack : Nat}
    {R : SepProp}
    (hm : m ⊨ stackAt (sp - 80#64) hookStack ∗ stackAt sp parseSidFrameStack ∗ R) :
    hookStack ≤ 2 ^ 64 := by
  by_cases h0 : hookStack = 0
  · omega
  · have hm' :
        m ⊨ memRegion (sp - 80#64) 80 ∗
          (memRegion ((sp - 80#64) - BitVec.ofNat 64 hookStack) hookStack ∗ R) := by
      dsimp only [stackAt, parseSidFrameStack] at hm
      ac_nf at hm ⊢
    have hd := disjointRegions_of_coversRegion (by decide) (Nat.pos_of_ne_zero h0)
      (IsBlock.memRegion (sp - 80#64) 80).covers
      (IsBlock.memRegion ((sp - 80#64) - BitVec.ofNat 64 hookStack) hookStack).covers
      hm'
    have hlt1 := (((sp - 80#64) - BitVec.ofNat 64 hookStack) - (sp - 80#64)).isLt
    have hlt2 := ((sp - 80#64) - ((sp - 80#64) - BitVec.ofNat 64 hookStack)).isLt
    have h1 := hd.1
    have h2 := hd.2
    omega

end CryptoVerification.SignalSession.Cli.MainHops
