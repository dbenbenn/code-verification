/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.FnPtr
public import ProofLib.SepLogic.WP

/-!
# Function-Pointer Hoare Logic Tests

Unit and regression tests for `FnPtrSpec`, `SafeFnPtrSpec`, `wp_blr_of_fnPtrSpec`, and
`wp_br_of_fnPtrSpec`.
-/

@[expose] public section

namespace ProofLib.Tests.FnPtr

open Arm64 ProofLib

theorem wp_blr_and_br_smoke {prog : Program} {s : State} {spec : Spec Unit} {P : SepProp}
    {post : State → SepProp → Prop}
    (hfn : FnPtrSpec prog (s.readReg64 .x8) spec)
    (hpc : s.pc = 0x2000#64) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hfetch : prog.fetch 0x2000#64 = some (.blr .x8))
    (hpre : ∀ R, s.mem ⊨ P ∗ R →
      s.mem ⊨ spec.pre () ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) ∗ (emp ∗ R))
    (hnopan : ∀ R' sf, sf.status = .Panicked →
      ¬(sf.mem ⊨ spec.onPanic () ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) sf ∗ R'))
    (hnoex : ∀ R' code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit () code ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) sf ∗ R'))
    (hnooom : ∀ R' sf, sf.status = .OutOfMemory →
      ¬(sf.mem ⊨ spec.onOom () ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) sf ∗ R'))
    (hcont : ∀ sf, sf.pc = 0x2004#64 → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog 0x2008#64 sf (spec.post () ((s.writeReg64 Reg.lr 0x2004#64).setPC (s.readReg64 .x8)) sf ∗ emp) post) :
    SepWP prog 0x2008#64 s P post :=
  wp_blr_of_fnPtrSpec hfn hpc hrun halign hfetch hpre hnopan hnoex hcont
    (fun R sf hst ho => False.elim (hnooom (emp ∗ R) sf hst ho))

end ProofLib.Tests.FnPtr
