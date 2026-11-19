/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Shard 3

Kernel-checked `dagNodeOk` certificates (`certRangeOk_3`) for receive-DAG nodes `5040 ≤ id < 6720`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert3

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk certRangeOk_trans dagNodeOk_of_certRangeOk)

private theorem s0 : certRangeOk 5040 5100 = true := by decide +kernel
private theorem s1 : certRangeOk 5100 5160 = true := by decide +kernel
private theorem s2 : certRangeOk 5160 5220 = true := by decide +kernel
private theorem s3 : certRangeOk 5220 5280 = true := by decide +kernel
private theorem s4 : certRangeOk 5280 5340 = true := by decide +kernel
private theorem s5 : certRangeOk 5340 5400 = true := by decide +kernel
private theorem s6 : certRangeOk 5400 5460 = true := by decide +kernel
private theorem s7 : certRangeOk 5460 5520 = true := by decide +kernel
private theorem s8 : certRangeOk 5520 5580 = true := by decide +kernel
private theorem s9 : certRangeOk 5580 5640 = true := by decide +kernel
private theorem s10 : certRangeOk 5640 5700 = true := by decide +kernel
private theorem s11 : certRangeOk 5700 5760 = true := by decide +kernel
private theorem s12 : certRangeOk 5760 5820 = true := by decide +kernel
private theorem s13 : certRangeOk 5820 5880 = true := by decide +kernel
private theorem s14 : certRangeOk 5880 5940 = true := by decide +kernel
private theorem s15 : certRangeOk 5940 6000 = true := by decide +kernel
private theorem s16 : certRangeOk 6000 6060 = true := by decide +kernel
private theorem s17 : certRangeOk 6060 6120 = true := by decide +kernel
private theorem s18 : certRangeOk 6120 6180 = true := by decide +kernel
private theorem s19 : certRangeOk 6180 6240 = true := by decide +kernel
private theorem s20 : certRangeOk 6240 6300 = true := by decide +kernel
private theorem s21 : certRangeOk 6300 6360 = true := by decide +kernel
private theorem s22 : certRangeOk 6360 6420 = true := by decide +kernel
private theorem s23 : certRangeOk 6420 6480 = true := by decide +kernel
private theorem s24 : certRangeOk 6480 6540 = true := by decide +kernel
private theorem s25 : certRangeOk 6540 6600 = true := by decide +kernel
private theorem s26 : certRangeOk 6600 6660 = true := by decide +kernel
private theorem s27 : certRangeOk 6660 6720 = true := by decide +kernel

private theorem shard_3 : certRangeOk 5040 6720 = true :=
  (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans s0 s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19) s20) s21) s22) s23) s24) s25) s26) s27)

theorem certRangeOk_3 {id : Nat} (hlo : 5040 ≤ id) (hhi : id < 6720) :
    dagNodeOk dagOp dagBytes id = true :=
  dagNodeOk_of_certRangeOk shard_3 hlo hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert3
