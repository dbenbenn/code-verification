/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Shard 1

Kernel-checked `dagNodeOk` certificates (`certRangeOk_1`) for receive-DAG nodes `1680 ≤ id < 3360`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert1

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk certRangeOk_trans dagNodeOk_of_certRangeOk)

private theorem s0 : certRangeOk 1680 1740 = true := by decide +kernel
private theorem s1 : certRangeOk 1740 1800 = true := by decide +kernel
private theorem s2 : certRangeOk 1800 1860 = true := by decide +kernel
private theorem s3 : certRangeOk 1860 1920 = true := by decide +kernel
private theorem s4 : certRangeOk 1920 1980 = true := by decide +kernel
private theorem s5 : certRangeOk 1980 2040 = true := by decide +kernel
private theorem s6 : certRangeOk 2040 2100 = true := by decide +kernel
private theorem s7 : certRangeOk 2100 2160 = true := by decide +kernel
private theorem s8 : certRangeOk 2160 2220 = true := by decide +kernel
private theorem s9 : certRangeOk 2220 2280 = true := by decide +kernel
private theorem s10 : certRangeOk 2280 2340 = true := by decide +kernel
private theorem s11 : certRangeOk 2340 2400 = true := by decide +kernel
private theorem s12 : certRangeOk 2400 2460 = true := by decide +kernel
private theorem s13 : certRangeOk 2460 2520 = true := by decide +kernel
private theorem s14 : certRangeOk 2520 2580 = true := by decide +kernel
private theorem s15 : certRangeOk 2580 2640 = true := by decide +kernel
private theorem s16 : certRangeOk 2640 2700 = true := by decide +kernel
private theorem s17 : certRangeOk 2700 2760 = true := by decide +kernel
private theorem s18 : certRangeOk 2760 2820 = true := by decide +kernel
private theorem s19 : certRangeOk 2820 2880 = true := by decide +kernel
private theorem s20 : certRangeOk 2880 2940 = true := by decide +kernel
private theorem s21 : certRangeOk 2940 3000 = true := by decide +kernel
private theorem s22 : certRangeOk 3000 3060 = true := by decide +kernel
private theorem s23 : certRangeOk 3060 3120 = true := by decide +kernel
private theorem s24 : certRangeOk 3120 3180 = true := by decide +kernel
private theorem s25 : certRangeOk 3180 3240 = true := by decide +kernel
private theorem s26 : certRangeOk 3240 3300 = true := by decide +kernel
private theorem s27 : certRangeOk 3300 3360 = true := by decide +kernel

private theorem shard_1 : certRangeOk 1680 3360 = true :=
  (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans s0 s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19) s20) s21) s22) s23) s24) s25) s26) s27)

theorem certRangeOk_1 {id : Nat} (hlo : 1680 ≤ id) (hhi : id < 3360) :
    dagNodeOk dagOp dagBytes id = true :=
  dagNodeOk_of_certRangeOk shard_1 hlo hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert1
