/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Shard 2

Kernel-checked `dagNodeOk` certificates (`certRangeOk_2`) for receive-DAG nodes `3360 ≤ id < 5040`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert2

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk certRangeOk_trans dagNodeOk_of_certRangeOk)

private theorem s0 : certRangeOk 3360 3420 = true := by decide +kernel
private theorem s1 : certRangeOk 3420 3480 = true := by decide +kernel
private theorem s2 : certRangeOk 3480 3540 = true := by decide +kernel
private theorem s3 : certRangeOk 3540 3600 = true := by decide +kernel
private theorem s4 : certRangeOk 3600 3660 = true := by decide +kernel
private theorem s5 : certRangeOk 3660 3720 = true := by decide +kernel
private theorem s6 : certRangeOk 3720 3780 = true := by decide +kernel
private theorem s7 : certRangeOk 3780 3840 = true := by decide +kernel
private theorem s8 : certRangeOk 3840 3900 = true := by decide +kernel
private theorem s9 : certRangeOk 3900 3960 = true := by decide +kernel
private theorem s10 : certRangeOk 3960 4020 = true := by decide +kernel
private theorem s11 : certRangeOk 4020 4080 = true := by decide +kernel
private theorem s12 : certRangeOk 4080 4140 = true := by decide +kernel
private theorem s13 : certRangeOk 4140 4200 = true := by decide +kernel
private theorem s14 : certRangeOk 4200 4260 = true := by decide +kernel
private theorem s15 : certRangeOk 4260 4320 = true := by decide +kernel
private theorem s16 : certRangeOk 4320 4380 = true := by decide +kernel
private theorem s17 : certRangeOk 4380 4440 = true := by decide +kernel
private theorem s18 : certRangeOk 4440 4500 = true := by decide +kernel
private theorem s19 : certRangeOk 4500 4560 = true := by decide +kernel
private theorem s20 : certRangeOk 4560 4620 = true := by decide +kernel
private theorem s21 : certRangeOk 4620 4680 = true := by decide +kernel
private theorem s22 : certRangeOk 4680 4740 = true := by decide +kernel
private theorem s23 : certRangeOk 4740 4800 = true := by decide +kernel
private theorem s24 : certRangeOk 4800 4860 = true := by decide +kernel
private theorem s25 : certRangeOk 4860 4920 = true := by decide +kernel
private theorem s26 : certRangeOk 4920 4980 = true := by decide +kernel
private theorem s27 : certRangeOk 4980 5040 = true := by decide +kernel

private theorem shard_2 : certRangeOk 3360 5040 = true :=
  (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans s0 s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19) s20) s21) s22) s23) s24) s25) s26) s27)

theorem certRangeOk_2 {id : Nat} (hlo : 3360 ≤ id) (hhi : id < 5040) :
    dagNodeOk dagOp dagBytes id = true :=
  dagNodeOk_of_certRangeOk shard_2 hlo hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert2
