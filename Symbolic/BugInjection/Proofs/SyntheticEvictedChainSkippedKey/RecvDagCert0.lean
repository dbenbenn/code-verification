/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

/-!
# Per-Node DAG Certificate Shard 0

Kernel-checked `dagNodeOk` certificates (`certRangeOk_0`) for receive-DAG nodes `0 ≤ id < 1680`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert0

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagOp dagBytes certRangeOk certRangeOk_trans dagNodeOk_of_certRangeOk)

private theorem s0 : certRangeOk 0 60 = true := by decide +kernel
private theorem s1 : certRangeOk 60 120 = true := by decide +kernel
private theorem s2 : certRangeOk 120 180 = true := by decide +kernel
private theorem s3 : certRangeOk 180 240 = true := by decide +kernel
private theorem s4 : certRangeOk 240 300 = true := by decide +kernel
private theorem s5 : certRangeOk 300 360 = true := by decide +kernel
private theorem s6 : certRangeOk 360 420 = true := by decide +kernel
private theorem s7 : certRangeOk 420 480 = true := by decide +kernel
private theorem s8 : certRangeOk 480 540 = true := by decide +kernel
private theorem s9 : certRangeOk 540 600 = true := by decide +kernel
private theorem s10 : certRangeOk 600 660 = true := by decide +kernel
private theorem s11 : certRangeOk 660 720 = true := by decide +kernel
private theorem s12 : certRangeOk 720 780 = true := by decide +kernel
private theorem s13 : certRangeOk 780 840 = true := by decide +kernel
private theorem s14 : certRangeOk 840 900 = true := by decide +kernel
private theorem s15 : certRangeOk 900 960 = true := by decide +kernel
private theorem s16 : certRangeOk 960 1020 = true := by decide +kernel
private theorem s17 : certRangeOk 1020 1080 = true := by decide +kernel
private theorem s18 : certRangeOk 1080 1140 = true := by decide +kernel
private theorem s19 : certRangeOk 1140 1200 = true := by decide +kernel
private theorem s20 : certRangeOk 1200 1260 = true := by decide +kernel
private theorem s21 : certRangeOk 1260 1320 = true := by decide +kernel
private theorem s22 : certRangeOk 1320 1380 = true := by decide +kernel
private theorem s23 : certRangeOk 1380 1440 = true := by decide +kernel
private theorem s24 : certRangeOk 1440 1500 = true := by decide +kernel
private theorem s25 : certRangeOk 1500 1560 = true := by decide +kernel
private theorem s26 : certRangeOk 1560 1620 = true := by decide +kernel
private theorem s27 : certRangeOk 1620 1680 = true := by decide +kernel

private theorem shard_0 : certRangeOk 0 1680 = true :=
  (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans (certRangeOk_trans s0 s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19) s20) s21) s22) s23) s24) s25) s26) s27)

theorem certRangeOk_0 {id : Nat} (hlo : 0 ≤ id) (hhi : id < 1680) :
    dagNodeOk dagOp dagBytes id = true :=
  dagNodeOk_of_certRangeOk shard_0 hlo hhi

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert0
