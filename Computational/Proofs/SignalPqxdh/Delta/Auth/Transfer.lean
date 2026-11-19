/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
import VCVio.EvalDist.Monad.Basic
import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB3

/-!
# PQXDH δ authentication: transfer of the KEM correctness bad event

**Checked by Lean.** Proves `authCorrTransfer` (`AuthCorrTransferStmt`, DEV-PQ21), bounding
`hasBadAuthKemCorr` in `runAuthSendLatchedSim .g3` by `hasBadKemCorrRecords` in `runAuthShCrSim`.
-/

public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

private theorem at_hasBadAuthKemCorr_imp_hasBadKemCorrRecords {S : Setup} (P : Primitives)
    (hst : AuthHybridShCrState S) (hV : ValidHybridShCr S hst)
    (hSend : hst.sendCount ≤ S.N_send_tot)
    (hBad : hasBadAuthKemCorr P hst.base = true) :
    hasBadKemCorrRecords S P hst.initKemRecs hst.recvKemRecs = true := by
  unfold hasBadAuthKemCorr at hBad
  rw [List.any_eq_true] at hBad; rcases hBad with ⟨i, hi, hBadR⟩; rw [List.any_eq_true] at hBadR
  rcases hBadR with ⟨r, hr, hPred⟩; rcases hV.1 i hi with ⟨i', hi', rfl, hiLt⟩
  rcases hV.2 r hr with ⟨r', hr', rfl, hrLt⟩
  have hPred' : isKemCorrPair P i' r' = true := hPred
  have hiTot : i'.sendIdx < S.N_send_tot := Nat.lt_of_lt_of_le hiLt hSend
  have hPos : 0 < S.N_send_tot := Nat.pos_of_ne_zero (by omega)
  let idx := r'.bIdx * S.N_send_tot + i'.sendIdx
  have hIdxLt : idx < S.N_spk_tot * S.N_send_tot := by
    dsimp [idx]
    calc r'.bIdx * S.N_send_tot + i'.sendIdx
        < r'.bIdx * S.N_send_tot + S.N_send_tot := Nat.add_lt_add_left hiTot _
      _ = (r'.bIdx + 1) * S.N_send_tot := by ring
      _ ≤ S.N_spk_tot * S.N_send_tot := Nat.mul_le_mul_right _ hrLt
  have hDiv : idx / S.N_send_tot = r'.bIdx := by
    dsimp [idx]; rw [Nat.mul_comm, Nat.mul_add_div hPos, Nat.div_eq_of_lt hiTot, Nat.add_zero]
  have hMod : idx % S.N_send_tot = i'.sendIdx := by
    dsimp [idx]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hiTot]
  unfold hasBadKemCorrRecords; rw [List.any_eq_true]
  refine ⟨idx, List.mem_range.mpr hIdxLt, ?_⟩
  unfold hasBadKemCorrRecordsAt
  rw [hDiv, hMod, List.any_eq_true]; refine ⟨i', hi', ?_⟩
  simp only [beq_self_eq_true, Bool.true_and, List.any_eq_true]; exact ⟨r', hr', by simp [hPred']⟩

end Proofs.SignalPqxdh.Security.PqxdhDelta
