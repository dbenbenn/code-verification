/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.NonVacuity.CliSatisfiable
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.BugInjection.Synthetic.Witnesses.DecryptCloneNotPersistedCli
public import Symbolic.BugInjection.Synthetic.Witnesses.SignalMsgCanonicalMacCli

/-!
# Pinned `fits` Predicate and Satisfiability under `(compI7003, compHooks7003)`

Defines `compFitsPinned7003` and `cliCompFitsPinned7003` (the proof-layer pinned `fits` predicates
for receive-path synthetic mutant witnesses recorded at `setup_seed = 7003`) and proves
`cliCompFitsPinned7003_satisfiable` for both `DecryptCloneNotPersistedCli.setup` and
`SignalMsgCanonicalMacCli.setup`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.BugInjection
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws

/-- Pinned `fits` of a `CompRefines` witness under `compI7003` (proof layer only). -/
def compFitsPinned7003 (w : PQXDHSpqrSetup) (i : ExternInterpretation) (r : ProtocolSetup) : Prop :=
  SetupMatches w i r ∧ i = compI7003 ∧
    (secretBytes r 3 = fillFresh 11 64 ∧ secretBytes r 4 = fillFresh 16 64 ∧
      secretBytes r 5 = fillFresh 17 64) ∧
    (r.alice = "alice" ∧ r.bob = "bob") ∧
    DY.Libsignal.PQXDH.Refinement.X25519TorsionShiftsRejected i ∧
    TorsionShiftsRecorded i w.torsionShifts

/-- Pinned `fits` predicate for `CompRefinesCliElf` witnesses under `(compI7003, compHooks7003)`. -/
def cliCompFitsPinned7003 (w : PQXDHSpqrSetup)
    (iw : ExternInterpretation × CryptoVerification.SignalSession.CliHooks)
    (r : ProtocolSetup) : Prop :=
  compFitsPinned7003 w iw.1 r ∧
    ExternContractsHoldCli iw.1 ∧
    HooksMatchInterpretation iw.1 iw.2

/-- Concrete `ProtocolSetup` of a witness setup `w` evaluated under `compI7003`. -/
def compRecordsI7003 (w : PQXDHSpqrSetup) : ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := false, regIdA := w.regIdA, regIdB := w.regIdB,
    spkId := w.spkId, kpkId := w.kpkId, opkId := 0, kyberSecB := w.kyberSec, fresh := w.fresh,
    opaqueBytes := gamma compI7003 w.compSem w.compGhost }

theorem compI7003_gamma_randTerm_pos (w : PQXDHSpqrSetup) (i n : Nat) (hn : n ≠ 0) :
    gamma compI7003 w.compSem w.compGhost (randTerm i n) = w.compGhost.σ i n := by
  unfold gamma gamma'
  conv => lhs; unfold randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom w.compGhost) (concretizeAll compI7003 w.compSem w.compGhost)]
  simp only [concretizeRandom, hn, ite_false]
  rfl

theorem compI7003_gamma_kemPk (w : PQXDHSpqrSetup) (sk : DY.Bytes) :
    gamma compI7003 w.compSem w.compGhost (DY.PQKem.kemPk sk) =
      w.compSem.kemPk (gamma compI7003 w.compSem w.compGhost sk) := by
  unfold gamma gamma'
  show ((({sk} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk w.compSem) (concretizeAll compI7003 w.compSem w.compGhost)]
  rfl

theorem compI7003_gamma_sign (w : PQXDHSpqrSetup) (sk n m : DY.Bytes) :
    gamma compI7003 w.compSem w.compGhost (DY.Signature.sign sk n m) =
      w.compSem.sign
        (gamma compI7003 w.compSem w.compGhost sk)
        (gamma compI7003 w.compSem w.compGhost n)
        (gamma compI7003 w.compSem w.compGhost m) := by
  unfold gamma gamma'
  show ((({sk, nonce := n, msg := m} : DY.Signature.Sign.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign w.compSem) (concretizeAll compI7003 w.compSem w.compGhost)]
  rfl

theorem compRecordsI7003_ne (w : PQXDHSpqrSetup) :
    (compRecordsI7003 w).alice ≠ (compRecordsI7003 w).bob := by
  show ("alice" : String) ≠ "bob"; decide

theorem compRecordsI7003_randomsAt (w : PQXDHSpqrSetup) :
    setupRandomsAt (compRecordsI7003 w) =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq (compRecordsI7003 w) (compRecordsI7003_ne w)]
  rfl

theorem compRecordsI7003_public (w : PQXDHSpqrSetup) :
    setupPublic (compRecordsI7003 w) 5 =
      DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
        (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))) ∧
    setupPublic (compRecordsI7003 w) 6 =
      DY.PQKem.kemPk (randTerm 16 64) ∧
    setupPublic (compRecordsI7003 w) 7 =
      DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
        (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64))) :=
  ⟨Symbolic.Swarm.CREF.b1_setupPublic_5 (compRecordsI7003 w) (compRecordsI7003_ne w),
   Symbolic.Swarm.CREF.b1_setupPublic_6 (compRecordsI7003 w) (compRecordsI7003_ne w),
   Symbolic.Swarm.CREF.b1_setupPublic_7 (compRecordsI7003 w) (compRecordsI7003_ne w)⟩

/-- Any plausible witness setup whose torsion shifts are recorded in `compI7003` satisfies
`cliCompFitsPinned7003` under `(compI7003, compHooks7003)` and `compRecordsI7003 w`. -/
theorem cliCompFitsPinned7003_satisfiable_of_plausible (w : PQXDHSpqrSetup)
    (hw : w.withOpk = false)
    (h : w.Plausible) (htor : TorsionShiftsRecorded compI7003 w.torsionShifts) :
    ∃ iw r, cliCompFitsPinned7003 w iw r := by
  obtain ⟨ha, hb, hs, hss, hk, hks, hsec, hslice, hnd, _, _⟩ := h
  obtain ⟨h5, h6, h7⟩ := compRecordsI7003_public w
  have hR := compRecordsI7003_randomsAt w
  have o5 : (compRecordsI7003 w).opaqueBytes (setupPublic (compRecordsI7003 w) 5) = w.spkSig := by
    rw [h5]
    show gamma compI7003 w.compSem w.compGhost _ = _
    rw [compI7003_gamma_sign]
    show (if gamma compI7003 w.compSem w.compGhost (randTerm 11 64) = fillFresh 11 64
      then _ else _) = _
    rw [compI7003_gamma_randTerm_pos w 11 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh]
  have o6 : (compRecordsI7003 w).opaqueBytes (setupPublic (compRecordsI7003 w) 6) = w.kyberPk := by
    rw [h6]
    show gamma compI7003 w.compSem w.compGhost _ = _
    rw [compI7003_gamma_kemPk]; rfl
  have o7 : (compRecordsI7003 w).opaqueBytes (setupPublic (compRecordsI7003 w) 7) = w.kyberPkSig := by
    rw [h7]
    show gamma compI7003 w.compSem w.compGhost _ = _
    rw [compI7003_gamma_sign]
    show (if gamma compI7003 w.compSem w.compGhost (randTerm 17 64) = fillFresh 11 64
      then _ else _) = _
    rw [compI7003_gamma_randTerm_pos w 17 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh, fillFresh_ne_11_17]
  have hwf : ProtocolSetupWF (compRecordsI7003 w) := by
    refine ⟨compRecordsI7003_ne w, ?_, ?_, ?_, ?_, ?_, hsec, ?_⟩
    · rw [hR]
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [compRecordsI7003, PQXDHSpqrSetup.fresh, fillFresh, ha, hb, hs]
    · rw [hR]
      simpa [hw, compRecordsI7003, PQXDHSpqrSetup.fresh] using hnd
    · exact (congrArg List.length o5).trans hss
    · exact (congrArg List.length o6).trans hk
    · exact (congrArg List.length o7).trans hks
    · exact hslice.trans o6.symm
  have hs0 : secretBytes (compRecordsI7003 w) 0 = w.aliceId := by
    rw [secretBytes, hR]; simp [compRecordsI7003, PQXDHSpqrSetup.fresh]
  have hs1 : secretBytes (compRecordsI7003 w) 1 = w.bobId := by
    rw [secretBytes, hR]; simp [compRecordsI7003, PQXDHSpqrSetup.fresh]
  have hs2 : secretBytes (compRecordsI7003 w) 2 = w.spk := by
    rw [secretBytes, hR]; simp [compRecordsI7003, PQXDHSpqrSetup.fresh]
  have hs3 : secretBytes (compRecordsI7003 w) 3 = fillFresh 11 64 := by
    rw [secretBytes, hR]; simp [compRecordsI7003, PQXDHSpqrSetup.fresh]
  have hs4 : secretBytes (compRecordsI7003 w) 4 = fillFresh 16 64 := by
    rw [secretBytes, hR]; simp [compRecordsI7003, PQXDHSpqrSetup.fresh]
  have hs5 : secretBytes (compRecordsI7003 w) 5 = fillFresh 17 64 := by
    rw [secretBytes, hR]; simp [compRecordsI7003, PQXDHSpqrSetup.fresh]
  have hopk_fit :
      (match w.withOpk with
       | false => (compRecordsI7003 w).withOpk = false
       | true =>
         (compRecordsI7003 w).withOpk = true ∧ (compRecordsI7003 w).opkId = w.opkId ∧
           secretBytes (compRecordsI7003 w) 6 = w.opk) := by
    rw [hw]; rfl
  exact ⟨(compI7003, compHooks7003), compRecordsI7003 w,
    ⟨⟨hwf, hopk_fit, rfl, rfl, rfl, rfl, hs0, hs1, hs2, o5, o6, o7, rfl,
      compI7003_cryptoEquationsHold, compI7003_pubCanonical,
      compI7003_kyberCorrectOn (compRecordsI7003 w) w.kyberCts⟩,
     rfl, ⟨hs3, hs4, hs5⟩, ⟨rfl, rfl⟩,
     compI7003_torsionShiftsRejected, htor⟩,
    compI7003_externContractsHoldCli, compI7003_hooksMatch⟩

theorem cliCompFitsPinned7003_satisfiable_decryptCloneNotPersisted :
    ∃ iw r, cliCompFitsPinned7003 Synthetic.Witnesses.DecryptCloneNotPersistedCli.setup iw r :=
  cliCompFitsPinned7003_satisfiable_of_plausible
    Synthetic.Witnesses.DecryptCloneNotPersistedCli.setup
    rfl
    (by decide +kernel)
    (fun _ h => nomatch h)

theorem cliCompFitsPinned7003_satisfiable_signalMsgCanonicalMac :
    ∃ iw r, cliCompFitsPinned7003 Synthetic.Witnesses.SignalMsgCanonicalMacCli.setup iw r :=
  cliCompFitsPinned7003_satisfiable_of_plausible
    Synthetic.Witnesses.SignalMsgCanonicalMacCli.setup
    rfl
    (by decide +kernel)
    (fun _ h => nomatch h)

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003
