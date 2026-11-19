/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtEncryptBody -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import LibsignalBinary.Proofs.SpqrV1.Drop.States1a
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.TopDecodes
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.Core
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCtPkEq
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtGenKeysMac
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacX
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSignalMsgNew
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSpqrSendEmpty
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.Wire.New
import LibsignalBinary.Proofs.SpqrV1.M4.Encrypt -- shake: keep

/-!
# CLI SPQR V1 `OutgoingTripleRatchet::encrypt` Assembly

Threads spatial frames and pure state/tape predicates through `spqr::send` to prove
`OutgoingTripleRatchet::encrypt::<Coins>` against `otrEncryptSpecT` across fixed-table,
`trTrapProgAt`, and `tripleRatchetProgAtExt` programs.
-/

public section

namespace CryptoVerification.LibsignalSpqrV1.M4

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalTripleRatchet.Encrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem h43a_except_ok_eq_error {α ε : Type _} (x : α) (e : ε) :
    ((Except.ok x : Except ε α) = Except.error e) = False := by simp

private theorem h43a_except_ok_ne_error_eq_true {α ε : Type _} (x : α) (e : ε) :
    ((Except.ok x : Except ε α) ≠ Except.error e) = True := by simp

attribute [local arm64_norm] h43a_except_ok_eq_error h43a_except_ok_ne_error_eq_true

private theorem h43a_subroutine_ok_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {Qpre : α → State → SepProp} {F : SepProp}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ (Qpre x s0 ∗ F ∗ spec.pre x s0) ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R))) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry
      { spec with
        pre := fun x s => Qpre x s ∗ F ∗ spec.pre x s
        post := fun x s0 sf => F ∗ spec.post x s0 sf } := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  refine ⟨P, Fr, hm, ?_⟩
  have hcomm : ∀ sf, (F ∗ spec.post x s0 sf) ∗ R = spec.post x s0 sf ∗ (F ∗ R) := fun sf => by ac_rfl
  simp only [hcomm]
  exact hwp

private theorem h43a_absorb_frame {prog : Program} {ret : BitVec 64} {s : State}
    {F P R : SepProp} {Ψ φ_pan : State → Prop} {sp0 : BitVec 64} {s0 : State}
    (h : SepWPp prog ret s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ (F ∗ R)) → Ψ sf) ∧
        sf.sp = sp0 ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F ∗ R)) → (φ_pan sf ∧ sf.mem ⊨ anyHeap ∗ (F ∗ R)))) :
    SepWPp prog ret s (F ∗ P)
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → Ψ sf) ∧
        sf.sp = sp0 ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (φ_pan sf ∧ sf.mem ⊨ anyHeap ∗ R)) := by
  intro R' hm hL
  have hm' : s.mem ⊨ P ∗ (F ∗ R') := by
    have heq : (F ∗ P) ∗ R' = P ∗ (F ∗ R') := by ac_rfl
    exact heq ▸ hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hfalse⟩⟩ :=
    h (F ∗ R') hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, F ∗ P_f, ?_, ⟨?_, hsp, hcs⟩⟩⟩
    · have heq : P_f ∗ (F ∗ R') = (F ∗ P_f) ∗ R' := by ac_rfl
      exact heq ▸ hmf
    · intro hmR
      have heq : (F ∗ P_f) ∗ R = P_f ∗ (F ∗ R) := by ac_rfl
      exact hq (heq ▸ hmR)
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, F ∗ P_f, ?_, ?_⟩)⟩
    · have heq : P_f ∗ (F ∗ R') = (F ∗ P_f) ∗ R' := by ac_rfl
      exact heq ▸ hmf
    · intro hmR
      have heq : (F ∗ P_f) ∗ R = P_f ∗ (F ∗ R) := by ac_rfl
      obtain ⟨hφ, hany⟩ := hqp (heq ▸ hmR)
      refine ⟨hφ, ?_⟩
      rw [← sepConj_assoc] at hany
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hany
  · exact (not_satisfies_false_sepConj hfalse).elim

open CryptoVerification.LibsignalSpqrV1 (MlKem SpqrHooks spqrV1)

end CryptoVerification.LibsignalSpqrV1.M4
