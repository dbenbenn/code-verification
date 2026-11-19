/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanVis
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Clean Ghost Construction, `GhostWF`, and Public-Key/Kyber Evaluation (`CleanGhost.lean`)

1. Unpacks `keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r` (`r_facts_of_fit`, `setupRandomsAt_of_fit`).
2. Defines the canonical clean `Ghost` `gClean r cls` aligned with `ssClean cls 5` (`0` whisper sends,
   so `addr := fun _ => pqAddrBytes`).
3. Proves `ghostAndSemMatchSetup_gClean` and `ghostWF_visClean` (`m ≤ 5`, `ValidCoinLens cls`).
4. Evaluates all 10 honest X25519 public keys and Kyber encapsulations under `keepOpkI0` and `gClean r cls`,
   and discharges `¬ KyberMismatch keepOpkI0 r p` and `¬ ImplicitReject r (cleanPreKeyRep cls k)` (`k ∈ {2, 5}`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost

open scoped DY.Libsignal.Composed
open DY (Bytes)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk kemEncap kemDecap)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (errToOption)
open DY.Libsignal.Refinement (x25519PublicKeySymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry PreKeyFields
   gamma gamma' concretizeAll concretizeKemPk concretizeSign clamp slice ecKey kyberKey
   randTerm rngEntry kyberCoinEntries setupRandomsAt setupPublic setupSecret secretBytes
   GhostAndSemMatchSetup GhostWF KyberMismatch stepView runTrace runWrapped)
open DY.Libsignal.Composed.Refinement.Cli (serializeAddresses aliceUuid bobUuid)
open Symbolic.BugInjection (fillFresh)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd kemDecap_kemEncap)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (t4Opk t5Opk pqskB oOpk t4Opk_length t7Opk_length)
open Symbolic.Swarm.CREF.TR (gamma_rand gamma_litByte gamma_concat gamma_dhPk gamma_kemEncap_fst)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0 keepOpkCompFitsPinned keepOpkSecretIdx keepOpkPubOfIdx
   keepOpkPubOfOpt keepOpkLookupPub keepOpkKyberEncaps keepOpkKyberCt0 keepOpkKyberCt0_length
   keepOpkKyberCt1 keepOpkKyberCt1_length)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws
  (keepOpkI0_publicKey keepOpkI0_kyberEncaps keepOpkI0_kyberCorrectOn
   keepOpkPointIdx_keepOpkPubOfOpt)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
  (w0 ev ev0In_eq ev0Coins_eq ev1Coins_eq ev2Coins_eq ev3Coins_eq ev4Coins_eq ev5Coins_eq
   ev0KyberEnt ev0KyberEnt_eq ev3KyberEnt ev3KyberEnt_eq
   ev0_coins_base ev3_coins_base ev1_facts ev2_facts ev4_facts)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace
  (ValidCoinLens cleanCallSteps ssClean s0Clean s1Clean s2Clean s3Clean s4Clean
   trClean2 trClean3 trClean4 o2Clean cleanPreKeyRep runTrace_ssClean_eqs setupSecret_eqs)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanVis
  (visOfSteps visClean visClean_succ stepView_s0 stepView_s1 stepView_s2 stepView_s3 stepView_s4)

attribute [local irreducible] WitnessParse.ev

/-! ## 1. Unpacking `keepOpkCompFitsPinned` -/

structure FitFacts (r : ProtocolSetup) : Prop where
  alice_eq : r.alice = "alice"
  bob_eq : r.bob = "bob"
  withOpk_eq : r.withOpk = true
  opkId_eq : r.opkId = 3#32
  spkId_eq : r.spkId = 7#32
  kpkId_eq : r.kpkId = 9#32
  regIdA_eq : r.regIdA = w0.regIdA
  regIdB_eq : r.regIdB = w0.regIdB
  sec0_eq : secretBytes r 0 = w0.aliceId
  sec1_eq : secretBytes r 1 = w0.bobId
  sec2_eq : secretBytes r 2 = w0.spk
  sec3_eq : secretBytes r 3 = fillFresh 11 64
  sec4_eq : secretBytes r 4 = fillFresh 16 64
  sec5_eq : secretBytes r 5 = fillFresh 17 64
  sec6_eq : secretBytes r 6 = w0.opk
  pub5_eq : r.opaqueBytes (setupPublic r 5) = w0.spkSig
  pub6_eq : r.opaqueBytes (setupPublic r 6) = w0.kyberPk
  pub7_eq : r.opaqueBytes (setupPublic r 7) = w0.kyberPkSig
  kyberSec_eq : r.kyberSecB = w0.kyberSec

theorem r_facts_of_fit {r : ProtocolSetup}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r) : FitFacts r where
  alice_eq := hfit.1.2.2.2.1.1
  bob_eq := hfit.1.2.2.2.1.2
  withOpk_eq := hfit.1.1.2.1.1
  opkId_eq := hfit.1.1.2.1.2.1
  spkId_eq := hfit.1.1.2.2.2.2.1
  kpkId_eq := hfit.1.1.2.2.2.2.2.1
  regIdA_eq := hfit.1.1.2.2.1
  regIdB_eq := hfit.1.1.2.2.2.1
  sec0_eq := hfit.1.1.2.2.2.2.2.2.1
  sec1_eq := hfit.1.1.2.2.2.2.2.2.2.1
  sec2_eq := hfit.1.1.2.2.2.2.2.2.2.2.1
  sec3_eq := hfit.1.2.2.1.1
  sec4_eq := hfit.1.2.2.1.2.1
  sec5_eq := hfit.1.2.2.1.2.2
  sec6_eq := hfit.1.1.2.1.2.2
  pub5_eq := hfit.1.1.2.2.2.2.2.2.2.2.2.1
  pub6_eq := hfit.1.1.2.2.2.2.2.2.2.2.2.2.1
  pub7_eq := hfit.1.1.2.2.2.2.2.2.2.2.2.2.2.1
  kyberSec_eq := hfit.1.1.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem setupRandomsAt_of_fit {r : ProtocolSetup}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r) :
    setupRandomsAt r = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64), (22, 32)] := by
  have hf := r_facts_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hf.alice_eq, hf.bob_eq]; decide
  have h := Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe
  rw [hf.withOpk_eq] at h
  simpa using h

/-! ## 2. Clean Ghost `gClean` and Lookup Equations -/

/-- Serialized `(alice, bob)` protocol address pair on `PreKeySignalMessage` sends. -/
abbrev pqAddrBytes : HwBytes :=
  serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩

/-- Canonical clean `Ghost` aligned with the compact timestamps of `ssClean cls 5`. -/
def gClean (r : ProtocolSetup) (_cls : Nat → Nat) : Ghost where
  σ ts n :=
    if ts < 26 then r.fresh ts n
    else if ts = 26 then slice (ev 0).coins 0 32
    else if ts = 27 then ev0KyberEnt
    else if ts = 28 then slice (ev 0).coins 160 32
    else if ts = 35 then (ev 1).input
    else if ts = 36 then (ev 1).coins.take n
    else if ts = 42 then (ev 2).coins.take 32
    else if ts = 52 then slice (ev 3).coins 0 32
    else if ts = 53 then ev3KyberEnt
    else if ts = 54 then slice (ev 3).coins 160 32
    else if ts = 61 then (ev 4).input
    else if ts = 62 then (ev 4).coins.take n
    else r.fresh ts n
  addr _ := pqAddrBytes

theorem gClean_sigma_lt26 (r : ProtocolSetup) (cls : Nat → Nat) {ts n : Nat} (h : ts < 26) :
    (gClean r cls).σ ts n = r.fresh ts n := by
  simp [gClean, h]

theorem gClean_sigma_26 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 26 n = slice (ev 0).coins 0 32 := rfl
theorem gClean_sigma_27 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 27 n = ev0KyberEnt := rfl
theorem gClean_sigma_28 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 28 n = slice (ev 0).coins 160 32 := rfl
theorem gClean_sigma_35 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 35 n = (ev 1).input := rfl
theorem gClean_sigma_36 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 36 n = (ev 1).coins.take n := rfl
theorem gClean_sigma_42 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 42 n = (ev 2).coins.take 32 := rfl
theorem gClean_sigma_52 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 52 n = slice (ev 3).coins 0 32 := rfl
theorem gClean_sigma_53 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 53 n = ev3KyberEnt := rfl
theorem gClean_sigma_54 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 54 n = slice (ev 3).coins 160 32 := rfl
theorem gClean_sigma_61 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 61 n = (ev 4).input := rfl
theorem gClean_sigma_62 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) :
    (gClean r cls).σ 62 n = (ev 4).coins.take n := rfl

theorem gClean_addr (r : ProtocolSetup) (cls : Nat → Nat) (w : Bytes) :
    (gClean r cls).addr w = pqAddrBytes := rfl

/-! ## 3. `GhostAndSemMatchSetup` and `GhostWF` on `gClean` -/

theorem gamma_KemPk (i : CryptoProofLib.Refinement.ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (sk : Bytes) :
    gamma i S g (kemPk sk) = S.kemPk (gamma i S g sk) := by
  unfold gamma gamma'
  show ((({ sk } : DY.PQKem.Pk.SubF Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll i S g)]; rfl

theorem gamma_Sign (i : CryptoProofLib.Refinement.ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (sk n m : Bytes) :
    gamma i S g (DY.Signature.sign sk n m) =
      S.sign (gamma i S g sk) (gamma i S g n) (gamma i S g m) := by
  unfold gamma gamma'
  show ((({ sk, nonce := n, msg := m } : DY.Signature.Sign.SubF Bytes).pack).rec
    (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll i S g)]; rfl

theorem gamma_randTerm_pos {i : CryptoProofLib.Refinement.ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ts n : Nat} (hn : n ≠ 0) :
    gamma i S g (randTerm ts n) = g.σ ts n := by
  unfold randTerm
  rw [gamma_rand]
  simp only [hn, ↓reduceIte]

theorem ghostAndSemMatchSetup_gClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (cls : Nat → Nat)
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S g) :
    GhostAndSemMatchSetup keepOpkI0 r S (gClean r cls) := by
  have hf := r_facts_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hf.alice_eq, hf.bob_eq]; decide
  have hrandAt := setupRandomsAt_of_fit hfit
  have hc1 : ∀ p ∈ setupRandomsAt r, (gClean r cls).σ p.1 p.2 = r.fresh p.1 p.2 := by
    rw [hrandAt]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact gClean_sigma_lt26 r cls (by decide)
  have hsig_eq : ∀ ts n,
      (ts, n) ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64), (22, 32)] →
      n ≠ 0 → gamma keepOpkI0 S (gClean r cls) (randTerm ts n) =
        gamma keepOpkI0 S g (randTerm ts n) := by
    intro ts n hmem hn
    have hmem' : (ts, n) ∈ setupRandomsAt r := hrandAt ▸ hmem
    rw [gamma_randTerm_pos hn, gamma_randTerm_pos hn]
    exact (hc1 (ts, n) hmem').trans (hCompat.1 (ts, n) hmem').symm
  refine ⟨hc1, ?_, hCompat.2.2⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [← hCompat.2.1 r.spkSigTerm (by simp),
        show r.spkSigTerm = setupPublic r 5 from rfl,
        Symbolic.Swarm.CREF.b1_setupPublic_5 r hNe]
    unfold DY.Libsignal.PQXDH.encodeEC
    rw [gamma_Sign, gamma_Sign, gamma_concat, gamma_concat, gamma_litByte, gamma_litByte,
        gamma_dhPk, gamma_dhPk,
        hsig_eq 5 32 (by decide) (by decide),
        hsig_eq 11 64 (by decide) (by decide),
        hsig_eq 10 32 (by decide) (by decide)]
  · rw [← hCompat.2.1 r.pqpkPubTerm (by simp),
        show r.pqpkPubTerm = setupPublic r 6 from rfl,
        Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe]
    rw [gamma_KemPk, gamma_KemPk, hsig_eq 16 64 (by decide) (by decide)]
  · rw [← hCompat.2.1 r.pqpkSigTerm (by simp),
        show r.pqpkSigTerm = setupPublic r 7 from rfl,
        Symbolic.Swarm.CREF.b1_setupPublic_7 r hNe]
    unfold DY.Libsignal.PQXDH.encodeKEM
    rw [gamma_Sign, gamma_Sign, gamma_concat, gamma_concat, gamma_litByte, gamma_litByte,
        gamma_KemPk, gamma_KemPk,
        hsig_eq 5 32 (by decide) (by decide),
        hsig_eq 17 64 (by decide) (by decide),
        hsig_eq 16 64 (by decide) (by decide)]

private def VisStepWF (g : Ghost) (vs : List VisEntry) : Prop :=
  (∀ v ∈ vs, v.kind = .rng → ∀ ts n, n ≠ 0 → randTerm ts n ∈ v.terms → (g.σ ts n).length = n) ∧
  (∀ v ∈ vs, v.kind = .send → v.layout ≠ .whisper)

private theorem visStepWF_append {g : Ghost} {xs ys : List VisEntry}
    (hx : VisStepWF g xs) (hy : VisStepWF g ys) : VisStepWF g (xs ++ ys) :=
  ⟨fun v hv => by rcases List.mem_append.mp hv with h | h; exacts [hx.1 v h, hy.1 v h],
   fun v hv => by rcases List.mem_append.mp hv with h | h; exacts [hx.2 v h, hy.2 v h]⟩

private theorem randTerm_inj {ts ts' n n' : Nat}
    (heq : randTerm ts n = randTerm ts' n') : ts = ts' ∧ n = n' := by
  have h := Symbolic.DYBridge.DY.BytesView.pack_inj.mp heq
  exact ⟨congrArg DY.Random.Random.timestamp h, congrArg DY.Random.Random.size h⟩

private theorem take_len_eq {α : Type} {xs : List α} {n : Nat} (h : n ≤ xs.length) :
    (xs.take n).length = n :=
  List.length_take_of_le h

private theorem visStepWF_cleanStep {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls) :
    ∀ k < 5, ∀ s, (cleanCallSteps cls)[k]? = some s →
      VisStepWF (gClean r cls)
        (stepView s (runTrace r (ssClean cls k)) (runWrapped (ev k))) := by
  have hf := r_facts_of_fit hfit
  obtain ⟨ht0, ht1, ht2, ht3, ht4, _⟩ := runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq
  intro k hk s hs
  match k with
  | 0 =>
    injection hs with hs; subst hs
    rw [ht0, stepView_s0]
    have hc0 := ev0_coins_base.1
    refine ⟨?_, ?_⟩
    · intro v hv hkind ts n _ hmem
      simp only [kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | ⟨j, _, rfl⟩ | rfl
      · cases hkind
      · simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_26]; simp only [slice, List.drop_zero]; exact take_len_eq (by omega)
      · simp only [List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_27]; exact ev0_coins_base.2.1
      · simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_28]; dsimp only [slice]
        exact take_len_eq (by rw [List.length_drop, hc0])
    · intro v hv hkind
      simp only [kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false, rngEntry] at hv
      rcases hv with rfl | rfl | ⟨j, _, rfl⟩ | rfl <;> cases hkind
  | 1 =>
    injection hs with hs; subst hs
    rw [ht1, ev1_facts.2.2.2.2, stepView_s1]
    have hc1 := ev1_facts.2.2.2.1
    have hcl0 := hv.1
    refine ⟨?_, ?_⟩
    · intro v hv hkind ts n _ hmem
      by_cases h0 : cls 0 = 0
      · simp [h0] at hv
        rcases hv with rfl | rfl <;> cases hkind
      · simp [h0, rngEntry] at hv
        rcases hv with rfl | rfl | rfl
        · cases hkind
        · simp only [List.mem_singleton] at hmem
          obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
          rw [gClean_sigma_36]
          exact take_len_eq (by rcases hcl0 with h | h | h <;> omega)
        · cases hkind
    · intro v hv hkind
      by_cases h0 : cls 0 = 0 <;> (simp [h0, rngEntry] at hv; rcases hv with h | h <;>
        try rcases h with rfl | rfl) <;>
        (try cases hkind) <;> (intro hc; cases hc)
  | 2 =>
    injection hs with hs; subst hs
    rw [ht2, stepView_s2]
    have hc2 := ev2_facts.2.2.1
    refine ⟨?_, ?_⟩
    · intro v hv hkind ts n _ hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · cases hkind
      · simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_42]; exact take_len_eq (by omega)
      · cases hkind
    · intro v hv hkind
      simp only [List.mem_cons, List.not_mem_nil, or_false, rngEntry] at hv
      rcases hv with rfl | rfl | rfl <;> cases hkind
  | 3 =>
    injection hs with hs; subst hs
    rw [ht3, stepView_s3]
    have hc3 := ev3_coins_base.1
    refine ⟨?_, ?_⟩
    · intro v hv hkind ts n _ hmem
      simp only [kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | ⟨j, _, rfl⟩ | rfl
      · cases hkind
      · simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_52]; simp only [slice, List.drop_zero]; exact take_len_eq (by omega)
      · simp only [List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_53]; exact ev3_coins_base.2.1
      · simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_54]; dsimp only [slice]
        exact take_len_eq (by rw [List.length_drop, hc3])
    · intro v hv hkind
      simp only [kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false, rngEntry] at hv
      rcases hv with rfl | rfl | ⟨j, _, rfl⟩ | rfl <;> cases hkind
  | 4 =>
    injection hs with hs; subst hs
    rw [ht4, ev4_facts.2.2.2.2, stepView_s4]
    have hc4 := ev4_facts.2.2.2.1
    have hcl1 := hv.2
    refine ⟨?_, ?_⟩
    · intro v hv hkind ts n _ hmem
      by_cases h1 : cls 1 = 0
      · simp [h1] at hv
        rcases hv with rfl | rfl <;> cases hkind
      · simp [h1, rngEntry] at hv
        rcases hv with rfl | rfl | rfl
        · cases hkind
        · simp only [List.mem_singleton] at hmem
          obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
          rw [gClean_sigma_62]
          exact take_len_eq (by rcases hcl1 with h | h | h <;> omega)
        · cases hkind
    · intro v hv hkind
      by_cases h1 : cls 1 = 0 <;> (simp [h1, rngEntry] at hv; rcases hv with h | h <;>
        try rcases h with rfl | rfl) <;>
        (try cases hkind) <;> (intro hc; cases hc)
  | n + 5 => omega

private theorem visStepWF_visClean {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls) :
    ∀ m ≤ 5, VisStepWF (gClean r cls) (visClean r cls m)
  | 0, _ =>
    ⟨fun _ h => False.elim (List.not_mem_nil h),
     fun _ h => False.elim (List.not_mem_nil h)⟩
  | m + 1, hm => by
    have hlen : m < (cleanCallSteps cls).length := by rw [CleanTrace.cleanCallSteps_length]; omega
    have hs : (cleanCallSteps cls)[m]? = some (cleanCallSteps cls)[m] := List.getElem?_eq_getElem hlen
    rw [visClean_succ (by omega) hs]
    exact visStepWF_append (visStepWF_visClean hfit hv m (by omega))
      (visStepWF_cleanStep hfit hv m (by omega) (cleanCallSteps cls)[m] hs)

theorem ghostWF_visClean {r : ProtocolSetup} {cls : Nat → Nat} {m : Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls) (hm : m ≤ 5) :
    GhostWF (gClean r cls) (visClean r cls m) := by
  obtain ⟨hrng, hnowhisp⟩ := visStepWF_visClean hfit hv m hm
  refine ⟨hrng, fun _ => Or.inr rfl, fun v hv hk => ⟨fun _ _ _ _ _ _ _ => rfl, ?_⟩⟩
  intro hl
  exact False.elim (hnowhisp v hv hk hl)

/-! ## 4. X25519 Public-Key & Kyber-1024 Evaluations on `gClean` -/

theorem keepOpkPubOfIdx_inj {i j : Fin 10} (h : keepOpkPubOfIdx i = keepOpkPubOfIdx j) : i = j := by
  revert i j h; decide

theorem keepOpkPubOfIdx_length (i : Fin 10) : (keepOpkPubOfIdx i).length = 32 := by
  revert i; decide

/-- List of all 9 `gClean` timestamps carrying 32-byte X25519 secret keys on `ssClean cls 5`. -/
def dhSecretTimestamps : List Nat := [0, 5, 10, 22, 26, 28, 42, 52, 54]

def dhTsSecretIdx : Nat → Fin 10
  | 0 => ⟨0, by decide⟩
  | 5 => ⟨1, by decide⟩
  | 10 => ⟨2, by decide⟩
  | 22 => ⟨3, by decide⟩
  | 26 => ⟨4, by decide⟩
  | 28 => ⟨5, by decide⟩
  | 42 => ⟨6, by decide⟩
  | 52 => ⟨7, by decide⟩
  | _ => ⟨8, by decide⟩

theorem secretIdx_coins_facts :
    keepOpkSecretIdx (clamp w0.aliceId) = some ⟨0, by decide⟩ ∧
    keepOpkSecretIdx (clamp w0.bobId) = some ⟨1, by decide⟩ ∧
    keepOpkSecretIdx (clamp w0.spk) = some ⟨2, by decide⟩ ∧
    keepOpkSecretIdx (clamp w0.opk) = some ⟨3, by decide⟩ ∧
    keepOpkSecretIdx (clamp (slice (ev 0).coins 0 32)) = some ⟨4, by decide⟩ ∧
    keepOpkSecretIdx (clamp (slice (ev 0).coins 160 32)) = some ⟨5, by decide⟩ ∧
    keepOpkSecretIdx (clamp ((ev 2).coins.take 32)) = some ⟨6, by decide⟩ ∧
    keepOpkSecretIdx (clamp (slice (ev 3).coins 0 32)) = some ⟨7, by decide⟩ ∧
    keepOpkSecretIdx (clamp (slice (ev 3).coins 160 32)) = some ⟨8, by decide⟩ ∧
    keepOpkSecretIdx (clamp ((ev 5).coins.take 32)) = some ⟨9, by decide⟩ := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev0Coins_eq]; decide +kernel
  · rw [ev0Coins_eq]; decide +kernel
  · rw [ev2Coins_eq]; decide +kernel
  · rw [ev3Coins_eq]; decide +kernel
  · rw [ev3Coins_eq]; decide +kernel
  · rw [ev5Coins_eq]; decide +kernel

theorem ev0_bundle_opk_spk :
    slice (ev 0).input 9 33 = ecKey (keepOpkPubOfIdx ⟨3, by decide⟩) ∧
    slice (ev 0).input 46 33 = ecKey (keepOpkPubOfIdx ⟨2, by decide⟩) := by
  rw [ev0In_eq]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem gamma_dhPk_ts {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {ts : Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hts : ts ∈ dhSecretTimestamps) :
    gamma keepOpkI0 S (gClean r cls) (dhPk (rnd ts 32)) =
      keepOpkPubOfIdx (dhTsSecretIdx ts) := by
  have hf := r_facts_of_fit hfit
  have hrandAt := setupRandomsAt_of_fit hfit
  obtain ⟨hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, _⟩ := secretIdx_coins_facts
  have hsecIdx : keepOpkSecretIdx (clamp ((gClean r cls).σ ts 32)) =
      some (dhTsSecretIdx ts) := by
    simp only [dhSecretTimestamps, List.mem_cons, List.not_mem_nil, or_false] at hts
    rcases hts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [gClean_sigma_lt26 r cls (by decide)]
      have hs : secretBytes r 0 = r.fresh 0 32 := by unfold secretBytes; rw [hrandAt]; rfl
      rw [← hs, hf.sec0_eq]; exact hi0
    · rw [gClean_sigma_lt26 r cls (by decide)]
      have hs : secretBytes r 1 = r.fresh 5 32 := by unfold secretBytes; rw [hrandAt]; rfl
      rw [← hs, hf.sec1_eq]; exact hi1
    · rw [gClean_sigma_lt26 r cls (by decide)]
      have hs : secretBytes r 2 = r.fresh 10 32 := by unfold secretBytes; rw [hrandAt]; rfl
      rw [← hs, hf.sec2_eq]; exact hi2
    · rw [gClean_sigma_lt26 r cls (by decide)]
      have hs : secretBytes r 6 = r.fresh 22 32 := by unfold secretBytes; rw [hrandAt]; rfl
      rw [← hs, hf.sec6_eq]; exact hi3
    · rw [gClean_sigma_26]; exact hi4
    · rw [gClean_sigma_28]; exact hi5
    · rw [gClean_sigma_42]; exact hi6
    · rw [gClean_sigma_52]; exact hi7
    · rw [gClean_sigma_54]; exact hi8
  unfold rnd
  rw [gamma_dhPk, gamma_rand]
  simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, keepOpkI0_publicKey]
  unfold keepOpkLookupPub
  rw [hsecIdx]; rfl

theorem gamma_oOpk_ct (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (cls : Nat → Nat) :
    gamma keepOpkI0 S (gClean r cls) oOpk.ct = w0.kyberCts.getD 0 [] := by
  have hct : oOpk.ct = (kemEncap (kemPk pqskB) (rnd 27 32)).1 := by
    dsimp only [oOpk, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [t4Opk_length]; rfl
  rw [hct, gamma_kemEncap_fst]
  unfold rnd
  rw [gamma_rand]
  simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, gClean_sigma_27,
    keepOpkI0_kyberEncaps, Option.getD_some, ev0KyberEnt_eq]
  decide +kernel

theorem gamma_o2Clean_ct (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (cls : Nat → Nat) :
    gamma keepOpkI0 S (gClean r cls) o2Clean.ct = w0.kyberCts.getD 1 [] := by
  have hct : o2Clean.ct = (kemEncap (kemPk pqskB) (rnd 53 32)).1 := by
    dsimp only [o2Clean, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [t7Opk_length]; rfl
  rw [hct, gamma_kemEncap_fst]
  unfold rnd
  rw [gamma_rand]
  simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, gClean_sigma_53,
    keepOpkI0_kyberEncaps, Option.getD_some, ev3KyberEnt_eq]
  decide +kernel

/-! ## 5. Universal `¬ KyberMismatch` -/

theorem not_kyberMismatch_keepOpkI0 (r : ProtocolSetup) (p : PreKeyFields) :
    ¬ KyberMismatch keepOpkI0 r p := by
  rintro ⟨e, ct, ss, he32, _, henc, hndec⟩
  exact hndec (keepOpkI0_kyberCorrectOn r [ct] ct (.head []) e ss he32 henc)

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
