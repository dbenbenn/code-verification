/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingPlaced -- proof-setup: allow-public-import

/-!
# Placed CLI SHA-256 Guard Bridge Helpers

**Checked by Lean.** Pure and placed helper lemmas discharging `Sha256AgreesOnInput` at
`W.C.F = sha256Compress` and `RealHooksAgreeOnInput` at `W = realCliHooks`, plus `shaStateBytes`
round-trip decoding.
-/

public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open Arm64 Arm64.Process
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open CryptoVerification.SignalSession (CliHooks)

/-- Replaces `W.C.F` with the FIPS 180-4 SHA-256 block compression function
`CryptoVerification.LibsignalSpqrV1.sha256Compress` executed by the linked ELF code. -/
@[expose] def withRealSha256 (W : CliHooks) : CliHooks :=
  { W with C := { W.C with F := CryptoVerification.LibsignalSpqrV1.sha256Compress } }

/-- Per-call domain guard requiring that on any spec-domain transition matching `i`, the model
transition at `W.C.F` agrees with `CryptoVerification.LibsignalSpqrV1.sha256Compress`
(`withRealSha256 W`). -/
abbrev Sha256AgreesOnInput (W : CliHooks)
    (i : CryptoVerification.SignalSession.Inputs) : Prop :=
  ElfGuard.ModelAgreesOnInput ⟨W.C, W.Q⟩ ⟨(withRealSha256 W).C, (withRealSha256 W).Q⟩ i

/-- When `W.C.F` already equals `sha256Compress`, `withRealSha256 W` is `W` itself. -/
theorem withRealSha256_eq_self_of_eq {W : CliHooks}
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress) :
    withRealSha256 W = W := by
  cases W with
  | mk C Q =>
    cases C
    dsimp only at hF
    subst hF
    rfl

/-- At `W.C.F = sha256Compress`, the per-call domain guard `Sha256AgreesOnInput W i` is
equivalent to `True`. -/
theorem sha256AgreesOnInput_iff_true_of_eq {W : CliHooks}
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (i : CryptoVerification.SignalSession.Inputs) :
    Sha256AgreesOnInput W i ↔ True := by
  unfold Sha256AgreesOnInput ElfGuard.ModelAgreesOnInput
  rw [withRealSha256_eq_self_of_eq hF]
  simp

/-- When `W` satisfies all 9 closed primitive equations of `realCliHooks`, `W` equals
`realCliHooks`. -/
theorem eq_realCliHooks_of_eqs {W : CliHooks}
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental) :
    W = realCliHooks := by
  rcases W with ⟨⟨_, _, _, _, _⟩, ⟨_, _, _, _⟩⟩
  dsimp only at hF hE hD hX hPub hF512 hEnc hDec hK
  subst hF hE hD hX hPub hF512 hEnc hDec hK
  rfl

/-- At `W = realCliHooks`, the per-call domain guard `RealHooksAgreeOnInput W i` is equivalent
to `True`. -/
theorem realHooksAgreeOnInput_iff_true_of_eq {W : CliHooks}
    (hW : W = realCliHooks)
    (i : CryptoVerification.SignalSession.Inputs) :
    RealHooksAgreeOnInput W i ↔ True := by
  subst hW
  refine iff_true_intro ⟨fun _ _ _ _ _ hdom _ _ => ⟨rfl, hdom⟩, ?_⟩
  unfold ElfGuard.ModelAgreesOnInput
  simp

/-- At `W = realCliHooks`, `elfRel` equals the unguarded `runFnToRelation` of `cliRunElf`. -/
theorem elfRel_eq_runFnToRelation_of_eq
    (elf : ElfImage) (addrs : CryptoVerification.SignalSession.CliElfAddrs)
    (interp : ExternInterpretation)
    {W : CliHooks} (hW : W = realCliHooks) :
    elfRel elf addrs interp W =
      runFnToRelation (CryptoVerification.SignalSession.cliRunElf elf addrs) := by
  funext i o
  exact propext (and_iff_left ((realHooksAgreeOnInput_iff_true_of_eq hW i).mpr trivial))

/-- At `W = realCliHooks`, `elfRelPlaced` equals the unguarded `runFnToRelation` of
`cliRunPlacedSig`. -/
theorem elfRelPlaced_eq_runFnToRelation_of_eq
    (mpl : Obj.MultiPlacement) (elf : ElfImage) (interp : ExternInterpretation)
    {W : CliHooks} (hW : W = realCliHooks) :
    elfRelPlaced mpl elf interp W =
      runFnToRelation (CryptoVerification.SignalSession.Placed.cliRunPlacedSig mpl elf) := by
  funext i o
  exact propext (and_iff_left ((realHooksAgreeOnInput_iff_true_of_eq hW i).mpr trivial))

private theorem word32_of_le_mod_div (w : BitVec 32) :
    BitVec.ofNat 32
      (w.toNat % 256 + 256 * (w.toNat / 256 % 256) +
        65536 * (w.toNat / 65536 % 256) + 16777216 * (w.toNat / 16777216 % 256)) = w := by
  apply BitVec.eq_of_toNat_eq
  have hw : w.toNat < 4294967296 := w.isLt
  simp only [BitVec.toNat_ofNat]
  omega

/-- Decoding `shaStateBytes s` with `shaStateOfBytes` recovers `s`. -/
theorem shaStateOfBytes_shaStateBytes (s : CryptoGames.HMAC.ShaState) :
    DY.Libsignal.Refinement.shaStateOfBytes (DY.Libsignal.Refinement.shaStateBytes s) = s := by
  rcases s with ⟨l, hl⟩
  rcases l with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | tl⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hl)
  apply List.Vector.eq
  simp [DY.Libsignal.Refinement.shaStateBytes, DY.Libsignal.Refinement.shaStateOfBytes,
    List.Vector.toList, List.Vector.ofFn, List.getD_eq_getElem?_getD, word32_of_le_mod_div]
  rfl

end DY.Libsignal.Composed.Refinement.Cli
