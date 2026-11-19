/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberLits -- proof-setup: allow-public-import

/-!
# Sub-Row Split Helpers for `compHooks0` Kyber-1024 Kernel Certification

Splits `checkKyberRow` into `checkKyberRowEnc` (`11` Keccak permutations) and `checkKyberRowDec`
(`15` Keccak permutations) so each leaf `rfl_kernel` module stays well below the 16 GiB per-module
memory budget.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberSplit

open CryptoGames.MLKEM (Poly)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak (
  forceListBV8 forceListBV8_eq sha3_256Fast sha3_512Fast shake256Fast
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs (
  byteDecodeModFast checkKyberRow indCpaDecryptPrecomp indCpaEncryptPrecomp kyberEncapsOnePrecomp
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberLits (
  compKyberATLit compKyberHPkLit compKyberPk compKyberSHatLit compKyberSk compKyberTHatLit
)

public section
set_option autoImplicit false
set_option maxRecDepth 200000

@[expose] def checkKyberKeyLits : Bool :=
  forceListBV8 compKyberPk fun pk =>
  forceListBV8 compKyberSk fun sk =>
  (compKyberATLit.toList.length == 4) &&
  (compKyberTHatLit.toList.map Array.toList ==
    (List.range 4).map fun i => (byteDecodeModFast 12 ((pk.drop (384 * i)).take 384)).toList) &&
  (compKyberSHatLit.toList.map Array.toList ==
    (List.range 4).map fun i =>
      (byteDecodeModFast 12 (((sk.take 1536).drop (384 * i)).take 384)).toList) &&
  (compKyberHPkLit == sha3_256Fast pk) &&
  ((sk.drop 1536).take 1568 == pk) &&
  ((sk.drop 3104).take 32 == compKyberHPkLit)

@[expose] def checkKyberRowEnc (aTrans : Array (Array Poly)) (tHat : Array Poly)
    (hPk e ctExp : List (BitVec 8)) : Bool :=
  forceListBV8 hPk fun hPk =>
  forceListBV8 e fun e =>
  forceListBV8 ctExp fun ctExp =>
  forceListBV8 (sha3_256Fast (e.take 32)) fun m =>
  forceListBV8 (sha3_512Fast (m ++ hPk)) fun kr =>
  let r := (kr.drop 32).take 32
  let (c1, c2) := indCpaEncryptPrecomp 4 11 5 aTrans tHat m r
  forceListBV8 (c1 ++ c2) fun ct =>
  ct == ctExp

@[expose] def checkKyberRowDec (sHat : Array Poly)
    (hPk e ctExp ssExp : List (BitVec 8)) : Bool :=
  forceListBV8 hPk fun hPk =>
  forceListBV8 e fun e =>
  forceListBV8 ctExp fun ctExp =>
  forceListBV8 ssExp fun ssExp =>
  forceListBV8 (sha3_256Fast (e.take 32)) fun m =>
  forceListBV8 (sha3_512Fast (m ++ hPk)) fun kr =>
  let kBar := kr.take 32
  let ss := shake256Fast 32 (kBar ++ sha3_256Fast ctExp)
  (ss == ssExp) &&
  (indCpaDecryptPrecomp 4 11 5 sHat ctExp == m)

theorem checkKyberRow_of_split {aTrans : Array (Array Poly)} {tHat sHat : Array Poly}
    {hPk e ctExp ssExp : List (BitVec 8)}
    (henc : checkKyberRowEnc aTrans tHat hPk e ctExp = true)
    (hdec : checkKyberRowDec sHat hPk e ctExp ssExp = true) :
    checkKyberRow aTrans tHat sHat hPk e ctExp ssExp = true := by
  unfold checkKyberRowEnc at henc
  unfold checkKyberRowDec at hdec
  unfold checkKyberRow kyberEncapsOnePrecomp
  simp only [forceListBV8_eq] at henc hdec ⊢
  set m := sha3_256Fast (e.take 32)
  set kr := sha3_512Fast (m ++ hPk)
  generalize indCpaEncryptPrecomp 4 11 5 aTrans tHat m ((kr.drop 32).take 32) = p at henc ⊢
  rcases p with ⟨c1, c2⟩
  dsimp only at henc ⊢
  have hct : c1 ++ c2 = ctExp := beq_iff_eq.mp henc
  change (((c1 ++ c2 == ctExp) &&
    (shake256Fast 32 (kr.take 32 ++ sha3_256Fast (c1 ++ c2)) == ssExp)) &&
    (indCpaDecryptPrecomp 4 11 5 sHat ctExp == m)) = true
  rw [hct, beq_self_eq_true, Bool.true_and]
  exact hdec

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberSplit
