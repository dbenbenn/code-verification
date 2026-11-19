/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.DH.X25519
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak -- proof-setup: allow-public-import
meta import ProofLib.ProgramReflection

/-!
# Certified RFC 7748 X25519 Table Cache + Obligation (iv) Setup-Key Proofs

Provides kernel-evaluatable (`withForcedNat`) RFC 7748 X25519 Montgomery-ladder wrappers, proves
that `compHooks0`'s 12 recorded setup keys are already RFC 7748 clamped and satisfy
`compLookupPub (clamp k) = x25519Pubkey (clamp k)` (ElfBinding review obligation (iv)), and exports
certified table-accelerated `x25519PubFast = x25519PubFromSecretRef` and
`x25519DhFast = x25519Ref` for fast kernel evaluation of `RealHooksAgreeOnInput`.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealX25519

open scoped ProofLib.ProgramReflection
open VerifiedLibraries.Common (
  p25519 fpAdd fpSub fpMul fpSq fpInv fpPow modPow modPowLoop
  leBytesToNat natToLeBytes clampScalar
)
open CryptoGames.Ratchet (X25519Fn)
open CryptoGames.LibsignalSession (PubKeyFn)
open CryptoGames.RFC7748 (
  MontProjPoint a24 decodeU255 montDiffAddAndDouble montLadderLoop x25519
  x25519Basepoint x25519Ladder x25519PubFromSecretRef x25519Pubkey x25519Ref
)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (leBytes)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.Interp0 (
  bytesToNat compDhByIdx compLookupPub compPubOfIdx compPubOfOpt compSecretIdx
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak (withForcedNat withForcedNat_eq)

public section
set_option autoImplicit false

private theorem leBytes_bytesToNat : ∀ bs : HwBytes, leBytes bs.length (bytesToNat bs) = bs
  | [] => rfl
  | b :: bs => by
    have h1 : BitVec.ofNat 8 (b.toNat + 256 * bytesToNat bs) = b := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    have h2 : (b.toNat + 256 * bytesToNat bs) / 256 = bytesToNat bs := by
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt b.isLt, Nat.zero_add]
    simp only [List.length_cons, leBytes, bytesToNat, h1, h2, leBytes_bytesToNat bs]

private theorem leBytes_length (n v : Nat) : (leBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [leBytes, ih (v / 256)]

/-! ## Forced-`Nat` RFC 7748 X25519 Ladder for Kernel Evaluation -/

@[expose] def modPowLoopFast : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m, acc => acc % m
  | fuel + 1, base, exp, m, acc =>
    if exp == 0 then acc % m
    else
      withForcedNat (if exp % 2 == 1 then (acc * base) % m else acc) fun acc' =>
      withForcedNat ((base * base) % m) fun base' =>
      withForcedNat (exp / 2) fun exp' =>
      modPowLoopFast fuel base' exp' m acc'

private theorem modPowLoopFast_eq :
    ∀ (fuel base exp m acc : Nat), modPowLoopFast fuel base exp m acc = modPowLoop fuel base exp m acc
  | 0, _, _, _, _ => rfl
  | fuel + 1, base, exp, m, acc => by
    simp only [modPowLoopFast, modPowLoop]
    split
    · rfl
    · simp only [withForcedNat_eq, modPowLoopFast_eq fuel]

@[expose] def fpInvFast (a : Nat) : Nat :=
  modPowLoopFast 256 (a % p25519) (p25519 - 2) p25519 1

private theorem fpInvFast_eq (a : Nat) : fpInvFast a = fpInv a :=
  modPowLoopFast_eq 256 (a % p25519) (p25519 - 2) p25519 1

@[expose] def montDiffAddAndDoubleFast (u1 : Nat) (P Q : MontProjPoint) :
    MontProjPoint × MontProjPoint :=
  withForcedNat (fpAdd P.U P.W) fun A =>
  withForcedNat (fpSq A) fun AA =>
  withForcedNat (fpSub P.U P.W) fun B =>
  withForcedNat (fpSq B) fun BB =>
  withForcedNat (fpSub AA BB) fun E =>
  withForcedNat (fpAdd Q.U Q.W) fun C =>
  withForcedNat (fpSub Q.U Q.W) fun D =>
  withForcedNat (fpMul D A) fun DA =>
  withForcedNat (fpMul C B) fun CB =>
  withForcedNat (fpMul AA BB) fun U2 =>
  withForcedNat (fpMul E (fpAdd AA (fpMul a24 E))) fun W2 =>
  withForcedNat (fpSq (fpAdd DA CB)) fun U3 =>
  withForcedNat (fpMul u1 (fpSq (fpSub DA CB))) fun W3 =>
  (⟨U2, W2⟩, ⟨U3, W3⟩)

private theorem montDiffAddAndDoubleFast_eq (u1 : Nat) (P Q : MontProjPoint) :
    montDiffAddAndDoubleFast u1 P Q = montDiffAddAndDouble u1 P Q := by
  unfold montDiffAddAndDoubleFast montDiffAddAndDouble
  simp only [withForcedNat_eq]

@[expose] def montLadderLoopFast : Nat → Nat → Nat → MontProjPoint → MontProjPoint → MontProjPoint
  | 0, _, _, x0, _ => x0
  | fuel + 1, k, u1, x0, x1 =>
    withForcedNat ((k / (2 ^ fuel)) % 2) fun bit =>
    let (p0, p1) := if bit == 1 then (x1, x0) else (x0, x1)
    let (q0, q1) := montDiffAddAndDoubleFast u1 p0 p1
    let (x0', x1') := if bit == 1 then (q1, q0) else (q0, q1)
    montLadderLoopFast fuel k u1 x0' x1'

private theorem montLadderLoopFast_eq :
    ∀ (fuel k u1 : Nat) (x0 x1 : MontProjPoint),
      montLadderLoopFast fuel k u1 x0 x1 = montLadderLoop fuel k u1 x0 x1
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, u1, x0, x1 => by
    simp only [montLadderLoopFast, montLadderLoop, withForcedNat_eq,
      montDiffAddAndDoubleFast_eq, montLadderLoopFast_eq fuel]

@[expose] def x25519LadderFast (k u : Nat) : Nat :=
  withForcedNat (u % p25519) fun u1 =>
  let res := montLadderLoopFast 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
  withForcedNat (fpInvFast res.W) fun wInv =>
  fpMul res.U wInv

private theorem x25519LadderFast_eq (k u : Nat) : x25519LadderFast k u = x25519Ladder k u := by
  unfold x25519LadderFast x25519Ladder
  simp only [withForcedNat_eq, montLadderLoopFast_eq, fpInvFast_eq]

@[expose] def x25519Fast (scalar uBytes : List (BitVec 8)) : List (BitVec 8) :=
  natToLeBytes 32 (x25519LadderFast (clampScalar scalar) (decodeU255 uBytes))

theorem x25519Fast_eq (scalar uBytes : List (BitVec 8)) :
    x25519Fast scalar uBytes = x25519 scalar uBytes := by
  unfold x25519Fast x25519
  rw [x25519LadderFast_eq]

theorem x25519Fast_length (scalar uBytes : List (BitVec 8)) :
    (x25519Fast scalar uBytes).length = 32 := by
  simp [x25519Fast, natToLeBytes]

/-! ## Recorded 12 Setup Keys and Obligation (iv) -/

@[expose] def compSecretNatOfIdx (i : Fin 12) : Nat :=
  match i.val with
  | 0 => 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b1566240215318
  | 1 => 0x5ebeb27d522a4e8b1b9ec6ebbda97281992ffac69a7acd4c118e846ea93bc948
  | 2 => 0x66964f30e299608354c3ce2401e61e48206f8f36b8468efae8fb77c019042648
  | 3 => 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd52080
  | 4 => 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df00
  | 5 => 0x5c7f85979eaf14f7fb49936bd882f71348114868c9e6902973986d357f2a7e20
  | 6 => 0x549ffe504bfdab7f6ec624aa856858679cde98852e60034bba69ec90eb4fef88
  | 7 => 0x52461536c4ec47f2f627d8acad21a894997606a9f69e103e2b90d87b87062920
  | 8 => 0x6264601f3e57cc7b01d4d961486f4f76c69227f456ddcf04d2fe0ce30504f8b0
  | 9 => 0x7f62e60296fdfd995c0ef0e79e17027f62ee6dbfe35320b65c29f2075b719610
  | 10 => 0x640de9c22005555e9f5bc5f1de78c1a837ccef0b2752c025b10c76f4432be218
  | _ => 0x73a8337d2e8afab34f706c15ac4bb27e43eefd6e2178cb07b9d9f3a798205660

/-- The 12 recorded 32-byte setup private keys indexed by `Fin 12` (matching `compSecretIdx`). -/
@[expose] def compSecretOfIdx (i : Fin 12) : HwBytes :=
  leBytes 32 (compSecretNatOfIdx i)

theorem compSecretOfIdx_length (i : Fin 12) : (compSecretOfIdx i).length = 32 :=
  leBytes_length 32 (compSecretNatOfIdx i)

/-- Vector form of `compSecretOfIdx i`. -/
@[expose] def compSecretVecOfIdx (i : Fin 12) : List.Vector (BitVec 8) 32 :=
  ⟨compSecretOfIdx i, compSecretOfIdx_length i⟩

private theorem ite_beq_some {n m : Nat} {a i : Fin 12} {rest : Option (Fin 12)}
    (h : (if n == m then some a else rest) = some i) :
    (n = m ∧ i = a) ∨ rest = some i := by
  cases hnm : (n == m)
  · rw [hnm] at h; exact Or.inr h
  · rw [hnm] at h; injection h with h'; exact Or.inl ⟨beq_iff_eq.mp hnm, h'.symm⟩

theorem compSecretIdx_some {s : HwBytes} {i : Fin 12} (h : compSecretIdx s = some i) :
    s = compSecretOfIdx i := by
  unfold compSecretIdx at h
  cases hlen : (s.length == 32)
  · rw [hlen] at h; cases h
  · rw [hlen] at h
    dsimp only at h
    have hsLen : s.length = 32 := beq_iff_eq.mp hlen
    have hnat : bytesToNat s = compSecretNatOfIdx i := by
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      rcases ite_beq_some h with ⟨hn, rfl⟩ | h; · exact hn
      cases h
    have hle := leBytes_bytesToNat s
    rw [hsLen] at hle
    exact hle.symm.trans (congrArg (leBytes 32) hnat)

private theorem compSetupKeys_cert :
    ((List.finRange 12).all fun i =>
      decide (compSecretIdx (compSecretOfIdx i) = some i) &&
      decide (CryptoGames.Ratchet.clampScalar (compSecretVecOfIdx i) = compSecretVecOfIdx i) &&
      decide (x25519Fast (compSecretOfIdx i) x25519Basepoint = compPubOfIdx i)) = true := by
  rfl_kernel

private theorem compSetupKeys_cert_at (i : Fin 12) :
    compSecretIdx (compSecretOfIdx i) = some i ∧
    CryptoGames.Ratchet.clampScalar (compSecretVecOfIdx i) = compSecretVecOfIdx i ∧
    x25519Fast (compSecretOfIdx i) x25519Basepoint = compPubOfIdx i := by
  have hall := List.all_eq_true.mp compSetupKeys_cert i (List.mem_finRange i)
  rcases Bool.and_eq_true _ _ |>.mp hall with ⟨h12, h3⟩
  rcases Bool.and_eq_true _ _ |>.mp h12 with ⟨h1, h2⟩
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3⟩

/-- **ElfBinding review obligation (iv)**: on every one of the 12 setup private keys `k`,
`compSecretIdx` recognizes the RFC 7748 clamped bytes `(clampScalar k).toList`, and
`compLookupPub (clampScalar k).toList = x25519Pubkey (clampScalar k).toList`. -/
theorem compSetupKey_clamped_pub_ok (i : Fin 12) :
    compSecretIdx (CryptoGames.Ratchet.clampScalar (compSecretVecOfIdx i)).toList = some i ∧
    compLookupPub (CryptoGames.Ratchet.clampScalar (compSecretVecOfIdx i)).toList =
      x25519Pubkey (CryptoGames.Ratchet.clampScalar (compSecretVecOfIdx i)).toList := by
  rcases compSetupKeys_cert_at i with ⟨hidx, hclamp, hpub⟩
  have hclList : (CryptoGames.Ratchet.clampScalar (compSecretVecOfIdx i)).toList =
      compSecretOfIdx i := congrArg List.Vector.toList hclamp
  refine ⟨hclList.symm ▸ hidx, ?_⟩
  have h1 : compLookupPub (compSecretOfIdx i) = compPubOfIdx i :=
    congrArg compPubOfOpt hidx
  have h2 : compPubOfIdx i = x25519Pubkey (compSecretOfIdx i) :=
    hpub.symm.trans (x25519Fast_eq (compSecretOfIdx i) x25519Basepoint)
  exact (congrArg compLookupPub hclList).trans
    ((h1.trans h2).trans (congrArg x25519Pubkey hclList.symm))

theorem compLookupPub_eq_x25519Pubkey_of_secretIdx {s : HwBytes} {i : Fin 12}
    (h : compSecretIdx s = some i) :
    compLookupPub s = x25519Pubkey s := by
  have hs := compSecretIdx_some h
  rcases compSetupKeys_cert_at i with ⟨_, _, hpub⟩
  have h1 : compLookupPub s = compPubOfIdx i := congrArg compPubOfOpt h
  have h2 : compPubOfIdx i = x25519Pubkey (compSecretOfIdx i) :=
    hpub.symm.trans (x25519Fast_eq (compSecretOfIdx i) x25519Basepoint)
  exact h1.trans (h2.trans (congrArg x25519Pubkey hs.symm))

/-! ## Certified Table-Accelerated `x25519PubFast` and `x25519DhFast` -/

theorem compPubOfIdx_length (i : Fin 12) : (compPubOfIdx i).length = 32 := by
  unfold compPubOfIdx
  repeat (first | exact leBytes_length 32 _ | split)

@[expose] def x25519PubFast : PubKeyFn :=
  fun sec =>
    match compSecretIdx sec.toList with
    | some i => ⟨compPubOfIdx i, compPubOfIdx_length i⟩
    | none => ⟨x25519Fast sec.toList x25519Basepoint, x25519Fast_length sec.toList x25519Basepoint⟩

theorem x25519PubFast_eq_ref : x25519PubFast = x25519PubFromSecretRef := by
  funext sec
  apply List.Vector.eq
  unfold x25519PubFast x25519PubFromSecretRef
  cases h : compSecretIdx sec.toList with
  | none =>
    dsimp only [x25519Pubkey]
    exact x25519Fast_eq sec.toList x25519Basepoint
  | some i =>
    change compPubOfIdx i = x25519 sec.toList x25519Basepoint
    have hs := compSecretIdx_some h
    rcases compSetupKeys_cert_at i with ⟨_, _, hpub⟩
    exact hpub.symm.trans ((x25519Fast_eq (compSecretOfIdx i) x25519Basepoint).trans
      (congrArg (x25519 · x25519Basepoint) hs.symm))

@[expose] def compCanonicalU (j : Fin 12) : Nat :=
  match j.val with
  | 0 => 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a
  | 1 => 0x4dc349100e5b5e487b92852d337badcba1b1139305b83213f7868f2c4f90bbab
  | 2 => 0x3fd3bf370a6f0d82bce23a6bc81073a3968030a12fd4407213598fb0a385fc5b
  | 3 => 0x1814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6
  | 4 => 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7
  | 5 => 0xdf1b9cfdb6f1beecfab864aec3b00d301fabcf8efbdadae64b8f3ce0a70062a
  | 6 => 0x3876d0f225aa2d85682498e61e2fe97bc189e4815c96aee21e8218cf997b078f
  | 7 => 0x4ae020f0133ecd4a8abe6ff58f162cef8c18ef9d7411918dad639572eb5d1627
  | 8 => 0x72286eeb9c357cfe8e987def6eb01547ab213f371009d6008d514824f77f6845
  | 9 => 0x191933f5352eccec96182dee25cb6fc49f24128081a4b0215fcc626dfb5fa897
  | 10 => 0x403fe1f44d61222fa5fa45d5d75c73b9cf3bb9613445fbf0ec18d035609a9783
  | _ => 0x2d6b8af9c5741253c312f5863e6816d644b74e4125980fb1d878a17e71049637

/-- Canonical 255-bit Montgomery `u`-coordinate lookup for the 12 setup public keys (excludes the
8-torsion point `compEkATorsion` so every hit equals real RFC 7748 `x25519`). -/
@[expose] def compCanonicalPointIdxOfU (u : Nat) : Option (Fin 12) :=
  (List.finRange 12).find? (fun j => u == compCanonicalU j)

private theorem compPubU_cert :
    ((List.finRange 12).all fun j =>
      decide (compCanonicalU j = decodeU255 (compPubOfIdx j))) = true := by
  rfl_kernel

private theorem compCanonicalPointIdxOfU_some {u : Nat} {j : Fin 12}
    (h : compCanonicalPointIdxOfU u = some j) :
    u = decodeU255 (compPubOfIdx j) := by
  unfold compCanonicalPointIdxOfU at h
  have hpred : (u == compCanonicalU j) = true :=
    @List.find?_some _ (fun k => u == compCanonicalU k) _ _ h
  have hu : u = compCanonicalU j := beq_iff_eq.mp hpred
  have hj := of_decide_eq_true (List.all_eq_true.mp compPubU_cert j (List.mem_finRange j))
  exact hu.trans hj

/-- Selector for the 13 recorded X25519 Diffie-Hellman key-index pairs in `compDhByIdx`. -/
@[expose] def compDhCertPair (i j : Fin 12) : Bool :=
  let lo := min i.val j.val
  let hi := max i.val j.val
  (lo == 0 && hi == 3) ||
  (lo == 1 && hi == 3) ||
  (lo == 1 && hi == 4) ||
  (lo == 2 && hi == 3) ||
  (lo == 2 && hi == 5) ||
  (lo == 3 && hi == 6) ||
  (lo == 3 && hi == 7) ||
  (lo == 3 && hi == 9) ||
  (lo == 3 && hi == 10) ||
  (lo == 4 && hi == 6) ||
  (lo == 4 && hi == 9) ||
  (lo == 7 && hi == 8) ||
  (lo == 7 && hi == 11)

private theorem compDhPairs_cert :
    ((List.finRange 12).all fun i =>
      (List.finRange 12).all fun j =>
        !(compDhCertPair i j) ||
        decide (x25519Fast (compSecretOfIdx i) (compPubOfIdx j) = compDhByIdx i j)) = true := by
  rfl_kernel

private theorem compDhPairs_cert_at {i j : Fin 12} (hp : compDhCertPair i j = true) :
    x25519Fast (compSecretOfIdx i) (compPubOfIdx j) = compDhByIdx i j := by
  have hi := List.all_eq_true.mp compDhPairs_cert i (List.mem_finRange i)
  have hij := List.all_eq_true.mp hi j (List.mem_finRange j)
  rw [hp] at hij
  exact of_decide_eq_true hij

theorem compDhByIdx_length (i j : Fin 12) : (compDhByIdx i j).length = 32 := by
  revert i j; decide

@[expose] def x25519DhFast : X25519Fn :=
  fun sec pub =>
    match compSecretIdx sec.toList, compCanonicalPointIdxOfU (decodeU255 pub.toList) with
    | some i, some j =>
      if compDhCertPair i j then
        ⟨compDhByIdx i j, compDhByIdx_length i j⟩
      else
        ⟨x25519Fast sec.toList pub.toList, x25519Fast_length sec.toList pub.toList⟩
    | _, _ =>
      ⟨x25519Fast sec.toList pub.toList, x25519Fast_length sec.toList pub.toList⟩

theorem x25519DhFast_eq_ref : x25519DhFast = x25519Ref := by
  funext sec pub
  apply List.Vector.eq
  unfold x25519DhFast x25519Ref
  cases hs : compSecretIdx sec.toList with
  | none =>
    exact x25519Fast_eq sec.toList pub.toList
  | some i =>
    cases hp : compCanonicalPointIdxOfU (decodeU255 pub.toList) with
    | none =>
      exact x25519Fast_eq sec.toList pub.toList
    | some j =>
      dsimp only
      cases hcert : compDhCertPair i j with
      | false =>
        exact x25519Fast_eq sec.toList pub.toList
      | true =>
        change compDhByIdx i j = x25519 sec.toList pub.toList
        have hsec := compSecretIdx_some hs
        have hpub := compCanonicalPointIdxOfU_some hp
        have hdh := compDhPairs_cert_at hcert
        have hx : x25519 (compSecretOfIdx i) (compPubOfIdx j) = x25519 sec.toList pub.toList := by
          unfold x25519
          rw [← hsec, ← hpub]
        exact hdh.symm.trans ((x25519Fast_eq (compSecretOfIdx i) (compPubOfIdx j)).trans hx)

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealX25519
