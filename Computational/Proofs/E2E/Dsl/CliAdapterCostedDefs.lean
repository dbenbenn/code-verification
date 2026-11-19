/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.TablesHonest -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.CliPqAdapterDefs
public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import Computational.Specifications.Session.StatementSession
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Definitions and Syntax-Size Bounds for `cliToModelAdapterProgTbl`

Extracts the `Ty.tbl`-backed binary-harness adapter AST (`cliToModelAdapterProgTbl`) and its
budget-independent `reductionSizeBudget` bound so downstream per-kind cost modules do not wait on
full adapter step-cost, query-bound, and experiment-equivalence proofs.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs

open OracleSpec
open _root_.ReductionDsl (Ty Var Expr Comp Ops Iface GameCodec CostedReduction bits)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification.SignalSession (stdinCapBytes)
open CryptoVerification.E2E (Bytes BHDRCtlQuery ModelDriverBase bhGameSpec bhTargetGameSpec bhInitRegId)
open CryptoVerification.E2E.Costed (e2eSig PB B PU32 U32 FinT PlainT BV512 BinStT GhostStT
  bundleT bundleV hdrT hdrV sidT keyIndQT keyIndRT smQT smRT recvResultT
  E2EPureOp e2ePureOps e2eAdapterOps E2EAdapterTag e2eAdapterIface e2eAdapterCodec)
open Computational.Proofs.E2E.Dsl.TablesHonest (adapterPureOp adapterInstMetaT adapterStateTy
  adapterNoneSmRespExpr adapterCrArm)

@[expose] def bhCtlUnStart {S : SignalPqxdh.Setup} : BHDRCtlQuery S → SignalPqxdh.SessionId S
  | .startDR sid => sid

@[expose, reducible] def e2eBhAdapterIface (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    Iface (e2eSig ℓ) (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) :=
  e2eAdapterIface S ℓ BHDRCtlQuery.startDR

@[expose, reducible] def e2eBhAdapterCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    GameCodec (e2eSig ℓ) (bhGameSpec S ℓ (BitVec 512)) :=
  e2eAdapterCodec S ℓ bhCtlUnStart

abbrev CliToModelAdapterProgHonest (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Type :=
  CostedReduction (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
    (bhGameSpec S ℓ (BitVec 512))
    (e2eBhAdapterCodec S ℓ) .unit .unit .bool .bool


section Helpers

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

@[expose, reducible] def cliQuery {Γ : List (Ty (e2eSig ℓ))} (g : E2EAdapterTag)
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ ((e2eBhAdapterIface S ℓ).dom g)) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) Γ
      ((e2eBhAdapterIface S ℓ).cod g) :=
  Comp.query (O := e2eAdapterOps ℓ decT encT) (I := e2eBhAdapterIface S ℓ) g e

@[expose] def isEmptyBytesExpr {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 32)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .bool :=
  .eqN (adapterPureOp (.bytesLen 32) e) (.nat 0)


/-- Test whether a byte slice fits within `stdinCapBytes` (`DEV-CLI21`). -/
@[expose] def capOkBytesExpr {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 32)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .bool :=
  .not (.lt (.nat stdinCapBytes) (adapterPureOp (.bytesLen 32) e))


@[expose] def initRegIdExpr {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ U32 :=
  .caseSum s
    (adapterPureOp .u32OfNat (adapterPureOp (.finVal S.N_id) (.fst .v0)))
    (.caseSum .v0
      (adapterPureOp .u32OfNat (adapterPureOp (.finVal S.N_id) (.fst .v0)))
      (adapterPureOp (.u32Lit 0#32) .unit))


end Helpers

@[expose] def packBytesLE : Bytes → ℕ
  | [] => 0
  | b :: bs => b.toNat + 256 * packBytesLE bs

@[expose] def pack1568Key4 (ub : SignalPqxdh.Bytes) : ℕ × ℕ × ℕ × ℕ :=
  let bs := CryptoVerification.E2E.ofU8 ub
  (packBytesLE ((bs.drop 0).take 392),
   (packBytesLE ((bs.drop 392).take 392),
    (packBytesLE ((bs.drop 784).take 392),
     packBytesLE ((bs.drop 1176).take 392))))

@[expose, reducible] def bundlesTblTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .tbl (.tbl (.tbl (.tbl (.tbl (.tbl (.opt (.prod (FinT S.N_id) (FinT S.N_recv))))))))

@[expose, reducible] def opksTblTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .tbl (.tbl (.tbl (.opt (PB 32))))

@[expose, reducible] def sendsHalfTblTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .tbl (.tbl (.opt (.prod bundleT hdrT)))

/-- Nested `Ty.tbl` mirror type for `ModelDriverBase S`. -/
@[expose, reducible] def drvMirrorTblTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (.tbl (.opt (PB 32)))
    (.prod (bundlesTblTy S ℓ)
      (.prod (opksTblTy ℓ)
        (.prod (sendsHalfTblTy ℓ) (sendsHalfTblTy ℓ))))

@[expose, reducible] def cliAdapterTblStateTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  adapterStateTy (drvMirrorTblTy S ℓ)

@[expose] def prinsTblOfList {S : SignalPqxdh.Setup}
    (l : List (Fin S.N_id × SignalPqxdh.Bytes)) : ℕ → Option SignalPqxdh.Bytes :=
  l.foldr (fun e tbl k => if k = e.1.val then some e.2 else tbl k) (fun _ => none)

@[expose] def bundlesTblOfList {S : SignalPqxdh.Setup}
    (l : List ((Fin S.N_id × Fin S.N_recv) × SignalPqxdh.Bytes × SignalPqxdh.Bytes)) :
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Option (Fin S.N_id × Fin S.N_recv) :=
  l.foldr (fun e tbl kJ kSpk k0 k1 k2 k3 =>
    let jKey := (UInt32.ofNat e.1.2.val).toNat
    let spkKey := packBytesLE (CryptoVerification.E2E.ofU8 e.2.1)
    let (p0, (p1, (p2, p3))) := pack1568Key4 e.2.2
    if kJ = jKey ∧ kSpk = spkKey ∧ k0 = p0 ∧ k1 = p1 ∧ k2 = p2 ∧ k3 = p3 then
      some e.1
    else
      tbl kJ kSpk k0 k1 k2 k3)
    (fun _ _ _ _ _ _ => none)

@[expose] def opksTblOfList {S : SignalPqxdh.Setup}
    (l : List ((Fin S.N_id × Fin S.N_recv × Fin S.N_opk) × SignalPqxdh.Bytes)) :
    ℕ → ℕ → ℕ → Option SignalPqxdh.Bytes :=
  l.foldr (fun e tbl ku kj ko =>
    if ku = e.1.1.val ∧ kj = e.1.2.1.val ∧ ko = e.1.2.2.val then some e.2
    else tbl ku kj ko)
    (fun _ _ _ => none)

@[expose] def sendsOpkTblOfList {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (l : List (SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr)) :
    ℕ → ℕ → Option ((Ty.prod (bundleT (ℓ := ℓ)) hdrT).denote) :=
  l.foldr (fun e tbl ku ki =>
    match e.1 with
    | .sendOPK u i =>
      if ku = u.val ∧ ki = i.val then some (bundleV (ℓ := ℓ) e.2.1, hdrV (ℓ := ℓ) e.2.2)
      else tbl ku ki
    | _ => tbl ku ki)
    (fun _ _ => none)

@[expose] def sendsNoOpkTblOfList {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (l : List (SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr)) :
    ℕ → ℕ → Option ((Ty.prod (bundleT (ℓ := ℓ)) hdrT).denote) :=
  l.foldr (fun e tbl ku ki =>
    match e.1 with
    | .sendNoOPK u i =>
      if ku = u.val ∧ ki = i.val then some (bundleV (ℓ := ℓ) e.2.1, hdrV (ℓ := ℓ) e.2.2)
      else tbl ku ki
    | _ => tbl ku ki)
    (fun _ _ => none)

@[expose] def drvMirrorTblToV {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : ModelDriverBase S) :
    (drvMirrorTblTy S ℓ).denote :=
  (prinsTblOfList d.prins,
   (bundlesTblOfList d.bundles,
    (opksTblOfList d.opks,
     (sendsOpkTblOfList (ℓ := ℓ) d.sends, sendsNoOpkTblOfList (ℓ := ℓ) d.sends))))

@[expose] def natListLitE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    List ℕ → Expr O Γ (.list .nat)
  | [] => .nil
  | k :: ks => .cons (.nat k) (natListLitE ks)

@[expose] def byte1ToNatE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 1)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .caseOpt
    (adapterPureOp .spqrParsePreamble
      (adapterPureOp (.bytesWiden 3 29)
        (adapterPureOp (.bytesCat 1 2)
          (.pair e (adapterPureOp (.bytesLit 2 [1#8, 0#8]) .unit)))))
    (.nat 0)
    (adapterPureOp .u8ToNat (.fst .v0))

@[expose] def pack8BytesE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 8)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .letE e
    (.foldrB 8 (natListLitE (List.range 8)) (.nat 0)
      (.add
        (byte1ToNatE
          (adapterPureOp (.bytesTakeK 8 1)
            (adapterPureOp (.bytesDrop 8) (.pair .v0 .v2))))
        (.mulK 256 .v1)))

@[expose] def pack32PbytesE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 32)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .letE (adapterPureOp (.pbytesToBytes 32) e)
    (.foldrB 4 (natListLitE (List.range 4)) (.nat 0)
      (.add
        (pack8BytesE
          (adapterPureOp (.bytesTakeK 32 8)
            (adapterPureOp (.bytesDrop 32) (.pair (.mulK 8 .v0) .v2))))
        (.mulK (256 ^ 8) .v1)))

@[expose] def pack56BytesE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 56)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .letE e
    (.foldrB 7 (natListLitE (List.range 7)) (.nat 0)
      (.add
        (pack8BytesE
          (adapterPureOp (.bytesTakeK 56 8)
            (adapterPureOp (.bytesDrop 56) (.pair (.mulK 8 .v0) .v2))))
        (.mulK (256 ^ 8) .v1)))

@[expose] def pack392BytesE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 392)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .letE e
    (.foldrB 7 (natListLitE (List.range 7)) (.nat 0)
      (.add
        (pack56BytesE
          (adapterPureOp (.bytesTakeK 392 56)
            (adapterPureOp (.bytesDrop 392) (.pair (.mulK 56 .v0) .v2))))
        (.mulK (256 ^ 56) .v1)))

@[expose] def pack1568Key4E {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 1568)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (.prod .nat (.prod .nat (.prod .nat .nat))) :=
  .letE (adapterPureOp (.pbytesToBytes 1568) e)
    (.pair
      (pack392BytesE
        (adapterPureOp (.bytesTakeK 1568 392)
          (adapterPureOp (.bytesDrop 1568) (.pair (.nat 0) .v0))))
      (.pair
        (pack392BytesE
          (adapterPureOp (.bytesTakeK 1568 392)
            (adapterPureOp (.bytesDrop 1568) (.pair (.nat 392) .v0))))
        (.pair
          (pack392BytesE
            (adapterPureOp (.bytesTakeK 1568 392)
              (adapterPureOp (.bytesDrop 1568) (.pair (.nat 784) .v0))))
          (pack392BytesE
            (adapterPureOp (.bytesTakeK 1568 392)
              (adapterPureOp (.bytesDrop 1568) (.pair (.nat 1176) .v0)))))))

@[expose] def tset2E {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl t)))
    (k0 k1 : Expr O Γ .nat) (val : Expr O Γ t) :
    Expr O Γ (.tbl (.tbl t)) :=
  .letE (.pair m (.pair k0 (.pair k1 val)))
    (let m0 := Expr.fst .v0
     let i0 := Expr.fst (.snd .v0)
     let i1 := Expr.fst (.snd (.snd .v0))
     let vE := Expr.snd (.snd (.snd .v0))
     .tset m0 i0 (.tset (.tget m0 i0) i1 vE))

@[expose] def tset3E {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl (.tbl t))))
    (k0 k1 k2 : Expr O Γ .nat) (val : Expr O Γ t) :
    Expr O Γ (.tbl (.tbl (.tbl t))) :=
  .letE (.pair m (.pair k0 (.pair k1 (.pair k2 val))))
    (.letE (.tget (.fst .v0) (.fst (.snd .v0)))
      (let m0 := Expr.fst .v1
       let i0 := Expr.fst (.snd .v1)
       let i1 := Expr.fst (.snd (.snd .v1))
       let i2 := Expr.fst (.snd (.snd (.snd .v1)))
       let vE := Expr.snd (.snd (.snd (.snd .v1)))
       .tset m0 i0 (.tset .v0 i1 (.tset (.tget .v0 i1) i2 vE))))

@[expose] def tset6E {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl (.tbl (.tbl (.tbl (.tbl t)))))))
    (k0 k1 k2 k3 k4 k5 : Expr O Γ .nat) (val : Expr O Γ t) :
    Expr O Γ (.tbl (.tbl (.tbl (.tbl (.tbl (.tbl t)))))) :=
  .letE (.pair m (.pair k0 (.pair k1 (.pair k2 (.pair k3 (.pair k4 (.pair k5 val)))))))
    (.letE (.tget (.fst .v0) (.fst (.snd .v0)))
      (.letE (.tget .v0 (.fst (.snd (.snd .v1))))
        (.letE (.tget .v0 (.fst (.snd (.snd (.snd .v2)))))
          (let tup := Expr.v3
           let m0 := Expr.fst tup
           let i0 := Expr.fst (.snd tup)
           let i1 := Expr.fst (.snd (.snd tup))
           let i2 := Expr.fst (.snd (.snd (.snd tup)))
           let i3 := Expr.fst (.snd (.snd (.snd (.snd tup))))
           let i4 := Expr.fst (.snd (.snd (.snd (.snd (.snd tup)))))
           let i5 := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd tup))))))
           let vE := Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd tup))))))
           .tset m0 i0
             (.tset .v2 i1
               (.tset .v1 i2
                 (tset3E .v0 i3 i4 i5 vE)))))))

@[expose] def stepBaseMirrorTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ) :=
  .letE (.pair drv (.pair kq kr))
    (.caseSum (.fst (.snd .v0))
      (.caseSum (.snd (.snd .v1))
        (.fst .v2)
        (.caseSum .v0
          (.pair
            (.tset (.fst (.fst .v3)) (adapterPureOp (.finVal S.N_id) .v2) (.some (.fst .v0)))
            (.snd (.fst .v3)))
          (.fst .v3)))
      (.caseSum .v0
        (.fst .v2)
        (.caseSum .v0
          (.caseSum (.snd (.snd .v3))
            (.fst .v4)
            (.caseSum .v0
              (.fst .v5)
              (.caseSum .v0
                (.fst .v6)
                (.caseSum .v0
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (let pqspkB := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
                     .letE (pack1568Key4E pqspkB)
                       (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTblTy S ℓ) :=
                          .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                        let ujE := Expr.v6
                        let spkB := Expr.fst (.snd (.snd .v1))
                        let jKeyE := adapterPureOp .pu32ToNat
                          (adapterPureOp .pu32OfNat (adapterPureOp (.finVal S.N_recv) (.snd ujE)))
                        let spkKeyE := pack32PbytesE spkB
                        .pair (.fst dE)
                          (.pair
                            (tset6E (.fst (.snd dE)) jKeyE spkKeyE
                              (.fst .v0) (.fst (.snd .v0))
                              (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
                              (.some ujE))
                            (.snd (.snd dE)))))
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))
          (.caseSum .v0
            (.caseSum (.snd (.snd .v4))
              (.fst .v5)
              (.caseSum .v0
                (.fst .v6)
                (.caseSum .v0
                  (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTblTy S ℓ) :=
                     .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
                   let ujo := Expr.v3
                   .pair (.fst dE)
                     (.pair (.fst (.snd dE))
                       (.pair
                         (tset3E (.fst (.snd (.snd dE)))
                           (adapterPureOp (.finVal S.N_id) (.fst ujo))
                           (adapterPureOp (.finVal S.N_recv) (.fst (.snd ujo)))
                           (adapterPureOp (.finVal S.N_opk) (.snd (.snd ujo)))
                           (.some .v0))
                         (.snd (.snd (.snd dE))))))
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
            (.caseSum .v0
              (.caseSum (.snd (.snd .v5))
                (.fst .v6)
                (.caseSum .v0
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                    (.caseSum .v0
                      (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
                      (.caseSum .v0
                        (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                        (.caseSum .v0
                          (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTblTy S ℓ) :=
                             .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                           let uib := Expr.v6
                           let bndE := Expr.snd (.snd uib)
                           .pair (.fst dE)
                             (.pair (.fst (.snd dE))
                               (.pair (.fst (.snd (.snd dE)))
                                 (.pair
                                   (tset2E (.fst (.snd (.snd (.snd dE))))
                                     (adapterPureOp (.finVal S.N_id) (.fst uib))
                                     (adapterPureOp (.finVal S.N_send_opk) (.fst (.snd uib)))
                                     (.some (.pair bndE .v0)))
                                   (.snd (.snd (.snd (.snd dE))))))))
                          (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))))))
              (.caseSum .v0
                (.caseSum (.snd (.snd .v6))
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                    (.caseSum .v0
                      (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
                      (.caseSum .v0
                        (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                        (.caseSum .v0
                          (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
                          (.caseSum .v0
                            (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTblTy S ℓ) :=
                               .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
                             let uib := Expr.v6
                             let bndE := Expr.snd (.snd uib)
                             .pair (.fst dE)
                               (.pair (.fst (.snd dE))
                                 (.pair (.fst (.snd (.snd dE)))
                                   (.pair
                                     (.fst (.snd (.snd (.snd dE))))
                                     (tset2E (.snd (.snd (.snd (.snd dE))))
                                       (adapterPureOp (.finVal S.N_id) (.fst uib))
                                       (adapterPureOp (.finVal S.N_send_no_opk) (.fst (.snd uib)))
                                       (.some (.pair bndE .v0)))))))
                            (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))))))))
                (.fst .v6)))))))

@[expose] def guardPromoteTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (.opt adapterInstMetaT) :=
  .letE (.pair drv sid)
    (let sendsLookup : Expr (e2eAdapterOps ℓ decT encT) _ (.opt (.prod bundleT hdrT)) :=
       .caseSum (.snd .v0)
         (.tget
           (.tget (.fst (.snd (.snd (.snd (.fst .v1)))))
             (adapterPureOp (.finVal S.N_id) (.fst .v0)))
           (adapterPureOp (.finVal S.N_send_opk) (.snd .v0)))
         (.caseSum .v0
           (.tget
             (.tget (.snd (.snd (.snd (.snd (.fst .v2)))))
               (adapterPureOp (.finVal S.N_id) (.fst .v0)))
             (adapterPureOp (.finVal S.N_send_no_opk) (.snd .v0)))
           .none)
     .caseOpt sendsLookup
       .none
       (let bnd := Expr.fst .v0
        let hdr := Expr.snd .v0
        let bndSpkB := Expr.fst (.snd (.snd bnd))
        let bndPqspkB := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd bnd))))))
        let hdrSpkId := Expr.fst (.snd (.snd hdr))
        let hdrPqspkId := Expr.fst (.snd (.snd (.snd (.snd hdr))))
        let preOk :=
          Expr.and (adapterPureOp .pu32Eq (.pair hdrSpkId hdrPqspkId))
            (.and (.eqN (adapterPureOp (.pbytesLen 32) bndSpkB) (.nat 32))
                  (.eqN (adapterPureOp (.pbytesLen 1568) bndPqspkB) (.nat 1568)))
        .ite preOk
          (.letE (pack1568Key4E bndPqspkB)
            (let bnd' := Expr.fst .v1
             let hdr' := Expr.snd .v1
             let bndSpkB' := Expr.fst (.snd (.snd bnd'))
             let hdrSpkId' := Expr.fst (.snd (.snd hdr'))
             let bndTbl := Expr.fst (.snd (.fst .v2))
             let foundBnd :=
               Expr.tget
                 (.tget
                   (.tget
                     (.tget
                       (.tget
                         (.tget bndTbl (adapterPureOp .pu32ToNat hdrSpkId'))
                         (pack32PbytesE bndSpkB'))
                       (.fst .v0))
                     (.fst (.snd .v0)))
                   (.fst (.snd (.snd .v0))))
                 (.snd (.snd (.snd .v0)))
             .caseOpt foundBnd
               .none
               (let uResp := Expr.fst .v0
                let bnd2 := Expr.fst .v2
                let prinsOk : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
                  .caseOpt
                    (.tget (.fst (.fst .v3)) (adapterPureOp (.finVal S.N_id) uResp))
                    (.bool false)
                    (adapterPureOp (.pbytesEq 32 32) (.pair .v0 (.fst (.fst .v3))))
                let bndOpkOpt := Expr.fst (.snd (.snd (.snd (.snd bnd2))))
                let opkOk : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
                  .caseOpt bndOpkOpt
                    (.bool true)
                    (.caseOpt
                      (.tget
                        (.tget
                          (.tget (.fst (.snd (.snd (.fst .v4))))
                            (adapterPureOp (.finVal S.N_id) (.fst .v1)))
                          (adapterPureOp (.finVal S.N_recv) (.snd .v1)))
                        (adapterPureOp .pu32ToNat (.fst .v0)))
                      (.bool false)
                      (adapterPureOp (.pbytesEq 32 32) (.pair .v0 (.snd .v1))))
                .ite (.and prinsOk opkOk)
                  (let regIdA := initRegIdExpr (.snd .v3)
                   let regIdB := adapterPureOp .u32OfNat (adapterPureOp (.finVal S.N_id) uResp)
                   let hdr2 := Expr.snd .v2
                   .some (.pair (.pair regIdA (.pair regIdB (.pair regIdA hdr2))) (.bool false)))
                  .none)))
          .none))

@[expose] def cliBobUpdateStateTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (σVar : Var (.opt recvResultT :: Γ) (cliAdapterTblStateTy S ℓ))
    (instIdxVar : Var (.opt recvResultT :: Γ) .nat)
    (instVar : Var (.opt recvResultT :: Γ) adapterInstMetaT)
    (mRegIdVar : Var (.opt recvResultT :: Γ) U32) :
    Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ) (cliAdapterTblStateTy S ℓ) :=
  .caseOpt .v0 (.var σVar)
    (.caseSum .v0 (.var (.succ (.succ σVar)))
      (let σE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ σVar))
       let idxE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instIdxVar))
       let instE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instVar))
       let mRegE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ mRegIdVar))
       let regIdA := Expr.fst (.fst instE)
       let regIdB := Expr.fst (.snd (.fst instE))
       let oldBobRem := Expr.fst (.snd (.snd (.fst instE)))
       let instHdr := Expr.snd (.snd (.snd (.fst instE)))
       let bobAcc := Expr.snd instE
       let newBobRem := Expr.ite (.not bobAcc) mRegE oldBobRem
       let newInst := Expr.pair (.pair regIdA (.pair regIdB (.pair newBobRem instHdr))) (.bool true)
       .pair (.tset (.fst σE) idxE (.some newInst)) (.snd σE)))

@[expose] def cliAliceUpdateStateTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (σVar : Var (.opt recvResultT :: Γ) (cliAdapterTblStateTy S ℓ))
    (instIdxVar : Var (.opt recvResultT :: Γ) .nat) :
    Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ) (cliAdapterTblStateTy S ℓ) :=
  .caseOpt .v0 (.var σVar)
    (.caseSum .v0 (.var (.succ (.succ σVar)))
      (let σE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ σVar))
       let idxE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instIdxVar))
       .pair (.fst σE)
         (.pair (.tset (.fst (.snd σE)) idxE (.bool true))
                (.snd (.snd σE)))))

@[expose] def cliAdapterKiOrCtlArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.sum (keyIndQT S) (sidT S), cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseSum .v0
    (.bind (cliQuery E2EAdapterTag.ki .v0)
      (.ret (.pair (.inl (.inl .v0))
        (.pair (.fst .v3)
          (.pair (.fst (.snd .v3))
            (stepBaseMirrorTblExpr (.snd (.snd .v3)) .v1 .v0))))))
    (.bind (cliQuery E2EAdapterTag.ctl .v0)
      (.caseOpt .v0
        (.ret (.pair (.inl (.inr .none)) .v3))
        (.caseOpt (guardPromoteTblExpr (.snd (.snd .v4)) .v2)
          (.ret (.pair (.inl (.inr (.some .v0))) .v4))
          (.ret (.pair (.inl (.inr (.some .v1)))
            (.pair (.tset (.fst .v5) .v1 (.some .v0)) (.snd .v5)))))))

@[expose] def cliAdapterTrArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (.prod PlainT (.opt BV512)),
       .prod .nat smQT, cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseOpt (.tget (.fst .v2) (.fst .v1))
    (.ret (.pair adapterNoneSmRespExpr .v2))
    (.bind (cliQuery E2EAdapterTag.tr (.pair (.fst .v2) .v1))
      (.caseOpt .v0
        (.ret (.pair adapterNoneSmRespExpr .v4))
        (let regIdA := Expr.fst (.fst .v2)
         let instHdr := Expr.snd (.snd (.snd (.fst .v2)))
         let wire :=
           Expr.ite (.fst .v3)
             (adapterPureOp .wrapWhisperWire .v0)
             (.ite (.tget (.fst (.snd .v5)) (.fst .v4))
               (adapterPureOp .wrapWhisperWire .v0)
               (adapterPureOp .wrapPreKeyWire (.pair regIdA (.pair instHdr .v0))))
         .ret (.pair (.inr (.pair (.some wire) (.pair .none .none))) .v5))))

@[expose] def cliAdapterChArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseOpt (.tget (.fst .v3) (.fst .v2))
    (.ret (.pair adapterNoneSmRespExpr .v3))
    (.bind (cliQuery E2EAdapterTag.ch (.pair (.fst .v3) .v1))
      (.caseOpt .v0
        (.ret (.pair adapterNoneSmRespExpr .v5))
        (let regIdA := Expr.fst (.fst .v2)
         let instHdr := Expr.snd (.snd (.snd (.fst .v2)))
         let wire :=
           Expr.ite (.fst .v3)
             (adapterPureOp .wrapWhisperWire .v0)
             (.ite (.tget (.fst (.snd .v6)) (.fst .v5))
               (adapterPureOp .wrapWhisperWire .v0)
               (adapterPureOp .wrapPreKeyWire (.pair regIdA (.pair instHdr .v0))))
         .ret (.pair (.inr (.pair (.some wire) (.pair .none .none))) .v6))))

@[expose] def cliAdapterDlArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (B 32),
       .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .ite (.fst .v0)
    (.caseOpt (.tget (.fst .v4) (.fst .v3))
      (.ret (.pair adapterNoneSmRespExpr .v4))
      (.caseOpt (adapterPureOp .parsePreKeyWire (.snd .v1))
        (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v1))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v4) (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
            (.ret (.pair adapterNoneSmRespExpr .v6)))
          (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
            (.ite (isEmptyBytesExpr .v0)
              (.bind (cliQuery E2EAdapterTag.ij
                  (.pair (.fst .v5) (.pair (.bool true) (adapterPureOp .wrapWhisperWire .v0))))
                (.ret (.pair adapterNoneSmRespExpr
                  (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
              (.bind (cliQuery E2EAdapterTag.dl (.pair (.fst .v5) (.pair (.bool true) .v0)))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
            (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) (.pair (.bool true) (.snd .v3))))
              (.ret (.pair adapterNoneSmRespExpr
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))
        (.ite (isEmptyBytesExpr (.snd (.snd .v0)))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v5)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd (.snd .v0))))))
            (.ret (.pair adapterNoneSmRespExpr
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
          (.bind (.ret (.fst .v5))
            (.bind (.ret (.fst .v1))
              (.bind (cliQuery E2EAdapterTag.dl (.pair .v1 .v4))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (cliBobUpdateStateTblExpr
                    (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                    (.succ (.succ .zero))
                    (.succ (.succ (.succ (.succ .zero))))
                    (.succ .zero))))))))))
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.ite (isEmptyBytesExpr (.snd .v0))
        (.bind (cliQuery E2EAdapterTag.dl (.pair (.fst .v3) .v0))
          (.ret (.pair (.inr (.pair .none (.pair .v0 .none))) .v5)))
        (.ret (.pair adapterNoneSmRespExpr .v4)))
      (.ite (isEmptyBytesExpr .v0)
        (.ret (.pair adapterNoneSmRespExpr .v5))
        (.bind (.ret (.fst .v4))
          (.bind (cliQuery E2EAdapterTag.dl (.pair .v0 (.pair (.bool false) .v1)))
            (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
              (cliAliceUpdateStateTblExpr
                (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
                (.succ .zero))))))))

@[expose] def cliAdapterIjArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (B 32),
       .sum (.prod .bool (B 32)) .bool,
       .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .ite (.fst .v0)
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.caseOpt (adapterPureOp .parsePreKeyWire (.snd .v0))
        (.bind (cliQuery E2EAdapterTag.ij
            (.pair (.fst .v4) (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v0)))))
          (.ret (.pair adapterNoneSmRespExpr .v6)))
        (.ite (.and (capOkBytesExpr (.snd .v1))
            (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) (.some (.snd (.snd .v0))))))
          (.caseOpt (.tget (.fst .v6) (.fst .v5))
            (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v5) .v1))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (let bobAcc := Expr.snd .v0
             let regIdA := Expr.fst (.fst .v0)
             let instHdr := Expr.snd (.snd (.snd (.fst .v0)))
             let eqHdrExpr : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
               .caseOpt (adapterPureOp .partneredInnerBytes
                   (.pair bobAcc (.pair regIdA (.pair instHdr (.snd .v2)))))
                 (.bool false) (.bool true)
             .ite (isEmptyBytesExpr (.snd (.snd .v1)))
               (.ite eqHdrExpr
                 (.bind (cliQuery E2EAdapterTag.ij
                     (.pair (.fst .v6)
                       (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v2)))))
                   (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                     (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                 (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) .v2))
                   (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                     (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
               (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) .v2))
                 (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                   (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v5)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
            (.ret (.pair adapterNoneSmRespExpr
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
      (.ite (.and (capOkBytesExpr (.snd .v1))
          (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) .none)))
        (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
          (.ite (isEmptyBytesExpr .v0)
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5)
                  (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5) (.pair (.bool true) .v0)))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v6)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire .v1))))
            (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
        (.bind (cliQuery E2EAdapterTag.ij
            (.pair (.fst .v5)
              (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
          (.ret (.pair adapterNoneSmRespExpr
            (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.ret (.pair adapterNoneSmRespExpr .v5))
      (.ite (.and (capOkBytesExpr (.snd .v1))
          (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) .none)))
        (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
          (.ite (isEmptyBytesExpr .v0)
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5)
                  (.pair (.bool false) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (.bind (.ret (.fst .v5))
              (.bind (cliQuery E2EAdapterTag.ij (.pair .v0 (.pair (.bool false) .v1)))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (cliAliceUpdateStateTblExpr
                    (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
                    (.succ .zero)))))))
          (.bind (.ret (.fst .v6))
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair .v0 (.pair (.bool false) (adapterPureOp .wrapWhisperWire .v2))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (cliAliceUpdateStateTblExpr
                  (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.succ .zero)))))))
        (.ret (.pair adapterNoneSmRespExpr .v6))))

@[expose] def cliAdapterHandleTbl {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseSum (.var (.succ .zero))
    (cliAdapterKiOrCtlArmTbl S ℓ decT encT)
    (.caseSum (.snd .v0)
      (cliAdapterTrArmTbl S ℓ decT encT)
      (.caseSum .v0
        (cliAdapterChArmTbl S ℓ decT encT)
        (.caseSum .v0
          (cliAdapterDlArmTbl S ℓ decT encT)
          (.caseSum .v0
            (cliAdapterIjArmTbl S ℓ decT encT)
            (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
              (drvMirrorTblTy S ℓ))))))

/-- Budget-independent `Ty.tbl`-backed `CostedReduction` adapter `cliToModelAdapterProgTbl`. -/
@[expose] def cliToModelAdapterProgTbl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProgHonest S ℓ decT encT where
  σ := cliAdapterTblStateTy S ℓ
  init :=
    .ret (.pair
      .unit
      (.pair (.tconst .none)
        (.pair (.tconst (.bool false))
          (.pair (.tconst .none)
            (.pair (.tconst (.tconst (.tconst (.tconst (.tconst (.tconst .none))))))
              (.pair (.tconst (.tconst (.tconst .none)))
                (.pair (.tconst (.tconst .none)) (.tconst (.tconst .none)))))))))
  handle := cliAdapterHandleTbl decT encT S ℓ
  finish := .ret (.var (.succ .zero))

@[expose] def natListLitCost : List ℕ → ℕ
  | [] => 1
  | k :: ks => bits k + natListLitCost ks + 1

theorem natListLitE_cost {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    ∀ (ns : List ℕ), (natListLitE (O := O) (Γ := Γ) ns).cost = natListLitCost ns
  | [] => rfl
  | _ :: ks => by simp only [natListLitE, Expr.cost, natListLitE_cost ks, natListLitCost]

theorem natListLitE_size {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    ∀ (ns : List ℕ), (natListLitE (O := O) (Γ := Γ) ns).size = natListLitCost ns
  | [] => rfl
  | _ :: ks => by simp only [natListLitE, Expr.size, natListLitE_size ks, natListLitCost]

theorem bits_256_pow_8 : bits (256 ^ 8) = 65 := by
  have hp : (256 : ℕ) ^ 8 = 2 ^ 64 := by
    rw [show (256 : ℕ) = 2 ^ 8 by decide, ← Nat.pow_mul]
  rw [hp, ReductionDsl.bits, Nat.log_pow (by decide : 1 < 2)]

theorem bits_pow_mul {a b k : ℕ} (ha : a = 2 ^ b) : bits (a ^ k) = b * k + 1 := by
  subst ha
  rw [← Nat.pow_mul, ReductionDsl.bits, Nat.log_pow (by decide : 1 < 2)]

theorem bits_256_pow_56 : bits (256 ^ 56) = 449 :=
  (bits_pow_mul (b := 8) (k := 56) (by decide)).trans (by omega)


private theorem byte1ToNatE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 32 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 1)),
      (byte1ToNatE e).size = e.size + c := by
  have hB0 : bits 0 = 1 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    dsimp only [byte1ToNatE, adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim,
      e2ePureOps, Expr.size, E2EPureOp.opSize, List.length_cons, List.length_nil, Expr.v0]
    simp only [hB0, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack8BytesE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 128 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 8)),
      (pack8BytesE e).size = e.size + c := by
  obtain ⟨cb, hcb, hb⟩ := byte1ToNatE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL8 : natListLitCost (List.range 8) = 27 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256 : bits 256 = 9 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack8BytesE
    dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_size, hb]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v2]
    simp only [hL8, hB0, hB8, hB256, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack32PbytesE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 256 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 32)),
      (pack32PbytesE e).size = e.size + c := by
  obtain ⟨c8, hc8, h8⟩ := pack8BytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL4 : natListLitCost (List.range 4) = 11 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB4 : bits 4 = 3 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256_8 := bits_256_pow_8
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack32PbytesE
    dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_size, h8]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v2]
    simp only [hL4, hB0, hB4, hB8, hB256_8, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack56BytesE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 256 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 56)),
      (pack56BytesE e).size = e.size + c := by
  obtain ⟨c8, hc8, h8⟩ := pack8BytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL7 : natListLitCost (List.range 7) = 23 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB7 : bits 7 = 3 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256_8 := bits_256_pow_8
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack56BytesE
    dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_size, h8]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v2]
    simp only [hL7, hB0, hB7, hB8, hB256_8, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack392BytesE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 800 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 392)),
      (pack392BytesE e).size = e.size + c := by
  obtain ⟨c56, hc56, h56⟩ := pack56BytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL7 : natListLitCost (List.range 7) = 23 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB7 : bits 7 = 3 := by decide
  have hB56 : bits 56 = 6 := by decide
  have hB256_56 := bits_256_pow_56
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack392BytesE
    dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_size, h56]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v2]
    simp only [hL7, hB0, hB7, hB56, hB256_56, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack1568Key4E_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 3400 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 1568)),
      (pack1568Key4E e).size = e.size + c := by
  obtain ⟨c392, hc392, h392⟩ := pack392BytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hB0 : bits 0 = 1 := by decide
  have hB392 : bits 392 = 9 := by decide
  have hB784 : bits 784 = 10 := by decide
  have hB1176 : bits 1176 = 11 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack1568Key4E
    dsimp only [Expr.size]
    rw [h392, h392, h392, h392]
    simp only [Nat.zero_add, adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim,
      e2ePureOps, Expr.size, E2EPureOp.opSize, Expr.v0, hB0, hB392, hB784, hB1176, Nat.add_assoc]
    rfl
  case hB =>
    linarith

private theorem stepBaseMirrorTblExpr_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    (stepBaseMirrorTblExpr drv kq kr).size ≤
      32 * drv.size + 32 * kq.size + 32 * kr.size + 6000 := by
  obtain ⟨c1568, hc1568, h1568⟩ := pack1568Key4E_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  obtain ⟨c32, hc32, h32⟩ := pack32PbytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  dsimp only [stepBaseMirrorTblExpr, tset6E, tset3E, tset2E, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [h1568, h32]
  dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
    Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v1]
  omega

private theorem guardPromoteTblExpr_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (guardPromoteTblExpr drv sid).size ≤ 16 * drv.size + 16 * sid.size + 6000 := by
  obtain ⟨c1568, hc1568, h1568⟩ := pack1568Key4E_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  obtain ⟨c32, hc32, h32⟩ := pack32PbytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hB32 : bits 32 = 6 := by decide
  have hB1568 : bits 1568 = 11 := by decide
  dsimp only [guardPromoteTblExpr, initRegIdExpr, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  rw [h1568, h32]
  dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
    Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  simp only [hB32, hB1568]
  omega

private theorem cliAdapterKiOrCtlArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterKiOrCtlArmTbl S ℓ decT encT).size ≤ 14000 := by
  have hMir := stepBaseMirrorTblExpr_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
           cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v3)) .v1 .v0
  have hGrd := guardPromoteTblExpr_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
           cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v4)) .v2
  dsimp only [cliAdapterKiOrCtlArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hMir hGrd ⊢
  omega

private theorem cliAdapterTrArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterTrArmTbl S ℓ decT encT).size ≤ 256 := by
  dsimp only [cliAdapterTrArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
  omega

private theorem cliAdapterChArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterChArmTbl S ℓ decT encT).size ≤ 256 := by
  dsimp only [cliAdapterChArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  omega

private theorem cliAdapterDlArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterDlArmTbl S ℓ decT encT).size ≤ 1024 := by
  have hB0 : bits 0 = 1 := by decide
  dsimp only [cliAdapterDlArmTbl, cliBobUpdateStateTblExpr, cliAliceUpdateStateTblExpr,
    isEmptyBytesExpr, cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr,
    Comp.size, Expr.size, Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp,
    E2EPureOp.opSize, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hB0]
  omega

private theorem cliAdapterIjArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterIjArmTbl S ℓ decT encT).size ≤ 1536 := by
  have hB0 : bits 0 = 1 := by decide
  have hBCap : bits stdinCapBytes = 21 := by decide
  dsimp only [cliAdapterIjArmTbl, cliAliceUpdateStateTblExpr, isEmptyBytesExpr, capOkBytesExpr,
    cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hB0, hBCap]
  omega

theorem size_cliToModelAdapterProgTbl_le_reductionSizeBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget := by
  have h1 := cliAdapterKiOrCtlArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h2 := cliAdapterTrArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h3 := cliAdapterChArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h4 := cliAdapterDlArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h5 := cliAdapterIjArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h6 := Computational.Proofs.E2E.Dsl.TablesHonest.adapterCrArm_size S ℓ
    BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT (drvMirrorTblTy S ℓ)
  dsimp only [CostedReduction.size, _root_.ReductionDsl.reductionSizeBudget,
    cliToModelAdapterProgTbl, cliAdapterHandleTbl, Comp.size, Expr.size, Expr.v0]
  omega


end Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs
