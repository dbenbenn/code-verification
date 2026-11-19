/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.DagCertCheckA

/-!
# Concrete Evaluation DAG Certificate Checks (Nodes 100–198 & Buckets)
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

section Step1DagSafeMemo

open DY.Libsignal.Refinement (canonicalVariation sha256CompressFunction)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain TRSignalMsg trHonestWireMsg messageVersion spqrA2B spqrB2A lit litByte
   hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys kdfCk computeMac)
open DY.Libsignal.Composed.Refinement
  (TrialCtx trialTerms trWireBytes litOf clamp ofByteArray node opaqueNode spqrKeyNode
   concretizeLit concretizeConcat concretizeDhPk concretizeDh concretizeKdf
   concretizeSym concretizeTrunc concretizeTrWire concretizeKemEncap concretizeKemSS
   concretizeKemPk concretizeVk concretizeSign
   concretizeSpqrInit concretizeSpqrChainKey concretizeSpqrSendState
   concretizeSpqrSendKey concretizeSpqrSendMsg concretizeSpqrRecvState concretizeSpqrRecvKey
   sigFuns spqrFuns allFuns)
open ByteSpecs (hmacWith)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (compLookupPub compLookupDh compAesPerm compKyberEncaps bytesToNat)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compI0_publicKey compI0_agreement compI0_aesEncrypt compI0_kyberEncaps compLookupDh_comm)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (recvTailTerm stateAnchorPair trStateProxyRoots serialize_localTR_memo)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (BinTree btGet)


theorem dag_nodes_ok_100_16 :
    (List.range' 100 16).all (compDagNodeOk dagOp dagBytes) = true := by decide +kernel

theorem dag_nodes_ok_116_16 :
    (List.range' 116 16).all (compDagNodeOk dagOp dagBytes) = true := by decide +kernel

theorem dag_nodes_ok_132_16 :
    (List.range' 132 16).all (compDagNodeOk dagOp dagBytes) = true := by decide +kernel

theorem dag_nodes_ok_148_17 :
    (List.range' 148 17).all (compDagNodeOk dagOp dagBytes) = true := by decide +kernel

theorem dag_nodes_ok_165_17 :
    (List.range' 165 17).all (compDagNodeOk dagOp dagBytes) = true := by decide +kernel

theorem dag_nodes_ok_182_17 :
    (List.range' 182 17).all (compDagNodeOk dagOp dagBytes) = true := by decide +kernel

end Step1DagSafeMemo

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
