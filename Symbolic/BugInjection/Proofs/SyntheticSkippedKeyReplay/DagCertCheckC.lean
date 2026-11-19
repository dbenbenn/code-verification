/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.DagCertCheckB

/-!
# Concrete Evaluation DAG Bucket & Collision Certificate Checks
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


theorem dag_buckets_mem_100_33 :
    (List.range' 100 33).all dagBucketMemOk = true := by decide +kernel

theorem dag_buckets_mem_133_33 :
    (List.range' 133 33).all dagBucketMemOk = true := by decide +kernel

theorem dag_buckets_mem_166_33 :
    (List.range' 166 33).all dagBucketMemOk = true := by decide +kernel

theorem dag_buckets_ok_0_128 :
    (List.range' 0 128).all (fun b => bucketNoCollision (dagBucket b)) = true := by decide +kernel

theorem dag_buckets_ok_128_128 :
    (List.range' 128 128).all (fun b => bucketNoCollision (dagBucket b)) = true := by decide +kernel

theorem dag_no_ai_0100_bool :
    (List.range dagSize).all (fun id => !(dagOp id).isAI || !endsWith0100 (dagBytes id)) = true := by
  decide +kernel

end Step1DagSafeMemo

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
