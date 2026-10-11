/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion2BasisProofs
import Biunimodular.F11.HomogeneousCompletion2PairIndex
import Biunimodular.F11.CriticalRelationCertificate
import Biunimodular.F11.HomogeneousCompletion2Pairs01Proofs

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial

def homogeneousCompletion2Certificates : (r : Fin 3) → CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion2GPoly (homogeneousCompletion2MPoly (Fin.last 1)) homogeneousCompletion2PreviousIdeal (homogeneousCompletion2Pairs r) :=
  Fin.cons (α := fun r : Fin 3 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion2GPoly (homogeneousCompletion2MPoly (Fin.last 1)) homogeneousCompletion2PreviousIdeal (homogeneousCompletion2Pairs r))
    ⟨homogeneousCompletion2Pair1_2S, homogeneousCompletion2Pair1_2_relation, homogeneousCompletion2Pair1_2_last, homogeneousCompletion2Pair1_2_top⟩ (Fin.cons (α := fun r : Fin 2 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion2GPoly (homogeneousCompletion2MPoly (Fin.last 1)) homogeneousCompletion2PreviousIdeal (homogeneousCompletion2Pairs r.succ))
    ⟨homogeneousCompletion2Pair1_3S, homogeneousCompletion2Pair1_3_relation, homogeneousCompletion2Pair1_3_last, homogeneousCompletion2Pair1_3_top⟩ (Fin.cons (α := fun r : Fin 1 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion2GPoly (homogeneousCompletion2MPoly (Fin.last 1)) homogeneousCompletion2PreviousIdeal (homogeneousCompletion2Pairs r.succ.succ))
    ⟨homogeneousCompletion2Pair2_3S, homogeneousCompletion2Pair2_3_relation, homogeneousCompletion2Pair2_3_last, homogeneousCompletion2Pair2_3_top⟩ ((fun r : Fin 0 => Fin.elim0 r))))

def homogeneousCompletion2Family : Fin 3 → Fin 3 → MvPolynomial (Fin 6) ℂ :=
  fun r => (homogeneousCompletion2Certificates r).v

theorem homogeneousCompletion2_relations (r : Fin 3) :
    (∑ k, homogeneousCompletion2Family r k * homogeneousCompletion2GPoly k) = 0 := by
  exact (homogeneousCompletion2Certificates r).relation

theorem homogeneousCompletion2_labels (r : Fin 3) :
    relationLabelMap (homogeneousCompletion2MPoly (Fin.last 1)) (homogeneousCompletion2Family r) ∈ homogeneousCompletion2PreviousIdeal := by
  exact (homogeneousCompletion2Certificates r).label

theorem homogeneousCompletion2_tops (r : Fin 3) :
    homogeneousCompletion2Family r (homogeneousCompletion2Pairs r).2 * homogeneousCompletion2GPoly (homogeneousCompletion2Pairs r).2 ≠ 0 ∧
      homogeneousGrevlexOrder.degree (homogeneousCompletion2Family r (homogeneousCompletion2Pairs r).2 * homogeneousCompletion2GPoly (homogeneousCompletion2Pairs r).2) =
        homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly (homogeneousCompletion2Pairs r).1) ⊔
          homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly (homogeneousCompletion2Pairs r).2) ∧
      ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion2GPoly (homogeneousCompletion2Family r) k ≤
        schreyerKey homogeneousGrevlexOrder homogeneousCompletion2GPoly (homogeneousCompletion2Family r) (homogeneousCompletion2Pairs r).2 := by
  exact (homogeneousCompletion2Certificates r).top

theorem homogeneousCompletion2_all_relation_last
    (v : Fin 2 → MvPolynomial (Fin 6) ℂ)
    (hv : (∑ j, v j * homogeneousCompletion2OriginalPoly j) = 0) :
    v (Fin.last 1) ∈ homogeneousCompletion2PreviousIdeal := by
  apply original_relation_last_mem_of_critical_pairs homogeneousGrevlexOrder
    homogeneousCompletion2OriginalPoly homogeneousCompletion2GPoly homogeneousCompletion2MPoly homogeneousCompletion2NPoly homogeneousCompletion2Family
    homogeneousCompletion2PreviousIdeal homogeneousCompletion2_basis_nonzero homogeneousCompletion2_relations ?_
    homogeneousCompletion2_reverse homogeneousCompletion2_residual homogeneousCompletion2_labels v hv
  intro i j hij
  obtain ⟨r, hr⟩ := homogeneousCompletion2_pair_coverage i j hij
  exact ⟨r, by simpa only [hr] using homogeneousCompletion2_tops r⟩

theorem homogeneousCompletion2_colon (x : MvPolynomial (Fin 6) ℂ)
    (hx : homogeneousCompletion2OriginalPoly (Fin.last 1) * x ∈ homogeneousCompletion2PreviousIdeal) :
    x ∈ homogeneousCompletion2PreviousIdeal := by
  apply colon_of_relation_last_mem (fun i : Fin 1 => homogeneousCompletion2OriginalPoly i.castSucc)
    (homogeneousCompletion2OriginalPoly (Fin.last 1)) ?_ x hx
  intro v hv
  apply homogeneousCompletion2_all_relation_last v
  change (∑ j, v j * (Fin.snoc (Fin.init homogeneousCompletion2OriginalPoly)
    (homogeneousCompletion2OriginalPoly (Fin.last 1)) : Fin 2 → MvPolynomial (Fin 6) ℂ) j) = 0 at hv
  rw [Fin.snoc_init_self] at hv
  exact hv

end
end Biunimodular.F11
