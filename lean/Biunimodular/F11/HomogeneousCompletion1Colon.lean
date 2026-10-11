/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion1BasisProofs
import Biunimodular.F11.HomogeneousCompletion1PairIndex
import Biunimodular.F11.CriticalRelationCertificate

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial

def homogeneousCompletion1Certificates : (r : Fin 0) → CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion1GPoly (homogeneousCompletion1MPoly (Fin.last 0)) homogeneousCompletion1PreviousIdeal (homogeneousCompletion1Pairs r) :=
  (fun r : Fin 0 => Fin.elim0 r)

def homogeneousCompletion1Family : Fin 0 → Fin 1 → MvPolynomial (Fin 6) ℂ :=
  fun r => (homogeneousCompletion1Certificates r).v

theorem homogeneousCompletion1_relations (r : Fin 0) :
    (∑ k, homogeneousCompletion1Family r k * homogeneousCompletion1GPoly k) = 0 := by
  exact (homogeneousCompletion1Certificates r).relation

theorem homogeneousCompletion1_labels (r : Fin 0) :
    relationLabelMap (homogeneousCompletion1MPoly (Fin.last 0)) (homogeneousCompletion1Family r) ∈ homogeneousCompletion1PreviousIdeal := by
  exact (homogeneousCompletion1Certificates r).label

theorem homogeneousCompletion1_tops (r : Fin 0) :
    homogeneousCompletion1Family r (homogeneousCompletion1Pairs r).2 * homogeneousCompletion1GPoly (homogeneousCompletion1Pairs r).2 ≠ 0 ∧
      homogeneousGrevlexOrder.degree (homogeneousCompletion1Family r (homogeneousCompletion1Pairs r).2 * homogeneousCompletion1GPoly (homogeneousCompletion1Pairs r).2) =
        homogeneousGrevlexOrder.degree (homogeneousCompletion1GPoly (homogeneousCompletion1Pairs r).1) ⊔
          homogeneousGrevlexOrder.degree (homogeneousCompletion1GPoly (homogeneousCompletion1Pairs r).2) ∧
      ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion1GPoly (homogeneousCompletion1Family r) k ≤
        schreyerKey homogeneousGrevlexOrder homogeneousCompletion1GPoly (homogeneousCompletion1Family r) (homogeneousCompletion1Pairs r).2 := by
  exact (homogeneousCompletion1Certificates r).top

theorem homogeneousCompletion1_all_relation_last
    (v : Fin 1 → MvPolynomial (Fin 6) ℂ)
    (hv : (∑ j, v j * homogeneousCompletion1OriginalPoly j) = 0) :
    v (Fin.last 0) ∈ homogeneousCompletion1PreviousIdeal := by
  apply original_relation_last_mem_of_critical_pairs homogeneousGrevlexOrder
    homogeneousCompletion1OriginalPoly homogeneousCompletion1GPoly homogeneousCompletion1MPoly homogeneousCompletion1NPoly homogeneousCompletion1Family
    homogeneousCompletion1PreviousIdeal homogeneousCompletion1_basis_nonzero homogeneousCompletion1_relations ?_
    homogeneousCompletion1_reverse homogeneousCompletion1_residual homogeneousCompletion1_labels v hv
  intro i j hij
  obtain ⟨r, hr⟩ := homogeneousCompletion1_pair_coverage i j hij
  exact ⟨r, by simpa only [hr] using homogeneousCompletion1_tops r⟩

theorem homogeneousCompletion1_colon (x : MvPolynomial (Fin 6) ℂ)
    (hx : homogeneousCompletion1OriginalPoly (Fin.last 0) * x ∈ homogeneousCompletion1PreviousIdeal) :
    x ∈ homogeneousCompletion1PreviousIdeal := by
  apply colon_of_relation_last_mem (fun i : Fin 0 => homogeneousCompletion1OriginalPoly i.castSucc)
    (homogeneousCompletion1OriginalPoly (Fin.last 0)) ?_ x hx
  intro v hv
  apply homogeneousCompletion1_all_relation_last v
  change (∑ j, v j * (Fin.snoc (Fin.init homogeneousCompletion1OriginalPoly)
    (homogeneousCompletion1OriginalPoly (Fin.last 0)) : Fin 1 → MvPolynomial (Fin 6) ℂ) j) = 0 at hv
  rw [Fin.snoc_init_self] at hv
  exact hv

end
end Biunimodular.F11
