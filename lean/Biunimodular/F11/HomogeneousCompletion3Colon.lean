/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3BasisProofs
import Biunimodular.F11.HomogeneousCompletion3PairIndex
import Biunimodular.F11.CriticalRelationCertificate
import Biunimodular.F11.HomogeneousCompletion3Pairs01Proofs
import Biunimodular.F11.HomogeneousCompletion3Pairs02Proofs
import Biunimodular.F11.HomogeneousCompletion3Pairs03Proofs
import Biunimodular.F11.HomogeneousCompletion3Pairs04Proofs
import Biunimodular.F11.HomogeneousCompletion3Pairs05Proofs
import Biunimodular.F11.HomogeneousCompletion3Pairs06Proofs

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial

def homogeneousCompletion3Certificates : (r : Fin 21) → CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r) :=
  Fin.cons (α := fun r : Fin 21 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r))
    ⟨homogeneousCompletion3Pair1_2S, homogeneousCompletion3Pair1_2_relation, homogeneousCompletion3Pair1_2_last, homogeneousCompletion3Pair1_2_top⟩ (Fin.cons (α := fun r : Fin 20 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ))
    ⟨homogeneousCompletion3Pair1_3S, homogeneousCompletion3Pair1_3_relation, homogeneousCompletion3Pair1_3_last, homogeneousCompletion3Pair1_3_top⟩ (Fin.cons (α := fun r : Fin 19 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ))
    ⟨homogeneousCompletion3Pair1_4S, homogeneousCompletion3Pair1_4_relation, homogeneousCompletion3Pair1_4_last, homogeneousCompletion3Pair1_4_top⟩ (Fin.cons (α := fun r : Fin 18 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ))
    ⟨homogeneousCompletion3Pair1_5S, homogeneousCompletion3Pair1_5_relation, homogeneousCompletion3Pair1_5_last, homogeneousCompletion3Pair1_5_top⟩ (Fin.cons (α := fun r : Fin 17 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair1_6S, homogeneousCompletion3Pair1_6_relation, homogeneousCompletion3Pair1_6_last, homogeneousCompletion3Pair1_6_top⟩ (Fin.cons (α := fun r : Fin 16 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair1_7S, homogeneousCompletion3Pair1_7_relation, homogeneousCompletion3Pair1_7_last, homogeneousCompletion3Pair1_7_top⟩ (Fin.cons (α := fun r : Fin 15 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair2_3S, homogeneousCompletion3Pair2_3_relation, homogeneousCompletion3Pair2_3_last, homogeneousCompletion3Pair2_3_top⟩ (Fin.cons (α := fun r : Fin 14 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair2_4S, homogeneousCompletion3Pair2_4_relation, homogeneousCompletion3Pair2_4_last, homogeneousCompletion3Pair2_4_top⟩ (Fin.cons (α := fun r : Fin 13 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair2_5S, homogeneousCompletion3Pair2_5_relation, homogeneousCompletion3Pair2_5_last, homogeneousCompletion3Pair2_5_top⟩ (Fin.cons (α := fun r : Fin 12 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair2_6S, homogeneousCompletion3Pair2_6_relation, homogeneousCompletion3Pair2_6_last, homogeneousCompletion3Pair2_6_top⟩ (Fin.cons (α := fun r : Fin 11 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair2_7S, homogeneousCompletion3Pair2_7_relation, homogeneousCompletion3Pair2_7_last, homogeneousCompletion3Pair2_7_top⟩ (Fin.cons (α := fun r : Fin 10 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair3_4S, homogeneousCompletion3Pair3_4_relation, homogeneousCompletion3Pair3_4_last, homogeneousCompletion3Pair3_4_top⟩ (Fin.cons (α := fun r : Fin 9 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair3_5S, homogeneousCompletion3Pair3_5_relation, homogeneousCompletion3Pair3_5_last, homogeneousCompletion3Pair3_5_top⟩ (Fin.cons (α := fun r : Fin 8 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair3_6S, homogeneousCompletion3Pair3_6_relation, homogeneousCompletion3Pair3_6_last, homogeneousCompletion3Pair3_6_top⟩ (Fin.cons (α := fun r : Fin 7 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair3_7S, homogeneousCompletion3Pair3_7_relation, homogeneousCompletion3Pair3_7_last, homogeneousCompletion3Pair3_7_top⟩ (Fin.cons (α := fun r : Fin 6 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair4_5S, homogeneousCompletion3Pair4_5_relation, homogeneousCompletion3Pair4_5_last, homogeneousCompletion3Pair4_5_top⟩ (Fin.cons (α := fun r : Fin 5 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair4_6S, homogeneousCompletion3Pair4_6_relation, homogeneousCompletion3Pair4_6_last, homogeneousCompletion3Pair4_6_top⟩ (Fin.cons (α := fun r : Fin 4 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair4_7S, homogeneousCompletion3Pair4_7_relation, homogeneousCompletion3Pair4_7_last, homogeneousCompletion3Pair4_7_top⟩ (Fin.cons (α := fun r : Fin 3 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair5_6S, homogeneousCompletion3Pair5_6_relation, homogeneousCompletion3Pair5_6_last, homogeneousCompletion3Pair5_6_top⟩ (Fin.cons (α := fun r : Fin 2 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair5_7S, homogeneousCompletion3Pair5_7_relation, homogeneousCompletion3Pair5_7_last, homogeneousCompletion3Pair5_7_top⟩ (Fin.cons (α := fun r : Fin 1 => CriticalRelationCertificate homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3MPoly (Fin.last 2)) homogeneousCompletion3PreviousIdeal (homogeneousCompletion3Pairs r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
    ⟨homogeneousCompletion3Pair6_7S, homogeneousCompletion3Pair6_7_relation, homogeneousCompletion3Pair6_7_last, homogeneousCompletion3Pair6_7_top⟩ ((fun r : Fin 0 => Fin.elim0 r))))))))))))))))))))))

def homogeneousCompletion3Family : Fin 21 → Fin 7 → MvPolynomial (Fin 6) ℂ :=
  fun r => (homogeneousCompletion3Certificates r).v

theorem homogeneousCompletion3_relations (r : Fin 21) :
    (∑ k, homogeneousCompletion3Family r k * homogeneousCompletion3GPoly k) = 0 := by
  exact (homogeneousCompletion3Certificates r).relation

theorem homogeneousCompletion3_labels (r : Fin 21) :
    relationLabelMap (homogeneousCompletion3MPoly (Fin.last 2)) (homogeneousCompletion3Family r) ∈ homogeneousCompletion3PreviousIdeal := by
  exact (homogeneousCompletion3Certificates r).label

theorem homogeneousCompletion3_tops (r : Fin 21) :
    homogeneousCompletion3Family r (homogeneousCompletion3Pairs r).2 * homogeneousCompletion3GPoly (homogeneousCompletion3Pairs r).2 ≠ 0 ∧
      homogeneousGrevlexOrder.degree (homogeneousCompletion3Family r (homogeneousCompletion3Pairs r).2 * homogeneousCompletion3GPoly (homogeneousCompletion3Pairs r).2) =
        homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly (homogeneousCompletion3Pairs r).1) ⊔
          homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly (homogeneousCompletion3Pairs r).2) ∧
      ∀ k, schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3Family r) k ≤
        schreyerKey homogeneousGrevlexOrder homogeneousCompletion3GPoly (homogeneousCompletion3Family r) (homogeneousCompletion3Pairs r).2 := by
  exact (homogeneousCompletion3Certificates r).top

theorem homogeneousCompletion3_all_relation_last
    (v : Fin 3 → MvPolynomial (Fin 6) ℂ)
    (hv : (∑ j, v j * homogeneousCompletion3OriginalPoly j) = 0) :
    v (Fin.last 2) ∈ homogeneousCompletion3PreviousIdeal := by
  apply original_relation_last_mem_of_critical_pairs homogeneousGrevlexOrder
    homogeneousCompletion3OriginalPoly homogeneousCompletion3GPoly homogeneousCompletion3MPoly homogeneousCompletion3NPoly homogeneousCompletion3Family
    homogeneousCompletion3PreviousIdeal homogeneousCompletion3_basis_nonzero homogeneousCompletion3_relations ?_
    homogeneousCompletion3_reverse homogeneousCompletion3_residual homogeneousCompletion3_labels v hv
  intro i j hij
  obtain ⟨r, hr⟩ := homogeneousCompletion3_pair_coverage i j hij
  exact ⟨r, by simpa only [hr] using homogeneousCompletion3_tops r⟩

theorem homogeneousCompletion3_colon (x : MvPolynomial (Fin 6) ℂ)
    (hx : homogeneousCompletion3OriginalPoly (Fin.last 2) * x ∈ homogeneousCompletion3PreviousIdeal) :
    x ∈ homogeneousCompletion3PreviousIdeal := by
  apply colon_of_relation_last_mem (fun i : Fin 2 => homogeneousCompletion3OriginalPoly i.castSucc)
    (homogeneousCompletion3OriginalPoly (Fin.last 2)) ?_ x hx
  intro v hv
  apply homogeneousCompletion3_all_relation_last v
  change (∑ j, v j * (Fin.snoc (Fin.init homogeneousCompletion3OriginalPoly)
    (homogeneousCompletion3OriginalPoly (Fin.last 2)) : Fin 3 → MvPolynomial (Fin 6) ℂ) j) = 0 at hv
  rw [Fin.snoc_init_self] at hv
  exact hv

end
end Biunimodular.F11
