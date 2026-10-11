/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion2BasisChecks
import Biunimodular.F11.HomogeneousCompletion2LeadingChecks
import Biunimodular.F11.HomogeneousCompletionCriterion
import Biunimodular.F11.RationalSparseMatrixIdentity
import Biunimodular.F11.HomogeneousExponentArithmetic

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

noncomputable section
open MvPolynomial
open scoped MonomialOrder

def homogeneousCompletion2OriginalPoly : Fin 2 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion2Original i)

def homogeneousCompletion2GPoly : Fin 3 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion2G i)

def homogeneousCompletion2MPoly : Matrix (Fin 2) (Fin 3) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion2M i j)

def homogeneousCompletion2NPoly : Matrix (Fin 3) (Fin 2) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion2N i j)

def homogeneousCompletion2PreviousIdeal : Ideal (MvPolynomial (Fin 6) ℂ) :=
  Ideal.span (Set.range (fun i : Fin 1 => homogeneousCompletion2OriginalPoly i.castSucc))

theorem homogeneousCompletion2_original_mem (i : Fin 1) :
    homogeneousCompletion2OriginalPoly i.castSucc ∈ homogeneousCompletion2PreviousIdeal :=
  Ideal.subset_span ⟨i, rfl⟩

theorem homogeneousCompletion2_basis_nonzero (k : Fin 3) : homogeneousCompletion2GPoly k ≠ 0 :=
  ((homogeneousCompletion2_leading_check k).sound.1).ne_zero

theorem homogeneousCompletion2_basis_degree (k : Fin 3) :
    homogeneousGrevlexOrder.degree (homogeneousCompletion2GPoly k) = homogeneousExponent (homogeneousCompletion2Leading k) :=
  (homogeneousCompletion2_leading_check k).sound.2

theorem homogeneousCompletion2_reverse (j : Fin 2) :
    (∑ k, homogeneousCompletion2NPoly k j * homogeneousCompletion2GPoly k) = homogeneousCompletion2OriginalPoly j := by
  exact rationalSparseZeroCheck.combination (fun k => homogeneousCompletion2N k j) homogeneousCompletion2G
    (homogeneousCompletion2Original j) (homogeneousCompletion2_reverse_check j)

theorem homogeneousCompletion2_residual (j : Fin 2) :
    (if j = Fin.last 1 then 1 else 0) -
      (∑ k, homogeneousCompletion2MPoly (Fin.last 1) k * homogeneousCompletion2NPoly k j) ∈ homogeneousCompletion2PreviousIdeal := by
  have heq := rationalSparseZeroCheck.residual j
    (homogeneousCompletion2M (Fin.last 1)) (fun k => homogeneousCompletion2N k j)
    (fun i => homogeneousCompletion2EW i j) (fun i : Fin 1 => homogeneousCompletion2Original i.castSucc)
    (homogeneousCompletion2_residual_check j)
  change _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion2M (Fin.last 1) k) *
    rationalSparsePolynomial (homogeneousCompletion2N k j)) ∈ _
  rw [heq]
  exact homogeneousCompletion2PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion2PreviousIdeal.mul_mem_left _ (homogeneousCompletion2_original_mem i))

end
end Biunimodular.F11
