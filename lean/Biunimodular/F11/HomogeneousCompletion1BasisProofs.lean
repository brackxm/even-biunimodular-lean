/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion1BasisChecks
import Biunimodular.F11.HomogeneousCompletion1LeadingChecks
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

def homogeneousCompletion1OriginalPoly : Fin 1 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion1Original i)

def homogeneousCompletion1GPoly : Fin 1 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion1G i)

def homogeneousCompletion1MPoly : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion1M i j)

def homogeneousCompletion1NPoly : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion1N i j)

def homogeneousCompletion1PreviousIdeal : Ideal (MvPolynomial (Fin 6) ℂ) :=
  Ideal.span (Set.range (fun i : Fin 0 => homogeneousCompletion1OriginalPoly i.castSucc))

theorem homogeneousCompletion1_original_mem (i : Fin 0) :
    homogeneousCompletion1OriginalPoly i.castSucc ∈ homogeneousCompletion1PreviousIdeal :=
  Ideal.subset_span ⟨i, rfl⟩

theorem homogeneousCompletion1_basis_nonzero (k : Fin 1) : homogeneousCompletion1GPoly k ≠ 0 :=
  ((homogeneousCompletion1_leading_check k).sound.1).ne_zero

theorem homogeneousCompletion1_basis_degree (k : Fin 1) :
    homogeneousGrevlexOrder.degree (homogeneousCompletion1GPoly k) = homogeneousExponent (homogeneousCompletion1Leading k) :=
  (homogeneousCompletion1_leading_check k).sound.2

theorem homogeneousCompletion1_reverse (j : Fin 1) :
    (∑ k, homogeneousCompletion1NPoly k j * homogeneousCompletion1GPoly k) = homogeneousCompletion1OriginalPoly j := by
  exact rationalSparseZeroCheck.combination (fun k => homogeneousCompletion1N k j) homogeneousCompletion1G
    (homogeneousCompletion1Original j) (homogeneousCompletion1_reverse_check j)

theorem homogeneousCompletion1_residual (j : Fin 1) :
    (if j = Fin.last 0 then 1 else 0) -
      (∑ k, homogeneousCompletion1MPoly (Fin.last 0) k * homogeneousCompletion1NPoly k j) ∈ homogeneousCompletion1PreviousIdeal := by
  have heq := rationalSparseZeroCheck.residual j
    (homogeneousCompletion1M (Fin.last 0)) (fun k => homogeneousCompletion1N k j)
    (fun i => homogeneousCompletion1EW i j) (fun i : Fin 0 => homogeneousCompletion1Original i.castSucc)
    (homogeneousCompletion1_residual_check j)
  change _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion1M (Fin.last 0) k) *
    rationalSparsePolynomial (homogeneousCompletion1N k j)) ∈ _
  rw [heq]
  exact homogeneousCompletion1PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion1PreviousIdeal.mul_mem_left _ (homogeneousCompletion1_original_mem i))

end
end Biunimodular.F11
