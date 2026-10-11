/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3BasisChecks
import Biunimodular.F11.HomogeneousCompletion3LeadingChecks
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

def homogeneousCompletion3OriginalPoly : Fin 3 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion3Original i)

def homogeneousCompletion3GPoly : Fin 7 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion3G i)

def homogeneousCompletion3MPoly : Matrix (Fin 3) (Fin 7) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion3M i j)

def homogeneousCompletion3NPoly : Matrix (Fin 7) (Fin 3) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion3N i j)

def homogeneousCompletion3PreviousIdeal : Ideal (MvPolynomial (Fin 6) ℂ) :=
  Ideal.span (Set.range (fun i : Fin 2 => homogeneousCompletion3OriginalPoly i.castSucc))

theorem homogeneousCompletion3_original_mem (i : Fin 2) :
    homogeneousCompletion3OriginalPoly i.castSucc ∈ homogeneousCompletion3PreviousIdeal :=
  Ideal.subset_span ⟨i, rfl⟩

theorem homogeneousCompletion3_basis_nonzero (k : Fin 7) : homogeneousCompletion3GPoly k ≠ 0 :=
  ((homogeneousCompletion3_leading_check k).sound.1).ne_zero

theorem homogeneousCompletion3_basis_degree (k : Fin 7) :
    homogeneousGrevlexOrder.degree (homogeneousCompletion3GPoly k) = homogeneousExponent (homogeneousCompletion3Leading k) :=
  (homogeneousCompletion3_leading_check k).sound.2

theorem homogeneousCompletion3_reverse (j : Fin 3) :
    (∑ k, homogeneousCompletion3NPoly k j * homogeneousCompletion3GPoly k) = homogeneousCompletion3OriginalPoly j := by
  exact rationalSparseZeroCheck.combination (fun k => homogeneousCompletion3N k j) homogeneousCompletion3G
    (homogeneousCompletion3Original j) (homogeneousCompletion3_reverse_check j)

theorem homogeneousCompletion3_residual (j : Fin 3) :
    (if j = Fin.last 2 then 1 else 0) -
      (∑ k, homogeneousCompletion3MPoly (Fin.last 2) k * homogeneousCompletion3NPoly k j) ∈ homogeneousCompletion3PreviousIdeal := by
  have heq := rationalSparseZeroCheck.residual j
    (homogeneousCompletion3M (Fin.last 2)) (fun k => homogeneousCompletion3N k j)
    (fun i => homogeneousCompletion3EW i j) (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc)
    (homogeneousCompletion3_residual_check j)
  change _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion3M (Fin.last 2) k) *
    rationalSparsePolynomial (homogeneousCompletion3N k j)) ∈ _
  rw [heq]
  exact homogeneousCompletion3PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion3PreviousIdeal.mul_mem_left _ (homogeneousCompletion3_original_mem i))

end
end Biunimodular.F11
