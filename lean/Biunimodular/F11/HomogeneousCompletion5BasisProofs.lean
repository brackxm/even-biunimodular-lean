/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisChecks
import Biunimodular.F11.HomogeneousCompletion5LeadingChecks
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

def homogeneousCompletion5OriginalPoly : Fin 5 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion5Original i)

def homogeneousCompletion5GPoly : Fin 27 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion5G i)

def homogeneousCompletion5MPoly : Matrix (Fin 5) (Fin 27) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion5M i j)

def homogeneousCompletion5NPoly : Matrix (Fin 27) (Fin 5) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion5N i j)

def homogeneousCompletion5PreviousIdeal : Ideal (MvPolynomial (Fin 6) ℂ) :=
  Ideal.span (Set.range (fun i : Fin 4 => homogeneousCompletion5OriginalPoly i.castSucc))

theorem homogeneousCompletion5_original_mem (i : Fin 4) :
    homogeneousCompletion5OriginalPoly i.castSucc ∈ homogeneousCompletion5PreviousIdeal :=
  Ideal.subset_span ⟨i, rfl⟩

theorem homogeneousCompletion5_basis_nonzero (k : Fin 27) : homogeneousCompletion5GPoly k ≠ 0 :=
  ((homogeneousCompletion5_leading_check k).sound.1).ne_zero

theorem homogeneousCompletion5_basis_degree (k : Fin 27) :
    homogeneousGrevlexOrder.degree (homogeneousCompletion5GPoly k) = homogeneousExponent (homogeneousCompletion5Leading k) :=
  (homogeneousCompletion5_leading_check k).sound.2

theorem homogeneousCompletion5_reverse (j : Fin 5) :
    (∑ k, homogeneousCompletion5NPoly k j * homogeneousCompletion5GPoly k) = homogeneousCompletion5OriginalPoly j := by
  exact rationalSparseZeroCheck.combination (fun k => homogeneousCompletion5N k j) homogeneousCompletion5G
    (homogeneousCompletion5Original j) (homogeneousCompletion5_reverse_check j)

theorem homogeneousCompletion5_residual (j : Fin 5) :
    (if j = Fin.last 4 then 1 else 0) -
      (∑ k, homogeneousCompletion5MPoly (Fin.last 4) k * homogeneousCompletion5NPoly k j) ∈ homogeneousCompletion5PreviousIdeal := by
  have heq := rationalSparseZeroCheck.residual j
    (homogeneousCompletion5M (Fin.last 4)) (fun k => homogeneousCompletion5N k j)
    (fun i => homogeneousCompletion5EW i j) (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc)
    (homogeneousCompletion5_residual_check j)
  change _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion5M (Fin.last 4) k) *
    rationalSparsePolynomial (homogeneousCompletion5N k j)) ∈ _
  rw [heq]
  exact homogeneousCompletion5PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion5PreviousIdeal.mul_mem_left _ (homogeneousCompletion5_original_mem i))

end
end Biunimodular.F11
