/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisChecks
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks
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

def homogeneousCompletion4OriginalPoly : Fin 4 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion4Original i)

def homogeneousCompletion4GPoly : Fin 15 → MvPolynomial (Fin 6) ℂ :=
  fun i => rationalSparsePolynomial (homogeneousCompletion4G i)

def homogeneousCompletion4MPoly : Matrix (Fin 4) (Fin 15) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion4M i j)

def homogeneousCompletion4NPoly : Matrix (Fin 15) (Fin 4) (MvPolynomial (Fin 6) ℂ) :=
  fun i j => rationalSparsePolynomial (homogeneousCompletion4N i j)

def homogeneousCompletion4PreviousIdeal : Ideal (MvPolynomial (Fin 6) ℂ) :=
  Ideal.span (Set.range (fun i : Fin 3 => homogeneousCompletion4OriginalPoly i.castSucc))

theorem homogeneousCompletion4_original_mem (i : Fin 3) :
    homogeneousCompletion4OriginalPoly i.castSucc ∈ homogeneousCompletion4PreviousIdeal :=
  Ideal.subset_span ⟨i, rfl⟩

theorem homogeneousCompletion4_basis_nonzero (k : Fin 15) : homogeneousCompletion4GPoly k ≠ 0 :=
  ((homogeneousCompletion4_leading_check k).sound.1).ne_zero

theorem homogeneousCompletion4_basis_degree (k : Fin 15) :
    homogeneousGrevlexOrder.degree (homogeneousCompletion4GPoly k) = homogeneousExponent (homogeneousCompletion4Leading k) :=
  (homogeneousCompletion4_leading_check k).sound.2

theorem homogeneousCompletion4_reverse (j : Fin 4) :
    (∑ k, homogeneousCompletion4NPoly k j * homogeneousCompletion4GPoly k) = homogeneousCompletion4OriginalPoly j := by
  exact rationalSparseZeroCheck.combination (fun k => homogeneousCompletion4N k j) homogeneousCompletion4G
    (homogeneousCompletion4Original j) (homogeneousCompletion4_reverse_check j)

theorem homogeneousCompletion4_residual (j : Fin 4) :
    (if j = Fin.last 3 then 1 else 0) -
      (∑ k, homogeneousCompletion4MPoly (Fin.last 3) k * homogeneousCompletion4NPoly k j) ∈ homogeneousCompletion4PreviousIdeal := by
  have heq := rationalSparseZeroCheck.residual j
    (homogeneousCompletion4M (Fin.last 3)) (fun k => homogeneousCompletion4N k j)
    (fun i => homogeneousCompletion4EW i j) (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc)
    (homogeneousCompletion4_residual_check j)
  change _ - (∑ k, rationalSparsePolynomial (homogeneousCompletion4M (Fin.last 3) k) *
    rationalSparsePolynomial (homogeneousCompletion4N k j)) ∈ _
  rw [heq]
  exact homogeneousCompletion4PreviousIdeal.sum_mem (fun i _ =>
    homogeneousCompletion4PreviousIdeal.mul_mem_left _ (homogeneousCompletion4_original_mem i))

end
end Biunimodular.F11
