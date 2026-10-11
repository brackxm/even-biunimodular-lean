/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinatePhaseRootCount
import Biunimodular.F11.GaussianG10Irreducibility
import Biunimodular.F11.ASectorQ60Irreducibility
import Biunimodular.F11.BSectorQ80OriginalIrreducibility
import Biunimodular.F11.R102GlobalPositive
import Biunimodular.F11.H252DegreeEven

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial
noncomputable section

theorem coordinatePhaseFactorsQ11_eq_original :
    coordinatePhaseFactorQ11 .g5 = p150G10KQ11 ∧
      coordinatePhaseFactorQ11 .f30 = p150Q60KQ11 ∧
      coordinatePhaseFactorQ11 .f40 = p150Q80KQ11 := by
  have h := p150FactorPolynomialQ11_eq_map_integer
  simp only [coordinatePhaseFactorQ11, p150G10KQ11, p150Q60KQ11, p150Q80KQ11,
    Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  exact ⟨congrArg (fun p : ℚ[X] => p.comp (X ^ 2)) h.1,
    congrArg (fun p : ℚ[X] => p.comp (X ^ 2)) h.2.1,
    congrArg (fun p : ℚ[X] => p.comp (X ^ 2)) h.2.2⟩

theorem coordinatePhaseFactorsQ11_irreducible (f : KFactor) :
    Irreducible (coordinatePhaseFactorQ11 f) := by
  cases f
  · rw [coordinatePhaseFactorsQ11_eq_original.1]
    exact p150G10KQ11_irreducible
  · rw [coordinatePhaseFactorsQ11_eq_original.2.1]
    exact p150Q60KQ11_irreducible
  · rw [coordinatePhaseFactorsQ11_eq_original.2.2]
    exact p150Q80KQ11_irreducible

theorem h252KR11_isRoot_iff_real_factor (k : ℝ) :
    h252KR11.IsRoot k ↔ p150KR11.IsRoot k := by
  have hr : r102KR11.eval k ≠ 0 := ne_of_gt (r102KR11_pos k)
  simp only [Polynomial.IsRoot, h252KR11, h252KQ11, Polynomial.map_mul,
    Polynomial.eval_mul]
  change p150KR11.eval k * r102KR11.eval k = 0 ↔ p150KR11.eval k = 0
  simp only [mul_eq_zero, hr, or_false]

theorem coordinatePhaseFactors11_root_counts :
    Nat.card (CoordinatePhaseUnitRoot11 .g5) = 10 ∧
      Nat.card (CoordinatePhaseUnitRoot11 .f30) = 30 ∧
      Nat.card (CoordinatePhaseUnitRoot11 .f40) = 40 :=
  ⟨coordinatePhaseUnitRoot11_card .g5,
    coordinatePhaseUnitRoot11_card .f30, coordinatePhaseUnitRoot11_card .f40⟩

/-- In characteristic zero, the proved irreducibility also gives simple roots. -/
theorem coordinatePhaseFactorsR11_separable (f : KFactor) :
    (coordinatePhaseFactorR11 f).Separable :=
  (coordinatePhaseFactorsQ11_irreducible f).separable.map

theorem originalCoordinatePhaseFactors11_degrees :
    p150G10KQ11.natDegree = 10 ∧ p150Q60KQ11.natDegree = 60 ∧
      p150Q80KQ11.natDegree = 80 := by
  simp only [p150G10KQ11, p150Q60KQ11, p150Q80KQ11,
    Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective,
    Polynomial.natDegree_comp,
    Polynomial.natDegree_X_pow, p150G5Y11_nonzero_degree.2,
    p150F30Y11_nonzero_degree.2, p150F40Y11_nonzero_degree.2]
  norm_num

end
end Biunimodular.F11
