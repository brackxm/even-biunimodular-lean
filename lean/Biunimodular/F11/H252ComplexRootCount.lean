/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252DegreeEven
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial
noncomputable section

theorem h252KComplex_degree : h252KComplex.natDegree = 252 := by
  rw [h252KComplex, Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    h252K11_degree]

theorem h252KComplex_rootSet_card : Nat.card (h252KComplex.rootSet ℂ) = 252 := by
  classical
  rw [Nat.card_eq_fintype_card, Polynomial.card_rootSet_eq_natDegree h252KComplex_separable
    (IsAlgClosed.splits (h252KComplex.map (algebraMap ℂ ℂ))), h252KComplex_degree]

theorem h252KComplex_rootMultiplicity_le_one (k : ℂ) :
    h252KComplex.rootMultiplicity k ≤ 1 :=
  Polynomial.rootMultiplicity_le_one_of_separable h252KComplex_separable k

theorem r102KComplex_even (k : ℂ) :
    (r102K11.map (Int.castRingHom ℂ)).eval (-k) =
      (r102K11.map (Int.castRingHom ℂ)).eval k := by
  simp [r102K11, Polynomial.map_comp, Polynomial.eval_comp]

end
end Biunimodular.F11
