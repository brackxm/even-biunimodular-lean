/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.NormNum.IsSquare

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial IntermediateField

/-- An irreducible rational squared-coordinate polynomial remains irreducible
on substituting X² if the norm of its root is not a rational square. -/
theorem irreducible_comp_square_of_norm_not_square (p : ℚ[X])
    (hm : p.Monic) (hi : Irreducible p)
    (hn : ¬ IsSquare ((-1 : ℚ) ^ p.natDegree * p.coeff 0)) :
    Irreducible (p.comp (X ^ 2)) := by
  apply Polynomial.irreducible_comp hm (monic_X_pow 2) hi
  intro E _ _ x hx
  have hxint : IsIntegral ℚ x := minpoly.ne_zero_iff.mp (hx ▸ hm.ne_zero)
  let pb := adjoin.powerBasis hxint
  have hnorm : Algebra.norm ℚ (AdjoinSimple.gen ℚ x) =
      (-1 : ℚ) ^ p.natDegree * p.coeff 0 := by
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    simpa only [pb, adjoin.powerBasis_gen, adjoin.powerBasis_dim, minpoly_gen, hx] using h
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · intro t ht
    have hs : t ^ 2 = AdjoinSimple.gen ℚ x := by
      simpa using (sub_eq_zero.mp (show t ^ 2 - AdjoinSimple.gen ℚ x = 0 by
        simpa only [Polynomial.map_pow, Polynomial.map_X, Polynomial.IsRoot,
          Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C] using ht))
    apply hn
    refine ⟨Algebra.norm ℚ t, ?_⟩
    rw [← pow_two, ← map_pow, hs, hnorm]

end Biunimodular.F11
