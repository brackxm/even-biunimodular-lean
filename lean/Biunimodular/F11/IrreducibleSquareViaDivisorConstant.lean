/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IrreducibleSquaredCoordinate
import Mathlib.RingTheory.Adjoin.PowerBasis

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial IntermediateField

/-- A square root of a generator gives a divisor of the doubled polynomial
whose degree is the original degree and whose constant has the required norm. -/
theorem irreducible_comp_square_of_divisor_constant (p : ℚ[X])
    (hm : p.Monic) (hi : Irreducible p)
    (hbad : ∀ q : ℚ[X], q.Monic → q.natDegree = p.natDegree →
      q ∣ p.comp (X ^ 2) → q.coeff 0 ^ 2 ≠ (-1 : ℚ) ^ p.natDegree * p.coeff 0) :
    Irreducible (p.comp (X ^ 2)) := by
  apply Polynomial.irreducible_comp hm (monic_X_pow 2) hi
  intro E _ _ x hx
  have hxint : IsIntegral ℚ x := minpoly.ne_zero_iff.mp (hx ▸ hm.ne_zero)
  let pb := adjoin.powerBasis hxint
  let := pb.finite
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · intro t ht
    have hs : t ^ 2 = AdjoinSimple.gen ℚ x := by
      apply sub_eq_zero.mp
      simpa only [Polynomial.map_pow, Polynomial.map_X, Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] using ht
    have htint : IsIntegral ℚ t := Algebra.IsIntegral.isIntegral t
    have hgen : Algebra.adjoin ℚ ({t} : Set ℚ⟮x⟯) = ⊤ := by
      apply pb.adjoin_eq_top_of_gen_mem_adjoin
      change AdjoinSimple.gen ℚ x ∈ Algebra.adjoin ℚ ({t} : Set ℚ⟮x⟯)
      rw [← hs]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton t)) 2
    let tb := PowerBasis.ofAdjoinEqTop htint hgen
    have hd : (minpoly ℚ t).natDegree = p.natDegree := by
      calc
        _ = tb.dim := rfl
        _ = Module.finrank ℚ ℚ⟮x⟯ := tb.finrank.symm
        _ = pb.dim := pb.finrank
        _ = p.natDegree := by simp only [pb, adjoin.powerBasis_dim, hx]
    have hdiv : minpoly ℚ t ∣ p.comp (X ^ 2) := by
      apply minpoly.dvd ℚ t
      rw [Polynomial.aeval_comp]
      simp only [map_pow, Polynomial.aeval_X, hs]
      rw [← hx]
      exact aeval_gen_minpoly ℚ x
    have hnorm : Algebra.norm ℚ (AdjoinSimple.gen ℚ x) =
        (-1 : ℚ) ^ p.natDegree * p.coeff 0 := by
      simpa only [pb, adjoin.powerBasis_gen, adjoin.powerBasis_dim, minpoly_gen, hx]
        using Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    have htnorm : Algebra.norm ℚ t = (-1 : ℚ) ^ p.natDegree * (minpoly ℚ t).coeff 0 := by
      simpa only [tb, PowerBasis.ofAdjoinEqTop_gen, PowerBasis.ofAdjoinEqTop_dim, hd]
        using Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly tb
    apply hbad (minpoly ℚ t) (minpoly.monic htint) hd hdiv
    have h := congrArg (Algebra.norm ℚ) hs
    rw [map_pow, hnorm, htnorm, mul_pow, ← pow_mul] at h
    have hsign : (-1 : ℚ) ^ (p.natDegree * 2) = 1 := by
      rw [Nat.mul_comm, pow_mul]
      norm_num
    simpa only [hsign, one_mul] using h

end Biunimodular.F11
