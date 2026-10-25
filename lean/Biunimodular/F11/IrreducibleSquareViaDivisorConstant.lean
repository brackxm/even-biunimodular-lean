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
  let : Fact (Irreducible p) := ⟨hi⟩
  apply Polynomial.irreducible_comp hi
  let pb := AdjoinRoot.powerBasis hm.ne_zero
  let := pb.finite
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · intro t ht
    have hs : t ^ 2 = AdjoinRoot.root p := by
      apply sub_eq_zero.mp
      simpa only [Polynomial.map_pow, Polynomial.map_X, Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] using ht
    have htint : IsIntegral ℚ t := Algebra.IsIntegral.isIntegral t
    have hgen : Algebra.adjoin ℚ ({t} : Set (AdjoinRoot p)) = ⊤ := by
      apply pb.adjoin_eq_top_of_gen_mem_adjoin
      change AdjoinRoot.root p ∈ Algebra.adjoin ℚ ({t} : Set (AdjoinRoot p))
      rw [← hs]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton t)) 2
    let tb := PowerBasis.ofAdjoinEqTop htint hgen
    have hd : (minpoly ℚ t).natDegree = p.natDegree := by
      calc
        _ = tb.dim := rfl
        _ = Module.finrank ℚ (AdjoinRoot p) := tb.finrank.symm
        _ = pb.dim := pb.finrank
        _ = p.natDegree := rfl
    have hdiv : minpoly ℚ t ∣ p.comp (X ^ 2) := by
      apply minpoly.dvd ℚ t
      rw [Polynomial.aeval_comp]
      simp only [map_pow, Polynomial.aeval_X, hs]
      simp only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hnorm : Algebra.norm ℚ (AdjoinRoot.root p) =
        (-1 : ℚ) ^ p.natDegree * p.coeff 0 := by
      have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
      rw [show minpoly ℚ pb.gen = p from AdjoinRoot.minpoly_powerBasis_gen_of_monic hm] at h
      simpa only [pb, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] using h
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
