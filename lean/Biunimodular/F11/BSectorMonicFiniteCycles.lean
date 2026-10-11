/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorMonicFactorization
import Biunimodular.F11.FiniteFieldPrimeCycle

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

private instance : Fact (Nat.Prime 37) := ⟨by decide⟩
private instance : Fact (Nat.Prime 211) := ⟨by decide⟩

private theorem b37MonicSeven_degree : B37monicSeven.natDegree = 7 := by
  norm_num [B37monicSeven]
  compute_degree <;> norm_num

private theorem b211MonicFive_degree : B211monicFive.natDegree = 5 := by
  norm_num [B211monicFive]
  compute_degree <;> norm_num

/-- The monic reduction modulo 37 has one Frobenius seven-cycle and one
fixed root in every splitting field. -/
theorem bMonic_mod37_frob_cycle (K : Type*) [Field K] [Algebra (ZMod 37) K]
    [Fact ((((X + C 36) * B37monicSeven : (ZMod 37)[X]).map
      (algebraMap (ZMod 37) K)).Splits)]
    [DecidableEq (((X + C 36) * B37monicSeven : (ZMod 37)[X]).rootSet K)] :
    (finiteFieldFrobPermIn ((X + C 36) * B37monicSeven) K).IsCycle ∧
    (finiteFieldFrobPermIn ((X + C 36) * B37monicSeven) K).support.card = 7 := by
  classical
  let l : (ZMod 37)[X] := X + C 36
  have hl : l.Splits := Splits.X_add_C (36 : ZMod 37)
  have hlne : l ≠ 0 := Polynomial.X_add_C_ne_zero _
  have hdeg : (l * B37monicSeven).natDegree = 8 := by
    norm_num [l, B37monicSeven]
    compute_degree <;> norm_num
  have hcard : Fintype.card ((l * B37monicSeven).rootSet K) < 2 * 7 := by
    have hle : Fintype.card ((l * B37monicSeven).rootSet K) ≤ 8 := by
      rw [Set.fintypeCard_eq_ncard]
      exact (Polynomial.ncard_rootSet_le (l * B37monicSeven) K).trans_eq hdeg
    omega
  exact finiteFieldFrobPermIn_split_mul_irreducible l B37monicSeven
    hl hlne B37monicSeven_irreducible 7 (by decide)
    b37MonicSeven_degree hcard

/-- The monic reduction modulo 211 has one Frobenius five-cycle and three
fixed roots in every splitting field. -/
theorem bMonic_mod211_frob_cycle (K : Type*) [Field K] [Algebra (ZMod 211) K]
    [Fact (((((X + C 7) * (X + C 141) * (X + C 67)) * B211monicFive :
      (ZMod 211)[X]).map (algebraMap (ZMod 211) K)).Splits)]
    [DecidableEq (((X + C 7) * (X + C 141) * (X + C 67) * B211monicFive :
      (ZMod 211)[X]).rootSet K)] :
    (finiteFieldFrobPermIn
      ((X + C 7) * (X + C 141) * (X + C 67) * B211monicFive) K).IsCycle ∧
    (finiteFieldFrobPermIn
      ((X + C 7) * (X + C 141) * (X + C 67) * B211monicFive) K).support.card = 5 := by
  classical
  let l : (ZMod 211)[X] := (X + C 7) * (X + C 141) * (X + C 67)
  have hl : l.Splits := by
    dsimp only [l]
    exact ((Splits.X_add_C (7 : ZMod 211)).mul
      (Splits.X_add_C (141 : ZMod 211))).mul (Splits.X_add_C (67 : ZMod 211))
  have hlne : l ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (Polynomial.X_add_C_ne_zero _) (Polynomial.X_add_C_ne_zero _))
      (Polynomial.X_add_C_ne_zero _)
  have hdeg : (l * B211monicFive).natDegree = 8 := by
    norm_num [l, B211monicFive]
    compute_degree <;> norm_num
  have hcard : Fintype.card ((l * B211monicFive).rootSet K) < 2 * 5 := by
    have hle : Fintype.card ((l * B211monicFive).rootSet K) ≤ 8 := by
      rw [Set.fintypeCard_eq_ncard]
      exact (Polynomial.ncard_rootSet_le (l * B211monicFive) K).trans_eq hdeg
    omega
  exact finiteFieldFrobPermIn_split_mul_irreducible l B211monicFive
    hl hlne B211monicFive_irreducible 5 (by decide)
    b211MonicFive_degree hcard

end

end Biunimodular.F11
