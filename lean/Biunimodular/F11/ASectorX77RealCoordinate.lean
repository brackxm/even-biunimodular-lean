/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorX77PolynomialRelation
import Biunimodular.F11.ASectorF30CharacteristicZero
import Biunimodular.F11.ASectorRealTower
import Biunimodular.F11.ASectorCyclotomicLiftData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial
open scoped IntermediateField

noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

/-- The symmetric conductor-77 expression for the A phase coordinate. -/
def aSectorX77Pair {R : Type*} [CommRing R] (z : R) : R :=
  -627 + ∑ n ∈ Finset.range 29,
    (aSectorCyclotomicCoeffs[n]! : R) *
      (z ^ ((3 * (n + 1)) % 77) + z ^ (77 - ((3 * (n + 1)) % 77)))

private theorem aSectorX77Pair_polynomial :
    aSectorX77Pair (X : ℤ[X]) = aSectorXPoly77 := by
  simp [aSectorX77Pair, aSectorCyclotomicCoeffs, Finset.sum_range_succ,
    aSectorXPoly77]
  ring

theorem aSectorX77Pair_eq_eval {R : Type*} [CommRing R] (z : R) :
    aSectorX77Pair z = eval₂ (Int.castRingHom R) z aSectorXPoly77 := by
  have hcast (c : ℤ) :
      eval₂ (Int.castRingHom R) z (c : ℤ[X]) = (c : R) := by
    rw [eval₂_eq_eval_map]
    simp
  rw [← aSectorX77Pair_polynomial]
  simp [aSectorX77Pair, eval₂_finsetSum, eval₂_add, eval₂_mul, eval₂_pow, hcast]

/-- The symmetric coordinate expression is real at every conductor-77 root
of unity, including the specified analytic root. -/
theorem aSectorX77Pair_real (μ : ℂ) (hμ : μ ^ 77 = 1) :
    star (aSectorX77Pair μ) = aSectorX77Pair μ := by
  unfold aSectorX77Pair
  rw [star_add, star_sum]
  have hconst : star (-627 : ℂ) = -627 := by simp
  rw [hconst]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hk : (3 * (n + 1)) % 77 ≤ 77 := Nat.le_of_lt (Nat.mod_lt _ (by norm_num))
  have hkc : 77 - ((3 * (n + 1)) % 77) ≤ 77 := Nat.sub_le _ _
  rw [star_mul, star_intCast, star_add,
    star_pow_complement77 μ hμ _ hk,
    star_pow_complement77 μ hμ _ hkc]
  simp only [Nat.sub_sub_self hk]
  ring

/-- The explicit coordinate in the full conductor-77 cyclotomic field. -/
def aSectorX77 : Conductor77Cyclotomic := aSectorX77Pair zeta77

theorem aSectorX77_isRoot_G30 :
    eval₂ (Int.castRingHom Conductor77Cyclotomic) aSectorX77 aSectorG30 = 0 := by
  rw [aSectorX77, aSectorX77Pair_eq_eval]
  exact aSectorX77_G30_relation zeta77 zeta77_cyclotomic_root

theorem aSectorX77_mem_maximalReal :
    aSectorX77 ∈ NumberField.maximalRealSubfield Conductor77Cyclotomic := by
  rw [NumberField.mem_maximalRealSubfield_iff]
  intro φ
  let μ : ℂ := φ zeta77
  have hζ : zeta77 ^ 77 = 1 := by
    exact (IsCyclotomicExtension.zeta_spec 77 ℚ
      Conductor77Cyclotomic).pow_eq_one
  have hμ : μ ^ 77 = 1 := by
    simpa only [μ, map_pow, map_one] using congrArg φ hζ
  have hvalue : φ aSectorX77 = aSectorX77Pair μ := by
    simp [aSectorX77, aSectorX77Pair, μ, map_sum, map_add,
      map_mul, map_pow, map_intCast, map_ofNat]
  rw [hvalue]
  exact aSectorX77Pair_real μ hμ

/-- The actual degree-thirty coordinate as an element of the real field. -/
def aSectorX77Real : Conductor77MaxReal :=
  ⟨aSectorX77, aSectorX77_mem_maximalReal⟩

theorem aSectorX77Real_isRoot_G30 :
    eval₂ (Int.castRingHom Conductor77MaxReal) aSectorX77Real aSectorG30 = 0 := by
  apply Subtype.ext
  have h := aSectorX77_isRoot_G30
  simp [aSectorG30, aSectorX77Real] at h ⊢
  exact h

/-- The monic polynomial G30 is the minimal polynomial of the explicit
real conductor-77 coordinate. -/
theorem aSectorX77Real_minpoly :
    aSectorG30.map (Int.castRingHom ℚ) = minpoly ℚ aSectorX77Real := by
  have hroot : (aeval aSectorX77Real)
      (aSectorG30.map (Int.castRingHom ℚ)) = 0 := by
    have hcomp : (algebraMap ℚ Conductor77MaxReal).comp
        (Int.castRingHom ℚ) = Int.castRingHom Conductor77MaxReal := by
      ext n
      simp
    simpa only [aeval_def, eval₂_map, hcomp] using
      aSectorX77Real_isRoot_G30
  exact minpoly.eq_of_irreducible_of_monic
    aSectorG30_irreducible_over_Q hroot
    (aSectorG30_monic.map (Int.castRingHom ℚ))

theorem aSectorX77Real_finrank :
    Module.finrank ℚ (Algebra.adjoin ℚ
      ({aSectorX77Real} : Set Conductor77MaxReal)) = 30 := by
  have hint : IsIntegral ℚ aSectorX77Real :=
    IsIntegral.of_finite ℚ aSectorX77Real
  have hsub := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    hint.isAlgebraic
  rw [← hsub]
  change Module.finrank ℚ ℚ⟮aSectorX77Real⟯ = 30
  rw [IntermediateField.adjoin.finrank hint, ← aSectorX77Real_minpoly]
  rw [natDegree_map_eq_of_injective (Int.cast_injective :
    Function.Injective (Int.castRingHom ℚ))]
  exact aSectorG30_natDegree

/-- The displayed A-coordinate generates the entire maximal real field. -/
theorem aSectorX77Real_generates_maxReal :
    Algebra.adjoin ℚ ({aSectorX77Real} : Set Conductor77MaxReal) = ⊤ :=
  conductor77_coordinate_generates_maxReal aSectorX77Real
    aSectorX77Real_finrank

/-- The concrete period and coordinate supply the A arithmetic model. -/
def aSectorConcreteCyclotomicModel : ASectorCyclotomicModel where
  periodField := conductor77PeriodField
  period_finrank := conductor77PeriodField_finrank
  period_is_abelian := conductor77PeriodField_isAbelianGalois
  squaredCoordinate := aSectorX77Real
  coordinate_finrank := aSectorX77Real_finrank

end
end Biunimodular.F11
