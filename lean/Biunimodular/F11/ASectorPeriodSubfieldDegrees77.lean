/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodSubfields77
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma

set_option autoImplicit false

namespace Biunimodular.F11
open Polynomial
open scoped IntermediateField
noncomputable section

def periodQuadraticMinimalPolynomial77 : ℤ[X] := X^2 - 77
def periodCubicMinimalPolynomial77 : ℤ[X] := X^3 - X^2 - 2*X + 1

theorem periodQuadraticMinimalPolynomial77_monic : periodQuadraticMinimalPolynomial77.Monic := by
  simpa [periodQuadraticMinimalPolynomial77] using
    (monic_X_pow_sub_C (77 : ℤ) (by decide : 2 ≠ 0))

theorem periodCubicMinimalPolynomial77_monic : periodCubicMinimalPolynomial77.Monic := by
  let low : ℤ[X] := -X^2 - 2*X + 1
  have hlow : low.degree < 3 := by
    simp only [low]
    compute_degree; norm_num
  rw [show periodCubicMinimalPolynomial77 = X^3 + low by
    simp only [periodCubicMinimalPolynomial77, low]; ring]
  exact monic_X_pow_add hlow

theorem periodQuadraticMinimalPolynomial77_irreducible :
    Irreducible (periodQuadraticMinimalPolynomial77.map (Int.castRingHom ℚ)) := by
  have hmod : Irreducible (periodQuadraticMinimalPolynomial77.map (Int.castRingHom (ZMod 3))) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : (periodQuadraticMinimalPolynomial77.map (Int.castRingHom (ZMod 3))).natDegree = 2 := by
        norm_num [periodQuadraticMinimalPolynomial77]; compute_degree; norm_num
      rw [hdeg]
      decide
    · intro x
      simp only [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map,
        periodQuadraticMinimalPolynomial77, Polynomial.eval₂_sub,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat]
      fin_cases x <;> norm_num <;> reduce_mod_char <;> decide
  have hZ := Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3))
    periodQuadraticMinimalPolynomial77 periodQuadraticMinimalPolynomial77_monic hmod
  exact (periodQuadraticMinimalPolynomial77_monic.irreducible_iff_irreducible_map_fraction_map).1 hZ

theorem periodCubicMinimalPolynomial77_irreducible :
    Irreducible (periodCubicMinimalPolynomial77.map (Int.castRingHom ℚ)) := by
  have hmod : Irreducible (periodCubicMinimalPolynomial77.map (Int.castRingHom (ZMod 2))) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : (periodCubicMinimalPolynomial77.map (Int.castRingHom (ZMod 2))).natDegree = 3 := by
        norm_num [periodCubicMinimalPolynomial77]; compute_degree <;> norm_num
      rw [hdeg]
      decide
    · intro x
      simp only [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map,
        periodCubicMinimalPolynomial77, Polynomial.eval₂_add, Polynomial.eval₂_sub,
        Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
      fin_cases x <;> norm_num <;> reduce_mod_char <;> decide
  have hZ := Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
    periodCubicMinimalPolynomial77 periodCubicMinimalPolynomial77_monic hmod
  exact (periodCubicMinimalPolynomial77_monic.irreducible_iff_irreducible_map_fraction_map).1 hZ

theorem periodQuadraticGenerator77_minpoly :
    periodQuadraticMinimalPolynomial77.map (Int.castRingHom ℚ) =
      minpoly ℚ periodQuadraticGenerator77 := by
  have hr : Polynomial.aeval periodQuadraticGenerator77
      (periodQuadraticMinimalPolynomial77.map (Int.castRingHom ℚ)) = 0 := by
    simpa [periodQuadraticMinimalPolynomial77, Polynomial.aeval_def] using
      (sub_eq_zero.mpr periodQuadraticGenerator77_square)
  exact minpoly.eq_of_irreducible_of_monic periodQuadraticMinimalPolynomial77_irreducible hr
    (periodQuadraticMinimalPolynomial77_monic.map (Int.castRingHom ℚ))

theorem periodCubicGenerator77_minpoly :
    periodCubicMinimalPolynomial77.map (Int.castRingHom ℚ) = minpoly ℚ periodCubicGenerator77 := by
  have hr : Polynomial.aeval periodCubicGenerator77
      (periodCubicMinimalPolynomial77.map (Int.castRingHom ℚ)) = 0 := by
    simpa [periodCubicMinimalPolynomial77, Polynomial.aeval_def] using periodCubicGenerator77_relation
  exact minpoly.eq_of_irreducible_of_monic periodCubicMinimalPolynomial77_irreducible hr
    (periodCubicMinimalPolynomial77_monic.map (Int.castRingHom ℚ))

theorem conductor77QuadraticSubfield_finrank : Module.finrank ℚ conductor77QuadraticSubfield = 2 := by
  have hint : IsIntegral ℚ periodQuadraticGenerator77 := IsIntegral.of_finite ℚ _
  change Module.finrank ℚ ℚ⟮periodQuadraticGenerator77⟯ = 2
  rw [IntermediateField.adjoin.finrank hint, ← periodQuadraticGenerator77_minpoly]
  norm_num [periodQuadraticMinimalPolynomial77]; compute_degree; norm_num

theorem conductor77CubicSubfield_finrank : Module.finrank ℚ conductor77CubicSubfield = 3 := by
  have hint : IsIntegral ℚ periodCubicGenerator77 := IsIntegral.of_finite ℚ _
  change Module.finrank ℚ ℚ⟮periodCubicGenerator77⟯ = 3
  rw [IntermediateField.adjoin.finrank hint, ← periodCubicGenerator77_minpoly]
  norm_num [periodCubicMinimalPolynomial77]; compute_degree <;> norm_num

/-- The sextic Gaussian-period field is the compositum of the actual
quadratic and cubic subfields generated by the displayed period sums. -/
theorem conductor77PeriodField_eq_quadratic_sup_cubic :
    conductor77PeriodField = conductor77QuadraticSubfield ⊔ conductor77CubicSubfield := by
  let L := conductor77QuadraticSubfield ⊔ conductor77CubicSubfield
  have hle : L ≤ conductor77PeriodField :=
    sup_le conductor77QuadraticSubfield_le_periodField conductor77CubicSubfield_le_periodField
  have hd2 : 2 ∣ Module.finrank ℚ L := by
    rw [← conductor77QuadraticSubfield_finrank]
    exact IntermediateField.finrank_dvd_of_le_right (show conductor77QuadraticSubfield ≤ L from le_sup_left)
  have hd3 : 3 ∣ Module.finrank ℚ L := by
    rw [← conductor77CubicSubfield_finrank]
    exact IntermediateField.finrank_dvd_of_le_right (show conductor77CubicSubfield ≤ L from le_sup_right)
  have hd6 : 6 ∣ Module.finrank ℚ L := by
    simpa only [show Nat.lcm 2 3 = 6 by decide] using Nat.lcm_dvd hd2 hd3
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hupper : Module.finrank ℚ L ≤ 6 := by
    rw [← conductor77PeriodField_finrank]
    exact IntermediateField.finrank_le_of_le_right hle
  have hdim : Module.finrank ℚ L = Module.finrank ℚ conductor77PeriodField := by
    rw [conductor77PeriodField_finrank]
    exact le_antisymm hupper (Nat.le_of_dvd hpos hd6)
  exact (IntermediateField.eq_of_le_of_finrank_eq hle hdim).symm

end
end Biunimodular.F11
