/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.R102ExteriorPositiveData

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial
noncomputable section

theorem r102Horner_eval_nonneg (cs : List ℚ) (t : ℝ)
    (ht : 0 ≤ t) (hcs : ∀ c ∈ cs, 0 ≤ c) :
    0 ≤ ((polynomialOfCoefficientsQ11 cs).map (algebraMap ℚ ℝ)).eval t := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [polynomialOfCoefficientsQ11_cons, Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    exact add_nonneg (Rat.cast_nonneg.mpr (hcs c (by simp)))
      (mul_nonneg ht (ih (fun x hx => hcs x (by simp [hx]))))

theorem r102Horner_eval_pos (cs : List ℚ) (t : ℝ)
    (ht : 0 ≤ t) (hne : cs ≠ []) (hcs : ∀ c ∈ cs, 0 < c) :
    0 < ((polynomialOfCoefficientsQ11 cs).map (algebraMap ℚ ℝ)).eval t := by
  cases cs with
  | nil => exact (hne rfl).elim
  | cons c cs =>
    simp only [polynomialOfCoefficientsQ11_cons, Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    exact add_pos_of_pos_of_nonneg (Rat.cast_pos.mpr (hcs c (by simp)))
      (mul_nonneg ht (r102Horner_eval_nonneg cs t ht
        (fun x hx => (hcs x (by simp [hx])).le)))

theorem r102_exterior_bernstein_identity11 :
    r102SquaredYQ11.comp (C 1 + C (1 / 16) * X) =
      bernsteinCombinationQ11 51 0 r102ExteriorBernsteinCoeffs11 := by
  change (polynomialOfCoefficientsQ11
      (r102SquaredCoeffs11.map (fun c => (c : ℚ)))).comp _ = _
  rw [← polynomialOfCoefficientsQ11_affine,
    ← polynomialOfCoefficientsQ11_bernsteinCombination]
  exact congrArg polynomialOfCoefficientsQ11 r102_exterior_bernstein_coefficients_exact11

theorem r102SquaredYR11_pos_near_exterior (y : ℝ)
    (hy : 1 ≤ y) (hyend : y < 17 / 16) : 0 < r102SquaredYR11.eval y := by
  let t : ℝ := 16 * (y - 1)
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have htail : ∀ x ∈ r102ExteriorBernsteinCoeffs11.tail, 0 ≤ x := by
    intro x hx
    exact (r102ExteriorBernsteinCoeffs11_pos x (List.mem_of_mem_tail hx)).le
  have hpos := bernsteinCombinationQ11_eval_pos_at_zero_index
    51 (r102ExteriorBernsteinCoeffs11[0]!) r102ExteriorBernsteinCoeffs11.tail
    t ht0 ht1 (by native_decide) htail
  have hlist : (r102ExteriorBernsteinCoeffs11[0]!) ::
      r102ExteriorBernsteinCoeffs11.tail = r102ExteriorBernsteinCoeffs11 := by native_decide
  rw [hlist] at hpos
  have heval := congrArg (fun p : ℝ[X] => p.eval t)
    (congrArg (Polynomial.map (algebraMap ℚ ℝ)) r102_exterior_bernstein_identity11)
  simp only [Polynomial.map_comp, Polynomial.eval_comp] at heval
  rw [← heval] at hpos
  have harg : ((C 1 + C (1 / 16) * X : ℚ[X]).map (algebraMap ℚ ℝ)).eval t = y := by
    dsimp [t]
    norm_num
    ring
  rw [harg] at hpos
  exact hpos

theorem r102SquaredYR11_pos_far_exterior (y : ℝ)
    (hy : 17 / 16 ≤ y) : 0 < r102SquaredYR11.eval y := by
  let t : ℝ := y - 17 / 16
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpos := r102Horner_eval_pos r102ExteriorTaylorCoeffs11 t ht
    r102ExteriorTaylorCoeffs11_nonempty r102ExteriorTaylorCoeffs11_pos
  have hid : polynomialOfCoefficientsQ11 r102ExteriorTaylorCoeffs11 =
      r102SquaredYQ11.comp (C (17 / 16) + C 1 * X) :=
    polynomialOfCoefficientsQ11_affine _ _ _
  rw [hid, Polynomial.map_comp, Polynomial.eval_comp] at hpos
  have harg : ((C (17 / 16) + C 1 * X : ℚ[X]).map (algebraMap ℚ ℝ)).eval t = y := by
    dsimp [t]
    norm_num
  rw [harg] at hpos
  exact hpos

theorem r102SquaredYR11_pos_of_nonneg (y : ℝ) (hy : 0 ≤ y) :
    0 < r102SquaredYR11.eval y := by
  by_cases h1 : y ≤ 1
  · exact r102SquaredYR11_pos_of_mem_Icc y hy h1
  · by_cases h2 : y < 17 / 16
    · exact r102SquaredYR11_pos_near_exterior y (le_of_not_ge h1) h2
    · exact r102SquaredYR11_pos_far_exterior y (le_of_not_gt h2)

/-- The the degree-102 cofactor is strictly positive at every real number. -/
theorem r102KR11_pos (k : ℝ) : 0 < r102KR11.eval k := by
  rw [r102KR11_eval]
  exact r102SquaredYR11_pos_of_nonneg _ (sq_nonneg k)

theorem r102KR11_not_isRoot (k : ℝ) : ¬r102KR11.IsRoot k :=
  ne_of_gt (r102KR11_pos k)

end
end Biunimodular.F11
