/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252FullComplexScheme
import Biunimodular.F11.H252ReverseRurCriterion
import Biunimodular.F11.CoordinateRootSeparation

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

theorem h252RurTorusPointEvaluation_var (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) (i : Fin 7) :
    h252RurTorusPointEvaluation x hx (h252LocalizedTorusVar i) =
      h252RurTorusPoint x i := by
  have h := AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp h252LocalizedTorusIdeal
      (MvPolynomial.aeval (h252RurTorusPoint x))
      (fun p hp ↦ RingHom.mem_ker.mp (h252RurTorusPoint_ideal_zero x hx hp)))
    (MvPolynomial.X i)
  simp [h252RurTorusPointEvaluation, h252LocalizedTorusVar, AlgHom.comp_apply] at h ⊢

theorem h252RurTorusPoint_castSucc (x : ℂ) (i : Fin 6) :
    h252RurTorusPoint x i.castSucc =
      integerCoefficientEval x (h252RurNumeratorCoefficients i) / h252RurDenominator x := by
  fin_cases i <;> simp [h252RurTorusPoint, h252RurNumeratorCoefficients]

/-- The six reverse RUR formulas hold in the original localized quotient,
including its scheme structure. -/
theorem h252LocalizedTorus_reverse_rur (i : Fin 6) :
    h252LocalizedTorusCoordinate (integerCoefficientEval (X : ℂ[X]) h252RurDCoeffs) *
      h252LocalizedTorusVar i.castSucc =
    h252LocalizedTorusCoordinate
      (integerCoefficientEval (X : ℂ[X]) (h252RurNumeratorCoefficients i)) := by
  apply coordinate_eq_of_root_evaluations h252LocalizedTorusCoordinate
    h252RurComplexPolynomial h252RurComplexPolynomial_separable
    (IsAlgClosed.splits _) h252LocalizedTorusCoordinate_surjective
    h252LocalizedTorusCoordinate_ker h252RurTorusPointEvaluation
    h252RurTorusPointEvaluation_coordinate
  intro x hx
  have hcomp : (h252RurTorusPointEvaluation x hx).comp h252LocalizedTorusCoordinate =
      Polynomial.aeval x := by
    apply Polynomial.algHom_ext
    simpa using h252RurTorusPointEvaluation_coordinate x hx
  have heval (cs : List ℤ) :
      h252RurTorusPointEvaluation x hx
        (h252LocalizedTorusCoordinate (integerCoefficientEval (X : ℂ[X]) cs)) =
      integerCoefficientEval x cs := by
    change ((h252RurTorusPointEvaluation x hx).comp h252LocalizedTorusCoordinate) _ = _
    rw [hcomp]
    simpa using integerCoefficientEval_map
      (Polynomial.aeval x : ℂ[X] →ₐ[ℂ] ℂ).toRingHom X cs
  rw [map_mul, heval, heval, h252RurTorusPointEvaluation_var, h252RurTorusPoint_castSucc]
  exact mul_div_cancel₀ _ (h252RurDenominator_ne_zero x hx)

/-- These are actual ideal memberships, without taking radicals. -/
theorem h252LocalizedTorus_reverse_rur_mem (i : Fin 6) :
    integerCoefficientEval (MvPolynomial.X (6 : Fin 7)) h252RurDCoeffs *
        MvPolynomial.X i.castSucc -
      integerCoefficientEval (MvPolynomial.X (6 : Fin 7))
        (h252RurNumeratorCoefficients i) ∈ h252LocalizedTorusIdeal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mkₐ ℂ h252LocalizedTorusIdeal) _ = 0
  have hmap (cs : List ℤ) :
      (Ideal.Quotient.mkₐ ℂ h252LocalizedTorusIdeal)
        (integerCoefficientEval (MvPolynomial.X (6 : Fin 7)) cs) =
      integerCoefficientEval (h252LocalizedTorusVar 6) cs :=
    integerCoefficientEval_map (Ideal.Quotient.mkₐ ℂ h252LocalizedTorusIdeal).toRingHom
      (MvPolynomial.X 6) cs
  rw [map_sub, map_mul, hmap, hmap]
  have hf (cs : List ℤ) :
      h252LocalizedTorusCoordinate (integerCoefficientEval (X : ℂ[X]) cs) =
        integerCoefficientEval (h252LocalizedTorusVar 6) cs := by
    simpa [h252LocalizedTorusCoordinate] using integerCoefficientEval_map
      h252LocalizedTorusCoordinate.toRingHom X cs
  rw [← hf, ← hf]
  exact sub_eq_zero.mpr (h252LocalizedTorus_reverse_rur i)

/-- Every complex point is the specified lift of its RUR coordinate. -/
theorem h252LocalizedTorus_point_unique
    (g : H252LocalizedTorusAlgebra →ₐ[ℂ] ℂ) :
    ∃ hx : h252RurComplexPolynomial.IsRoot (g (h252LocalizedTorusCoordinate X)),
      g = h252RurTorusPointEvaluation (g (h252LocalizedTorusCoordinate X)) hx := by
  let x := g (h252LocalizedTorusCoordinate X)
  have hcomp : g.comp h252LocalizedTorusCoordinate = Polynomial.aeval x := by
    apply Polynomial.algHom_ext
    simp [x]
  have hx : h252RurComplexPolynomial.IsRoot x := by
    change h252RurComplexPolynomial.eval x = 0
    have h : (g.comp h252LocalizedTorusCoordinate) h252RurComplexPolynomial = 0 := by
      simp [AlgHom.comp_apply, h252LocalizedTorusCoordinate_eliminant_zero]
    simpa [hcomp] using h
  refine ⟨hx, ?_⟩
  have hlift : (h252RurTorusPointEvaluation x hx).comp h252LocalizedTorusCoordinate =
      Polynomial.aeval x := by
    apply Polynomial.algHom_ext
    simpa using h252RurTorusPointEvaluation_coordinate x hx
  ext a
  obtain ⟨q, rfl⟩ := h252LocalizedTorusCoordinate_surjective a
  exact AlgHom.congr_fun (hcomp.trans hlift.symm) q

/-- The displayed rational formulas parametrize the complex points bijectively. -/
theorem h252RurTorusPointEvaluation_bijective :
    Function.Bijective (fun x : {x : ℂ // h252RurComplexPolynomial.IsRoot x} =>
      h252RurTorusPointEvaluation x.val x.property) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have heval := AlgHom.congr_fun h (h252LocalizedTorusCoordinate X)
    simpa only [h252RurTorusPointEvaluation_coordinate] using heval
  · intro g
    obtain ⟨hx, hg⟩ := h252LocalizedTorus_point_unique g
    exact ⟨⟨g (h252LocalizedTorusCoordinate X), hx⟩, hg.symm⟩

end
end Biunimodular.F11
