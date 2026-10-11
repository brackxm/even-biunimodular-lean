/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252ComplexPhaseReconstruction
import Biunimodular.F11.H252ComplexPhaseForward
import Biunimodular.F11.H252LocalizedTorusAlgebra
import Biunimodular.F11.EliminationIdealFromRootLifts
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

open Polynomial
noncomputable section

theorem h252RurComplexPhaseRootLift (x : ℂ)
    (hx : h252RurComplexPolynomial.IsRoot x) :
    ∃ a b : Fin 5 → ℂ, (∀ i, a i ^ 2 + b i ^ 2 = 1) ∧
      h252ComplexPhaseE1 a b = 0 ∧ h252ComplexPhaseE2 a b = 0 ∧
      h252ComplexPhaseE3 a b = 0 ∧ h252ComplexPhaseE4 a b = 0 ∧
      h252ComplexPhaseE5 a b = 0 ∧ Complex.I * b 4 = x := by
  let z : Fin 5 → ℂ := ![integerCoefficientEval x h252RurN1Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN2Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN3Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN4Coeffs / h252RurDenominator x,
    integerCoefficientEval x h252RurN5Coeffs / h252RurDenominator x]
  let w := integerCoefficientEval x h252RurN6Coeffs / h252RurDenominator x
  have hs : w * h252TorusDVector z = 1 := by
    have h := h252RurSaturation_zero x hx
    apply sub_eq_zero.mp
    simpa [z, w, h252TorusDVector, h252TorusD, h252RurDenominator, mul_assoc] using h
  let t : Fin 5 → ℂ := fun i ↦ w * h252TorusCofactor z i
  apply h252ComplexPhaseFromUnitTorus z t x (h252TorusCofactor_units z w hs)
  · simpa [z, h252RurDenominator] using h252RurF1_zero x hx
  · simpa [z, h252RurDenominator] using h252RurF2_zero x hx
  · simpa [z, h252RurDenominator] using h252RurF3_zero x hx
  · simpa [z, h252RurDenominator] using h252RurF4_zero x hx
  · simpa [z, h252RurDenominator] using h252RurF5_zero x hx
  · have h : z 4 ^ 2 - 2 * x * z 4 - 1 = 0 := by
      simpa [z, h252RurDenominator] using h252RurCoordinate_zero x hx
    linear_combination h

abbrev H252ComplexPhasePolynomialRing := MvPolynomial (Fin 10) ℂ

def h252ComplexPhaseAVars : Fin 5 → H252ComplexPhasePolynomialRing :=
  ![MvPolynomial.X 0, MvPolynomial.X 2, MvPolynomial.X 4, MvPolynomial.X 6, MvPolynomial.X 8]

def h252ComplexPhaseBVars : Fin 5 → H252ComplexPhasePolynomialRing :=
  ![MvPolynomial.X 1, MvPolynomial.X 3, MvPolynomial.X 5, MvPolynomial.X 7, MvPolynomial.X 9]

/-- The five circle equations followed by the five original phase equations. -/
def h252ComplexPhaseGenerators : Fin 10 → H252ComplexPhasePolynomialRing :=
  let a := h252ComplexPhaseAVars
  let b := h252ComplexPhaseBVars
  ![a 0 ^ 2 + b 0 ^ 2 - 1, a 1 ^ 2 + b 1 ^ 2 - 1,
    a 2 ^ 2 + b 2 ^ 2 - 1, a 3 ^ 2 + b 3 ^ 2 - 1, a 4 ^ 2 + b 4 ^ 2 - 1,
    h252ComplexPhaseE1 a b, h252ComplexPhaseE2 a b, h252ComplexPhaseE3 a b,
    h252ComplexPhaseE4 a b, h252ComplexPhaseE5 a b]

def h252ComplexPhaseIdeal : Ideal H252ComplexPhasePolynomialRing :=
  Ideal.span (Set.range h252ComplexPhaseGenerators)

abbrev H252ComplexPhaseAlgebra := H252ComplexPhasePolynomialRing ⧸ h252ComplexPhaseIdeal

def h252ComplexPhaseA (i : Fin 5) : H252ComplexPhaseAlgebra :=
  Ideal.Quotient.mkₐ ℂ h252ComplexPhaseIdeal (h252ComplexPhaseAVars i)

def h252ComplexPhaseB (i : Fin 5) : H252ComplexPhaseAlgebra :=
  Ideal.Quotient.mkₐ ℂ h252ComplexPhaseIdeal (h252ComplexPhaseBVars i)

def h252ComplexPhaseXCoordinate : ℂ[X] →ₐ[ℂ] H252ComplexPhaseAlgebra :=
  Polynomial.aeval ((algebraMap ℂ H252ComplexPhaseAlgebra Complex.I) * h252ComplexPhaseB 4)

theorem h252ComplexPhase_generator_zero (i : Fin 10) :
    Ideal.Quotient.mkₐ ℂ h252ComplexPhaseIdeal (h252ComplexPhaseGenerators i) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

theorem h252ComplexPhase_circle (i : Fin 5) :
    h252ComplexPhaseA i ^ 2 + h252ComplexPhaseB i ^ 2 = 1 := by
  fin_cases i
  · apply sub_eq_zero.mp
    simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB]
      using h252ComplexPhase_generator_zero 0
  · apply sub_eq_zero.mp
    simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB]
      using h252ComplexPhase_generator_zero 1
  · apply sub_eq_zero.mp
    simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB]
      using h252ComplexPhase_generator_zero 2
  · apply sub_eq_zero.mp
    simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB]
      using h252ComplexPhase_generator_zero 3
  · apply sub_eq_zero.mp
    simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB]
      using h252ComplexPhase_generator_zero 4

theorem h252ComplexPhase_equation1 :
    h252ComplexPhaseE1 h252ComplexPhaseA h252ComplexPhaseB = 0 := by
  have htwo : (Ideal.Quotient.mk h252ComplexPhaseIdeal)
      (2 : H252ComplexPhasePolynomialRing) = (2 : H252ComplexPhaseAlgebra) := by
    rw [show (2 : H252ComplexPhasePolynomialRing) = 1 + 1 by ring, map_add, map_one]
    ring
  simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB,
    h252ComplexPhaseE1, htwo] using h252ComplexPhase_generator_zero 5

theorem h252ComplexPhase_equation2 :
    h252ComplexPhaseE2 h252ComplexPhaseA h252ComplexPhaseB = 0 := by
  have htwo : (Ideal.Quotient.mk h252ComplexPhaseIdeal)
      (2 : H252ComplexPhasePolynomialRing) = (2 : H252ComplexPhaseAlgebra) := by
    rw [show (2 : H252ComplexPhasePolynomialRing) = 1 + 1 by ring, map_add, map_one]
    ring
  simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB,
    h252ComplexPhaseE2, htwo] using h252ComplexPhase_generator_zero 6

theorem h252ComplexPhase_equation3 :
    h252ComplexPhaseE3 h252ComplexPhaseA h252ComplexPhaseB = 0 := by
  have htwo : (Ideal.Quotient.mk h252ComplexPhaseIdeal)
      (2 : H252ComplexPhasePolynomialRing) = (2 : H252ComplexPhaseAlgebra) := by
    rw [show (2 : H252ComplexPhasePolynomialRing) = 1 + 1 by ring, map_add, map_one]
    ring
  simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB,
    h252ComplexPhaseE3, htwo] using h252ComplexPhase_generator_zero 7

theorem h252ComplexPhase_equation4 :
    h252ComplexPhaseE4 h252ComplexPhaseA h252ComplexPhaseB = 0 := by
  have htwo : (Ideal.Quotient.mk h252ComplexPhaseIdeal)
      (2 : H252ComplexPhasePolynomialRing) = (2 : H252ComplexPhaseAlgebra) := by
    rw [show (2 : H252ComplexPhasePolynomialRing) = 1 + 1 by ring, map_add, map_one]
    ring
  simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB,
    h252ComplexPhaseE4, htwo] using h252ComplexPhase_generator_zero 8

theorem h252ComplexPhase_equation5 :
    h252ComplexPhaseE5 h252ComplexPhaseA h252ComplexPhaseB = 0 := by
  have htwo : (Ideal.Quotient.mk h252ComplexPhaseIdeal)
      (2 : H252ComplexPhasePolynomialRing) = (2 : H252ComplexPhaseAlgebra) := by
    rw [show (2 : H252ComplexPhasePolynomialRing) = 1 + 1 by ring, map_add, map_one]
    ring
  simpa [h252ComplexPhaseGenerators, h252ComplexPhaseA, h252ComplexPhaseB,
    h252ComplexPhaseE5, htwo] using h252ComplexPhase_generator_zero 9

theorem h252ComplexPhaseXCoordinate_eliminant_zero :
    h252ComplexPhaseXCoordinate h252RurComplexPolynomial = 0 := by
  have he := h252ComplexPhaseForward h252ComplexPhaseA h252ComplexPhaseB
    h252ComplexPhase_circle h252ComplexPhase_equation1 h252ComplexPhase_equation2
    h252ComplexPhase_equation3 h252ComplexPhase_equation4 h252ComplexPhase_equation5
  let x := (algebraMap ℂ H252ComplexPhaseAlgebra Complex.I) * h252ComplexPhaseB 4
  change (Polynomial.aeval x : ℂ[X] →ₐ[ℂ] H252ComplexPhaseAlgebra).toRingHom
    (integerCoefficientEval (X : ℂ[X]) h252RurHCoeffs) = 0
  rw [integerCoefficientEval_map]
  have hX : (Polynomial.aeval x : ℂ[X] →ₐ[ℂ] H252ComplexPhaseAlgebra).toRingHom
      (X : ℂ[X]) = x := Polynomial.aeval_X x
  rw [hX]
  exact he

def h252ComplexPhasePoint (a b : Fin 5 → ℂ) : Fin 10 → ℂ :=
  ![a 0, b 0, a 1, b 1, a 2, b 2, a 3, b 3, a 4, b 4]

theorem h252ComplexPhasePoint_ideal_zero (a b : Fin 5 → ℂ)
    (hc : ∀ i, a i ^ 2 + b i ^ 2 = 1)
    (h1 : h252ComplexPhaseE1 a b = 0) (h2 : h252ComplexPhaseE2 a b = 0)
    (h3 : h252ComplexPhaseE3 a b = 0) (h4 : h252ComplexPhaseE4 a b = 0)
    (h5 : h252ComplexPhaseE5 a b = 0) :
    h252ComplexPhaseIdeal ≤
      RingHom.ker (MvPolynomial.aeval (h252ComplexPhasePoint a b)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨i, rfl⟩
  apply RingHom.mem_ker.mpr
  fin_cases i
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint] using sub_eq_zero.mpr (hc 0)
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint] using sub_eq_zero.mpr (hc 1)
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint] using sub_eq_zero.mpr (hc 2)
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint] using sub_eq_zero.mpr (hc 3)
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint] using sub_eq_zero.mpr (hc 4)
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint, h252ComplexPhaseE1] using h1
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint, h252ComplexPhaseE2] using h2
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint, h252ComplexPhaseE3] using h3
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint, h252ComplexPhaseE4] using h4
  · simpa [h252ComplexPhaseGenerators, h252ComplexPhaseAVars,
      h252ComplexPhaseBVars, h252ComplexPhasePoint, h252ComplexPhaseE5] using h5

/-- Exact elimination in the rotated coordinate x = i k for the original
circle and phase ideal, without replacing it by its radical. -/
theorem h252ComplexPhaseXCoordinate_ker :
    RingHom.ker h252ComplexPhaseXCoordinate =
      Ideal.span ({h252RurComplexPolynomial} : Set ℂ[X]) := by
  apply coordinateKernel_eq_span_of_separable_root_lifts
    h252ComplexPhaseXCoordinate h252RurComplexPolynomial
    h252RurComplexPolynomial_separable (IsAlgClosed.splits _)
    h252ComplexPhaseXCoordinate_eliminant_zero
  intro x hx
  obtain ⟨a, b, hc, h1, h2, h3, h4, h5, hk⟩ := h252RurComplexPhaseRootLift x hx
  let hzero := h252ComplexPhasePoint_ideal_zero a b hc h1 h2 h3 h4 h5
  let g : H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ h252ComplexPhaseIdeal
      (MvPolynomial.aeval (h252ComplexPhasePoint a b))
      (fun _p hp ↦ RingHom.mem_ker.mp (hzero hp))
  refine ⟨g, ?_⟩
  have hb : g (h252ComplexPhaseB 4) = b 4 := by
    simp [g, h252ComplexPhaseB, h252ComplexPhaseBVars,
      h252ComplexPhasePoint]
  simpa only [h252ComplexPhaseXCoordinate, Polynomial.aeval_X, map_mul,
    AlgHom.commutes, hb, Algebra.algebraMap_self, RingHom.id_apply] using hk

end
end Biunimodular.F11
