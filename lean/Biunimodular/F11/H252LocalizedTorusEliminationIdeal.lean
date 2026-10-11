/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252LocalizedTorusAlgebra
import Biunimodular.F11.H252UniversalElimination
import Biunimodular.F11.EliminationIdealFromRootLifts
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

open Polynomial

noncomputable section

theorem h252LocalizedTorus_generator_zero (i : Fin 7) :
    Ideal.Quotient.mkₐ ℂ h252LocalizedTorusIdeal (h252LocalizedTorusGenerators i) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

theorem h252LocalizedTorusCoordinate_eliminant_zero :
    h252LocalizedTorusCoordinate h252RurComplexPolynomial = 0 := by
  let z := h252LocalizedTorusVar
  have h1 : h252TorusF1 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 := by
    simpa [h252LocalizedTorusGenerators, z, h252LocalizedTorusVar, h252TorusF1]
      using h252LocalizedTorus_generator_zero 0
  have h2 : h252TorusF2 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 := by
    simpa [h252LocalizedTorusGenerators, z, h252LocalizedTorusVar, h252TorusF2]
      using h252LocalizedTorus_generator_zero 1
  have h3 : h252TorusF3 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 := by
    simpa [h252LocalizedTorusGenerators, z, h252LocalizedTorusVar, h252TorusF3]
      using h252LocalizedTorus_generator_zero 2
  have h4 : h252TorusF4 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 := by
    simpa [h252LocalizedTorusGenerators, z, h252LocalizedTorusVar, h252TorusF4]
      using h252LocalizedTorus_generator_zero 3
  have h5 : h252TorusF5 (z 0) (z 1) (z 2) (z 3) (z 4) = 0 := by
    simpa [h252LocalizedTorusGenerators, z, h252LocalizedTorusVar, h252TorusF5]
      using h252LocalizedTorus_generator_zero 4
  have hS : h252TorusS (z 0) (z 1) (z 2) (z 3) (z 5) (z 4) = 0 := by
    simpa [h252LocalizedTorusGenerators, z, h252LocalizedTorusVar, h252TorusS, h252TorusD]
      using h252LocalizedTorus_generator_zero 5
  have hc : (z 4) ^ 2 - 2 * (z 6) * (z 4) - 1 = 0 := by
    have htwo : (Ideal.Quotient.mk h252LocalizedTorusIdeal)
        (2 : H252LocalizedTorusPolynomialRing) = (2 : H252LocalizedTorusAlgebra) := by
      rw [show (2 : H252LocalizedTorusPolynomialRing) = 1 + 1 by ring, map_add, map_one]
      ring
    simpa [h252LocalizedTorusGenerators, z, h252LocalizedTorusVar, htwo]
      using h252LocalizedTorus_generator_zero 6
  have hcoord : (z 4) ^ 2 - 1 = 2 * (z 4) * (z 6) := by
    linear_combination hc
  have he := h252UniversalElimination
    (z 0) (z 1) (z 2) (z 3) (z 5) (z 4) (z 6) h1 h2 h3 h4 h5 hS hcoord
  change (Polynomial.aeval (z 6) : ℂ[X] →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom
    (integerCoefficientEval (X : ℂ[X]) h252RurHCoeffs) = 0
  rw [integerCoefficientEval_map]
  have hX : (Polynomial.aeval (z 6) : ℂ[X] →ₐ[ℂ] H252LocalizedTorusAlgebra).toRingHom
      (X : ℂ[X]) = z 6 := Polynomial.aeval_X (z 6)
  rw [hX]
  exact he

/-- Exact kernel equality for the original seven-generator localized torus
system, proved by ideal membership and explicit lifts of all eliminant roots.
No radicalization of the system ideal is used. -/
theorem h252LocalizedTorusCoordinate_ker :
    RingHom.ker h252LocalizedTorusCoordinate =
      Ideal.span ({h252RurComplexPolynomial} : Set ℂ[X]) := by
  apply coordinateKernel_eq_span_of_separable_root_lifts
    h252LocalizedTorusCoordinate h252RurComplexPolynomial
    h252RurComplexPolynomial_separable (IsAlgClosed.splits _)
    h252LocalizedTorusCoordinate_eliminant_zero
  intro x hx
  exact ⟨h252RurTorusPointEvaluation x hx, h252RurTorusPointEvaluation_coordinate x hx⟩

def h252LocalizedTorusEliminationIdeal : Ideal ℂ[X] :=
  Ideal.comap (Polynomial.aeval (MvPolynomial.X (6 : Fin 7)) :
    ℂ[X] →ₐ[ℂ] H252LocalizedTorusPolynomialRing).toRingHom h252LocalizedTorusIdeal

theorem h252LocalizedTorusEliminationIdeal_eq_kernel :
    h252LocalizedTorusEliminationIdeal = RingHom.ker h252LocalizedTorusCoordinate := by
  have hf : h252LocalizedTorusCoordinate =
      (Ideal.Quotient.mkₐ ℂ h252LocalizedTorusIdeal).comp
        (Polynomial.aeval (MvPolynomial.X (6 : Fin 7))) := by
    apply Polynomial.algHom_ext
    simp [h252LocalizedTorusCoordinate, h252LocalizedTorusVar]
  ext p
  change Polynomial.aeval (MvPolynomial.X (6 : Fin 7)) p ∈ h252LocalizedTorusIdeal ↔
    h252LocalizedTorusCoordinate p = 0
  rw [hf, AlgHom.comp_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.symm

theorem h252LocalizedTorusEliminationIdeal_eq_span :
    h252LocalizedTorusEliminationIdeal =
      Ideal.span ({h252RurComplexPolynomial} : Set ℂ[X]) := by
  rw [h252LocalizedTorusEliminationIdeal_eq_kernel, h252LocalizedTorusCoordinate_ker]

end

end Biunimodular.F11
