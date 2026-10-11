/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceFiveCoordinateAlgebra
import Biunimodular.F11.FixedSliceCoordinateAlgebraPoints
import Biunimodular.F11.SplitPolynomialFunctionAlgebra
import Biunimodular.F11.OrbitFunctionAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Biunimodular.F11
open Polynomial
noncomputable section

/-- Evaluation at the certified trace roots, indexed by the actual
projective fixed-slice points. -/
def fixedSliceTraceComplexAlgebraEquivFunctions :
    FixedSliceTraceComplexCoordinateAlgebra ≃ₐ[ℂ] (Even11FixedSlicePoint → ℂ) :=
  (splitPolynomialAlgebraEquivFunctions fixedSliceTraceComplexPolynomial
    fixedSliceTraceP32Q_separable.map).trans
    (AlgEquiv.piCongrLeft' ℂ (fun _ => ℂ)
      ((Set.equivOfEq (Polynomial.rootSet_map ℂ ℂ fixedSliceTraceP32Q)).trans
        (Equiv.ofBijective
          (even11FixedSliceTraceRootMap
            even11FixedSliceTraceGeometryCertificate.trace_isRoot)
          even11FixedSliceTraceGeometryCertificate.trace_bijective).symm))

/-- The original five-quadric algebra is the full algebra of complex
functions on its thirty-two certified geometric points. -/
def fixedSliceFiveAlgebraEquivFunctions :
    FixedSliceFiveCoordinateAlgebra ≃ₐ[ℂ] (Even11FixedSlicePoint → ℂ) :=
  fixedSliceFiveCoordinateAlgebraEquivTrace.trans
    fixedSliceTraceComplexAlgebraEquivFunctions

/-- Evaluation of the invariant polynomial at the actual quotient's
`u` values gives all complex functions on its sixteen points. -/
def fixedSliceQuotientComplexAlgebraEquivFunctions :
    FixedSliceQuotientComplexCoordinateAlgebra ≃ₐ[ℂ]
      (Even11FixedSliceFourierQuotient → ℂ) :=
  (splitPolynomialAlgebraEquivFunctions
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ))
    fixedSliceQuotientP16Q_separable.map).trans
    (AlgEquiv.piCongrLeft' ℂ (fun _ => ℂ)
      ((Set.equivOfEq (Polynomial.rootSet_map ℂ ℂ fixedSliceQuotientP16Q)).trans
        even11FixedSliceGeometryCertificate.quotientRootEquiv.symm))

@[simp] theorem fixedSliceQuotientComplexAlgebraEquivFunctions_mk
    (f : ℂ[X]) (q : Even11FixedSliceFourierQuotient) :
    fixedSliceQuotientComplexAlgebraEquivFunctions
      (AdjoinRoot.mk (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)) f) q =
        f.eval (even11FixedSliceQuotientU q) := by
  change f.eval (even11FixedSliceGeometryCertificate.quotientRootEquiv q).1 = _
  rw [Even11FixedSliceGeometryCertificate.quotientRootEquiv_value]

@[simp] theorem fixedSliceTraceComplexAlgebraEquivFunctions_mk
    (f : ℂ[X]) (p : Even11FixedSlicePoint) :
    fixedSliceTraceComplexAlgebraEquivFunctions
      (AdjoinRoot.mk fixedSliceTraceComplexPolynomial f) p =
        f.eval (even11FixedSliceTrace p) := by
  rfl

abbrev FixedSliceFourierInvariantFunctions :=
  orbitInvariantFunctionAlgebra ℂ Bool Even11FixedSlicePoint

/-- The degree-sixteen invariant algebra equals the invariant functions
under the concrete projective Fourier action. -/
def fixedSliceQuotientAlgebraEquivInvariantFunctions :
    FixedSliceQuotientComplexCoordinateAlgebra ≃ₐ[ℂ]
      FixedSliceFourierInvariantFunctions :=
  fixedSliceQuotientComplexAlgebraEquivFunctions.trans
    (orbitFunctionAlgebraEquiv ℂ Bool Even11FixedSlicePoint)

/-- Fourier invariants in the original five-quadric coordinate algebra,
defined by their values on the actual geometric Fourier orbits. -/
def fixedSliceFiveFourierInvariantAlgebra : Subalgebra ℂ FixedSliceFiveCoordinateAlgebra :=
  FixedSliceFourierInvariantFunctions.comap fixedSliceFiveAlgebraEquivFunctions.toAlgHom

/-- Pullback by the concrete Fourier permutation on geometric points,
acting on the original five-quadric coordinate algebra. -/
def fixedSliceFiveFourierPullback :
    FixedSliceFiveCoordinateAlgebra ≃ₐ[ℂ] FixedSliceFiveCoordinateAlgebra :=
  (fixedSliceFiveAlgebraEquivFunctions.trans
    (AlgEquiv.piCongrLeft' ℂ (fun _ => ℂ) even11FixedSliceFourier.symm)).trans
    fixedSliceFiveAlgebraEquivFunctions.symm

@[simp] theorem fixedSliceFiveFourierPullback_eval
    (f : FixedSliceFiveCoordinateAlgebra) (p : Even11FixedSlicePoint) :
    fixedSliceFiveAlgebraEquivFunctions (fixedSliceFiveFourierPullback f) p =
      fixedSliceFiveAlgebraEquivFunctions f (even11FixedSliceFourier p) := by
  simp [fixedSliceFiveFourierPullback, AlgEquiv.piCongrLeft'_apply]

theorem fixedSliceFiveFourierInvariantAlgebra_mem_iff
    (f : FixedSliceFiveCoordinateAlgebra) :
    f ∈ fixedSliceFiveFourierInvariantAlgebra ↔ fixedSliceFiveFourierPullback f = f := by
  constructor
  · intro hf
    apply fixedSliceFiveAlgebraEquivFunctions.injective
    funext p
    rw [fixedSliceFiveFourierPullback_eval]
    exact hf true p
  · intro hf
    change ∀ b p, fixedSliceFiveAlgebraEquivFunctions f (b +ᵥ p) =
      fixedSliceFiveAlgebraEquivFunctions f p
    intro b p
    cases b
    · rfl
    · change fixedSliceFiveAlgebraEquivFunctions f (even11FixedSliceFourier p) = _
      rw [← fixedSliceFiveFourierPullback_eval, hf]

def fixedSliceFiveInvariantEvaluation :
    fixedSliceFiveFourierInvariantAlgebra →ₐ[ℂ] FixedSliceFourierInvariantFunctions :=
  (fixedSliceFiveAlgebraEquivFunctions.toAlgHom.comp
    fixedSliceFiveFourierInvariantAlgebra.val).codRestrict
    FixedSliceFourierInvariantFunctions (fun f => f.2)

def fixedSliceFiveInvariantAlgebraEquivFunctions :
    fixedSliceFiveFourierInvariantAlgebra ≃ₐ[ℂ] FixedSliceFourierInvariantFunctions := by
  apply AlgEquiv.ofBijective fixedSliceFiveInvariantEvaluation
  constructor
  · intro f g h
    apply Subtype.ext
    apply fixedSliceFiveAlgebraEquivFunctions.injective
    exact congrArg Subtype.val h
  · intro f
    refine ⟨⟨fixedSliceFiveAlgebraEquivFunctions.symm f.1, ?_⟩, ?_⟩
    · change fixedSliceFiveAlgebraEquivFunctions
        (fixedSliceFiveAlgebraEquivFunctions.symm f.1) ∈ FixedSliceFourierInvariantFunctions
      simpa only [AlgEquiv.apply_symm_apply] using f.2
    · apply Subtype.ext
      exact fixedSliceFiveAlgebraEquivFunctions.apply_symm_apply f.1

/-- The actual Fourier invariant subalgebra of the original affine ring
is the algebra defined by the exact degree-sixteen invariant polynomial. -/
def fixedSliceFiveInvariantAlgebraEquivQuotient :
    fixedSliceFiveFourierInvariantAlgebra ≃ₐ[ℂ] FixedSliceQuotientComplexCoordinateAlgebra :=
  fixedSliceFiveInvariantAlgebraEquivFunctions.trans
    fixedSliceQuotientAlgebraEquivInvariantFunctions.symm

theorem fixedSliceFiveFourierInvariantAlgebra_finrank :
    Module.finrank ℂ fixedSliceFiveFourierInvariantAlgebra = 16 := by
  rw [fixedSliceFiveInvariantAlgebraEquivQuotient.toLinearEquiv.finrank_eq]
  exact fixedSliceQuotientComplexCoordinateAlgebra_finrank

end
end Biunimodular.F11
