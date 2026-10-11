/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceGeometricFunctionAlgebra
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Biunimodular.F11
open Polynomial
noncomputable section

abbrev fixedSliceQuotientComplexPolynomial :=
  fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)

def fixedSliceFiveInvariantU : fixedSliceFiveFourierInvariantAlgebra :=
  fixedSliceFiveInvariantAlgebraEquivQuotient.symm
    (AdjoinRoot.root fixedSliceQuotientComplexPolynomial)

def fixedSliceFiveInvariantPowerBasis :
    PowerBasis ℂ fixedSliceFiveFourierInvariantAlgebra :=
  (AdjoinRoot.powerBasis fixedSliceQuotientP16Q_separable.map.ne_zero).map
    fixedSliceFiveInvariantAlgebraEquivQuotient.symm

/-- The transported generator is the actual quotient's `u` coordinate
on every geometric Fourier orbit. -/
theorem fixedSliceFiveInvariantU_eval (p : Even11FixedSlicePoint) :
    (fixedSliceFiveInvariantAlgebraEquivFunctions fixedSliceFiveInvariantU).1 p =
      even11FixedSliceQuotientU (Quotient.mk'' p) := by
  have h : fixedSliceFiveInvariantAlgebraEquivFunctions fixedSliceFiveInvariantU =
      fixedSliceQuotientAlgebraEquivInvariantFunctions
        (AdjoinRoot.root fixedSliceQuotientComplexPolynomial) := by
    simp [fixedSliceFiveInvariantU, fixedSliceFiveInvariantAlgebraEquivQuotient]
  rw [h]
  change fixedSliceQuotientComplexAlgebraEquivFunctions
      (AdjoinRoot.mk fixedSliceQuotientComplexPolynomial X) (Quotient.mk'' p) = _
  rw [fixedSliceQuotientComplexAlgebraEquivFunctions_mk, Polynomial.eval_X]

private theorem fixedSliceQuotientComplexPolynomial_leadingCoeff :
    fixedSliceQuotientComplexPolynomial.leadingCoeff = 279841 := by
  rw [Polynomial.leadingCoeff_map_of_injective (algebraMap ℚ ℂ).injective,
    Polynomial.leadingCoeff, fixedSliceQuotientP16Q_natDegree]
  norm_num [fixedSliceQuotientP16Q, fixedSliceQuotientP16, Polynomial.coeff_X]

/-- The multiplication-by-`u` operator on the actual Fourier invariant
algebra has precisely the monic degree-sixteen characteristic
polynomial. The matrix uses the certified power basis of that algebra. -/
theorem fixedSliceFiveInvariantU_charpoly :
    (Algebra.leftMulMatrix fixedSliceFiveInvariantPowerBasis.basis
      fixedSliceFiveInvariantU).charpoly =
        fixedSliceQuotientComplexPolynomial * C ((279841 : ℂ)⁻¹) := by
  rw [show fixedSliceFiveInvariantU = fixedSliceFiveInvariantPowerBasis.gen from rfl,
    charpoly_leftMulMatrix]
  change minpoly ℂ (fixedSliceFiveInvariantAlgebraEquivQuotient.symm
      (AdjoinRoot.powerBasis fixedSliceQuotientP16Q_separable.map.ne_zero).gen) = _
  rw [minpoly.algEquiv_eq]
  have h := AdjoinRoot.minpoly_powerBasis_gen (f := fixedSliceQuotientComplexPolynomial)
    fixedSliceQuotientP16Q_separable.map.ne_zero
  rw [fixedSliceQuotientComplexPolynomial_leadingCoeff] at h
  exact h

end
end Biunimodular.F11
