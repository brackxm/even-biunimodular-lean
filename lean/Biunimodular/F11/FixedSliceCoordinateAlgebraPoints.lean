/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceQuotientCoordinateAlgebra
import Biunimodular.F11.FixedSliceTraceCoordinateAlgebra

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-- Complex points of the reduced trace algebra are the roots of its
degree-thirty-two defining polynomial. -/
def fixedSliceTraceAlgHomEquivRoot :
    (FixedSliceTraceCoordinateAlgebra →ₐ[ℚ] ℂ) ≃
      FixedSliceTraceRoot :=
  (AdjoinRoot.equiv ℂ ℚ fixedSliceTraceP32Q
    fixedSliceTraceP32Q_ne_zero).trans
    ((Equiv.refl ℂ).subtypeEquiv fun x => by
      exact (mem_aroots (p := fixedSliceTraceP32Q) (a := x)).trans
        (mem_rootSet (p := fixedSliceTraceP32Q) (a := x)).symm)

/-- The trace-shape certificate identifies the complex points of the
univariate trace algebra with the concrete projective fixed-slice points. -/
def fixedSliceTraceAlgHomEquivFixedSlice :
    (FixedSliceTraceCoordinateAlgebra →ₐ[ℚ] ℂ) ≃
      Even11FixedSlicePoint :=
  fixedSliceTraceAlgHomEquivRoot.trans
    (Equiv.ofBijective
      (even11FixedSliceTraceRootMap
        even11FixedSliceTraceGeometryCertificate.trace_isRoot)
      even11FixedSliceTraceGeometryCertificate.trace_bijective).symm

/-- Complex points of the reduced quotient invariant algebra are the roots
of the degree-sixteen defining polynomial. -/
def fixedSliceQuotientAlgHomEquivRoot :
    (FixedSliceQuotientCoordinateAlgebra →ₐ[ℚ] ℂ) ≃
      FixedSliceQuotientRoot :=
  (AdjoinRoot.equiv ℂ ℚ fixedSliceQuotientP16Q
    fixedSliceQuotientP16Q_separable.ne_zero).trans
    ((Equiv.refl ℂ).subtypeEquiv fun x => by
      exact (mem_aroots (p := fixedSliceQuotientP16Q) (a := x)).trans
        (mem_rootSet (p := fixedSliceQuotientP16Q) (a := x)).symm)

/-- The exact quotient certificate identifies the complex points of the
univariate invariant algebra with the concrete Fourier quotient points. -/
def fixedSliceQuotientAlgHomEquivFixedSliceQuotient :
    (FixedSliceQuotientCoordinateAlgebra →ₐ[ℚ] ℂ) ≃
      Even11FixedSliceFourierQuotient :=
  fixedSliceQuotientAlgHomEquivRoot.trans
    even11FixedSliceGeometryCertificate.quotientRootEquiv.symm

/-- On geometric points, the trace algebra is a two-sheeted cover of the
quotient invariant algebra, with the sheets exchanged by Fourier. -/
def fixedSliceTraceAlgHomTwoSheeted :
    (FixedSliceTraceCoordinateAlgebra →ₐ[ℚ] ℂ) ≃
      ((FixedSliceQuotientCoordinateAlgebra →ₐ[ℚ] ℂ) × Bool) :=
  fixedSliceTraceAlgHomEquivFixedSlice.trans
    (even11FixedSliceTwoSheeted.trans
      (fixedSliceQuotientAlgHomEquivFixedSliceQuotient.symm.prodCongr
        (Equiv.refl Bool)))

/-- There are thirty-two complex algebra maps from the trace algebra. -/
theorem fixedSliceTraceAlgHom_natCard :
    Nat.card (FixedSliceTraceCoordinateAlgebra →ₐ[ℚ] ℂ) = 32 := by
  rw [Nat.card_congr fixedSliceTraceAlgHomEquivRoot]
  simpa only [Nat.card_eq_fintype_card] using fixedSliceTraceRoot_card_eq_32

/-- There are sixteen complex algebra maps from the quotient algebra. -/
theorem fixedSliceQuotientAlgHom_natCard :
    Nat.card (FixedSliceQuotientCoordinateAlgebra →ₐ[ℚ] ℂ) = 16 := by
  rw [Nat.card_congr fixedSliceQuotientAlgHomEquivRoot]
  simpa only [Nat.card_eq_fintype_card] using fixedSliceQuotientRoot_card

end

end Biunimodular.F11
