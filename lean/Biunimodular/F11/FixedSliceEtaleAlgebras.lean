/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceNormalizedAffineChart
import Biunimodular.F11.FixedSliceGeometricFunctionAlgebra
import Mathlib.RingTheory.Etale.Pi

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- The actual five-quadric algebra is finite etale over the complex numbers. -/
instance fixedSliceFiveCoordinateAlgebra_etale :
    Algebra.Etale ℂ FixedSliceFiveCoordinateAlgebra := by
  let e : Even11FixedSlicePoint ≃ FixedSliceTraceRoot :=
    Equiv.ofBijective
      (even11FixedSliceTraceRootMap even11FixedSliceTraceGeometryCertificate.trace_isRoot)
      even11FixedSliceTraceGeometryCertificate.trace_bijective
  let : Finite Even11FixedSlicePoint := Finite.of_equiv FixedSliceTraceRoot e.symm
  exact Algebra.Etale.of_equiv fixedSliceFiveAlgebraEquivFunctions.symm

/-- The normalized homogeneous equations give an etale affine chart. -/
instance fixedSliceNormalizedAffineChart_etale :
    Algebra.Etale ℂ FixedSliceNormalizedAffineChartAlgebra :=
  Algebra.Etale.of_equiv fixedSliceNormalizedAffineChartEquivFive.symm

instance fixedSliceQuotientComplexCoordinateAlgebra_etale :
    Algebra.Etale ℂ FixedSliceQuotientComplexCoordinateAlgebra := by
  let e : Even11FixedSliceFourierQuotient ≃ FixedSliceQuotientRoot :=
    even11FixedSliceGeometryCertificate.quotientRootEquiv
  let : Finite Even11FixedSliceFourierQuotient :=
    Finite.of_equiv FixedSliceQuotientRoot e.symm
  exact Algebra.Etale.of_equiv fixedSliceQuotientComplexAlgebraEquivFunctions.symm

end
end Biunimodular.F11
