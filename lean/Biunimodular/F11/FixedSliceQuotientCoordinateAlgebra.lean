/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceQuotientPolynomial

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-!
# The reduced algebra of the quotient invariant

The polynomial `fixedSliceQuotientP16Q` is the exact spectrum of the concrete
Fourier quotient.  Its rational coordinate algebra is finite and reduced.
This result concerns the univariate invariant algebra; identifying it with
the coordinate ring of the projective quotient as a scheme is a separate
geometric statement.
-/

/-- The rational algebra cut out by the exact degree-sixteen invariant
polynomial. -/
abbrev FixedSliceQuotientCoordinateAlgebra :=
  ℚ[X] ⧸ Ideal.span {fixedSliceQuotientP16Q}

/-- The invariant coordinate algebra has degree sixteen over `ℚ`. -/
theorem fixedSliceQuotientCoordinateAlgebra_finrank :
    Module.finrank ℚ FixedSliceQuotientCoordinateAlgebra = 16 := by
  exact finrank_quotient_span_eq_natDegree.trans
    fixedSliceQuotientP16Q_natDegree

/-- The degree-sixteen invariant algebra has no nonzero nilpotents. -/
instance fixedSliceQuotientCoordinateAlgebra_isReduced :
    IsReduced FixedSliceQuotientCoordinateAlgebra := by
  change IsReduced (ℚ[X] ⧸ Ideal.span {fixedSliceQuotientP16Q})
  rw [← Ideal.isRadical_iff_quotient_reduced,
    ← isRadical_iff_span_singleton]
  exact (PerfectField.separable_iff_squarefree.mp
    fixedSliceQuotientP16Q_separable).isRadical

/-- The geometric invariant algebra after extending coefficients to `ℂ`. -/
abbrev FixedSliceQuotientComplexCoordinateAlgebra :=
  ℂ[X] ⧸ Ideal.span
    {fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)}

/-- The complex invariant algebra still has degree sixteen. -/
theorem fixedSliceQuotientComplexCoordinateAlgebra_finrank :
    Module.finrank ℂ FixedSliceQuotientComplexCoordinateAlgebra = 16 := by
  change Module.finrank ℂ (ℂ[X] ⧸ Ideal.span
    {fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)}) = 16
  rw [finrank_quotient_span_eq_natDegree,
    natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective]
  exact fixedSliceQuotientP16Q_natDegree

/-- All sixteen geometric invariant points are reduced. -/
instance fixedSliceQuotientComplexCoordinateAlgebra_isReduced :
    IsReduced FixedSliceQuotientComplexCoordinateAlgebra := by
  change IsReduced (ℂ[X] ⧸ Ideal.span
    {fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)})
  rw [← Ideal.isRadical_iff_quotient_reduced,
    ← isRadical_iff_span_singleton]
  exact (PerfectField.separable_iff_squarefree.mp
    fixedSliceQuotientP16Q_separable.map).isRadical

end Biunimodular.F11
