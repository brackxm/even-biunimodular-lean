/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceGeometryCertificate

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-!
# Reduced trace algebra of the concrete fixed slice

The exact trace-shape certificate identifies all thirty-two geometric points
with distinct roots of the degree-thirty-two trace polynomial.  Consequently
that polynomial is separable and its univariate coordinate algebra is reduced.
`FixedSliceSchemeCoordinateAlgebra` proves the algebra isomorphism with the
original multivariate affine fixed-slice ideal, preserving multiplicities.
-/

/-- The trace polynomial has thirty-two distinct complex roots. -/
theorem fixedSliceTraceRoot_card_eq_32 :
    Fintype.card FixedSliceTraceRoot = 32 := by
  let e : Even11FixedSlicePoint ≃ FixedSliceTraceRoot :=
    Equiv.ofBijective
      (even11FixedSliceTraceRootMap
        even11FixedSliceTraceGeometryCertificate.trace_isRoot)
      even11FixedSliceTraceGeometryCertificate.trace_bijective
  have hcard : Nat.card Even11FixedSlicePoint = 32 :=
    even11FixedSliceGeometryCertificate.cardinality_core.1
  have hroots : Nat.card FixedSliceTraceRoot = 32 := by
    rw [← Nat.card_congr e]
    exact hcard
  simpa only [Nat.card_eq_fintype_card] using hroots

/-- The exact degree-thirty-two trace eliminant is squarefree. -/
theorem fixedSliceTraceP32Q_separable :
    fixedSliceTraceP32Q.Separable := by
  apply (card_rootSet_eq_natDegree_iff_of_splits
    fixedSliceTraceP32Q_ne_zero
    (IsAlgClosed.splits
      (fixedSliceTraceP32Q.map (algebraMap ℚ ℂ)))).mp
  rw [fixedSliceTraceP32Q_natDegree]
  exact fixedSliceTraceRoot_card_eq_32

/-- The rational algebra cut out by the trace eliminant. -/
abbrev FixedSliceTraceCoordinateAlgebra :=
  ℚ[X] ⧸ Ideal.span {fixedSliceTraceP32Q}

theorem fixedSliceTraceCoordinateAlgebra_finrank :
    Module.finrank ℚ FixedSliceTraceCoordinateAlgebra = 32 := by
  exact finrank_quotient_span_eq_natDegree.trans
    fixedSliceTraceP32Q_natDegree

instance fixedSliceTraceCoordinateAlgebra_isReduced :
    IsReduced FixedSliceTraceCoordinateAlgebra := by
  change IsReduced (ℚ[X] ⧸ Ideal.span {fixedSliceTraceP32Q})
  rw [← Ideal.isRadical_iff_quotient_reduced,
    ← isRadical_iff_span_singleton]
  exact (PerfectField.separable_iff_squarefree.mp
    fixedSliceTraceP32Q_separable).isRadical

/-- The complex algebra cut out by the trace eliminant. -/
abbrev FixedSliceTraceComplexCoordinateAlgebra :=
  ℂ[X] ⧸ Ideal.span {fixedSliceTraceP32Q.map (algebraMap ℚ ℂ)}

theorem fixedSliceTraceComplexCoordinateAlgebra_finrank :
    Module.finrank ℂ FixedSliceTraceComplexCoordinateAlgebra = 32 := by
  change Module.finrank ℂ (ℂ[X] ⧸ Ideal.span
    {fixedSliceTraceP32Q.map (algebraMap ℚ ℂ)}) = 32
  rw [finrank_quotient_span_eq_natDegree,
    natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective]
  exact fixedSliceTraceP32Q_natDegree

instance fixedSliceTraceComplexCoordinateAlgebra_isReduced :
    IsReduced FixedSliceTraceComplexCoordinateAlgebra := by
  change IsReduced (ℂ[X] ⧸ Ideal.span
    {fixedSliceTraceP32Q.map (algebraMap ℚ ℂ)})
  rw [← Ideal.isRadical_iff_quotient_reduced,
    ← isRadical_iff_span_singleton]
  exact (PerfectField.separable_iff_squarefree.mp
    fixedSliceTraceP32Q_separable.map).isRadical

end Biunimodular.F11
