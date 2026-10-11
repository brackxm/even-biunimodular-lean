/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceChartDimension
import Mathlib.RingTheory.Regular.RegularSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section
open Polynomial
open scoped Pointwise

/-- An explicit regular hypersurface presentation of the actual affine chart. -/
def fixedSliceNormalizedAffineChartEquivTrace :
    FixedSliceNormalizedAffineChartAlgebra ≃ₐ[ℂ]
      (ℂ[X] ⧸ Ideal.span {fixedSliceTraceComplexPolynomial}) :=
  fixedSliceNormalizedAffineChartEquivFive.trans fixedSliceFiveCoordinateAlgebraEquivTrace

theorem fixedSliceTraceComplexPolynomial_regular_sequence :
    RingTheory.Sequence.IsRegular ℂ[X] [fixedSliceTraceComplexPolynomial] := by
  let R := ℂ[X]
  let p : R := fixedSliceTraceComplexPolynomial
  let : Nontrivial (R ⧸ Ideal.span {p}) :=
    fixedSliceNormalizedAffineChartEquivTrace.symm.toEquiv.nontrivial
  have hs : (p • (⊤ : Submodule R R)) = (Ideal.span {p} : Submodule R R) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
    simp
  let : Nontrivial (QuotSMulTop p R) := by
    change Nontrivial (R ⧸ (p • (⊤ : Submodule R R)))
    rw [hs]
    infer_instance
  apply (RingTheory.Sequence.isRegular_cons_iff R p []).mpr
  constructor
  · apply IsLeftRegular.isSMulRegular
    exact (isRegular_iff_ne_zero.mpr
      (fixedSliceTraceP32Q_separable.map.ne_zero)).left
  · exact RingTheory.Sequence.IsRegular.nil R _

/-- The chart admits a polynomial presentation by a regular sequence.
This establishes an affine complete-intersection presentation; the global
five-quadric projective regular-sequence assertion is a separate statement. -/
theorem fixedSliceNormalizedAffineChart_regular_presentation :
    ∃ p : ℂ[X], RingTheory.Sequence.IsRegular ℂ[X] [p] ∧
      Nonempty (FixedSliceNormalizedAffineChartAlgebra ≃ₐ[ℂ]
        (ℂ[X] ⧸ Ideal.span {p})) :=
  ⟨fixedSliceTraceComplexPolynomial, fixedSliceTraceComplexPolynomial_regular_sequence,
    ⟨fixedSliceNormalizedAffineChartEquivTrace⟩⟩

end
end Biunimodular.F11
