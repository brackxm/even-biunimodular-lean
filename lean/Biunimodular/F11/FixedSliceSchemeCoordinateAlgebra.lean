/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceSchemeIdeal
import Biunimodular.F11.FixedSliceGraphAlgebra
import Biunimodular.F11.FixedSliceTraceCoordinateAlgebra

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

namespace Biunimodular.F11

open Polynomial
noncomputable section

/-- Univariate interpretation of a trace-only sparse polynomial. -/
def fixedSliceSparseTracePoly (p : FixedSliceSparsePolynomial) : ℂ[X] :=
  (p.map fun t => Polynomial.C (fixedSliceAlphaEval t.coefficient) *
    Polynomial.X ^ t.exponent.trace).sum

theorem fixedSliceSparseTracePoly_eval (p : FixedSliceSparsePolynomial)
    (hp : fixedSliceSparseTraceOnly p) (t : ℂ) :
    (fixedSliceSparseTracePoly p).eval t = fixedSliceSparseEval p 0 0 0 0 0 t := by
  induction p with
  | nil => simp [fixedSliceSparseTracePoly, fixedSliceSparseEval]
  | cons a tail ih =>
    obtain ⟨h5, h4, h3, h2, h1⟩ := hp a (by simp)
    have htail : fixedSliceSparseTraceOnly tail := fun b hb => hp b (by simp [hb])
    simpa [fixedSliceSparseTracePoly, fixedSliceSparseEval, fixedSliceSparseTermEval,
      h5, h4, h3, h2, h1] using congrArg
        (fun z : ℂ => fixedSliceAlphaEval a.coefficient * t ^ a.exponent.trace + z)
        (ih htail)

def fixedSliceShapeByVariable : Fin 5 → FixedSliceSparsePolynomial :=
  ![fixedSliceShape6, fixedSliceShape5, fixedSliceShape4, fixedSliceShape3, fixedSliceShape2]

def fixedSliceShapeTailByVariable : Fin 5 → FixedSliceSparsePolynomial :=
  ![fixedSliceShapeTail5, fixedSliceShapeTail4, fixedSliceShapeTail3,
    fixedSliceShapeTail2, fixedSliceShapeTail1]

def fixedSliceReconstructPoly (i : Fin 5) : ℂ[X] :=
  Polynomial.C (-(fixedSliceShapeCoordinateScale : ℂ)⁻¹) *
    fixedSliceSparseTracePoly (fixedSliceShapeTailByVariable i)

abbrev fixedSliceTraceComplexPolynomial := fixedSliceTraceP32Q.map (algebraMap ℚ ℂ)

private theorem fixedSliceShapeTailByVariable_traceOnly (i : Fin 5) :
    fixedSliceSparseTraceOnly (fixedSliceShapeTailByVariable i) := by
  fin_cases i
  · exact fixedSliceShapeTail5_traceOnly
  · exact fixedSliceShapeTail4_traceOnly
  · exact fixedSliceShapeTail3_traceOnly
  · exact fixedSliceShapeTail2_traceOnly
  · exact fixedSliceShapeTail1_traceOnly

private theorem fixedSliceShapeByVariable_eval (i : Fin 5) (x : Fin 6 → ℂ) :
    fixedSliceSparseEval (fixedSliceShapeByVariable i) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) =
      fixedSliceShapeCoordinateScale * x i.castSucc +
        fixedSliceSparseEval (fixedSliceShapeTailByVariable i) 0 0 0 0 0 (x 5) := by
  fin_cases i
  · exact fixedSliceShape6_eval _ _ _ _ _ _
  · exact fixedSliceShape5_eval _ _ _ _ _ _
  · exact fixedSliceShape4_eval _ _ _ _ _ _
  · exact fixedSliceShape3_eval _ _ _ _ _ _
  · exact fixedSliceShape2_eval _ _ _ _ _ _

private theorem fixedSliceShape1_mv :
    fixedSliceSparseMv fixedSliceShape1 =
      Polynomial.aeval (MvPolynomial.X 5) fixedSliceTraceComplexPolynomial := by
  apply MvPolynomial.funext
  intro x
  change (MvPolynomial.aeval x) _ = (MvPolynomial.aeval x) _
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  change MvPolynomial.eval x _ = _
  rw [fixedSliceSparseMv_eval, fixedSliceShape1_eval]
  change _ = Polynomial.aeval (x 5) (fixedSliceTraceP32Q.map (algebraMap ℚ ℂ))
  rw [fixedSliceTraceP32Q_map_complex]
  simp [Polynomial.aeval_def, Polynomial.eval₂_map]

private theorem fixedSliceShapeByVariable_mv (i : Fin 5) :
    fixedSliceSparseMv (fixedSliceShapeByVariable i) =
      MvPolynomial.C (fixedSliceShapeCoordinateScale : ℂ) *
        (MvPolynomial.X i.castSucc -
          Polynomial.aeval (MvPolynomial.X 5) (fixedSliceReconstructPoly i)) := by
  apply MvPolynomial.funext
  intro x
  change (MvPolynomial.aeval x) _ = (MvPolynomial.aeval x) _
  simp only [map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    ← Polynomial.aeval_algHom_apply]
  change MvPolynomial.eval x _ = _
  rw [fixedSliceSparseMv_eval, fixedSliceShapeByVariable_eval]
  simp only [fixedSliceReconstructPoly, map_mul, Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
    Polynomial.eval_C, RingHom.id_apply]
  rw [fixedSliceSparseTracePoly_eval _ (fixedSliceShapeTailByVariable_traceOnly i)]
  linear_combination
    -fixedSliceSparseEval (fixedSliceShapeTailByVariable i) 0 0 0 0 0 (x 5) *
      (mul_inv_cancel₀ fixedSliceShapeCoordinateScale_ne_zero)

private theorem traceGraph_relation_mem (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) (i : Fin 5) :
    MvPolynomial.X i.castSucc - Polynomial.aeval (MvPolynomial.X 5) (fs i) ∈
      traceGraphIdeal p fs := by
  apply Ideal.subset_span
  fin_cases i <;> simp [traceGraphGenerators]

private theorem fixedSliceShapeByVariable_mem (i : Fin 5) :
    fixedSliceShapeByVariable i ∈ fixedSliceShapeSystem := by
  fin_cases i <;> simp [fixedSliceShapeByVariable, fixedSliceShapeSystem]

/-- The triangular shape ideal is the graph of five univariate coordinate
polynomials over the degree-32 trace equation. -/
theorem fixedSliceShapeIdeal_eq_graphIdeal :
    fixedSliceSparseIdeal fixedSliceShapeSystem =
      traceGraphIdeal fixedSliceTraceComplexPolynomial fixedSliceReconstructPoly := by
  let I := traceGraphIdeal fixedSliceTraceComplexPolynomial fixedSliceReconstructPoly
  have htrace : fixedSliceSparseMv fixedSliceShape1 ∈ I := by
    rw [fixedSliceShape1_mv]
    exact Ideal.subset_span (by simp [traceGraphGenerators])
  have hvar : ∀ i : Fin 5, fixedSliceSparseMv (fixedSliceShapeByVariable i) ∈ I := by
    intro i
    rw [fixedSliceShapeByVariable_mv]
    exact I.mul_mem_left _ (traceGraph_relation_mem _ _ i)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨p, hp, rfl⟩
    simp only [fixedSliceShapeSystem, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact htrace
    · exact hvar 4
    · exact hvar 3
    · exact hvar 2
    · exact hvar 1
    · exact hvar 0
  · have htrace' : Polynomial.aeval (MvPolynomial.X 5) fixedSliceTraceComplexPolynomial ∈
        fixedSliceSparseIdeal fixedSliceShapeSystem := by
      rw [← fixedSliceShape1_mv]
      exact Ideal.subset_span ⟨_, by simp [fixedSliceShapeSystem], rfl⟩
    have hvar' : ∀ i : Fin 5,
        MvPolynomial.X i.castSucc - Polynomial.aeval (MvPolynomial.X 5) (fixedSliceReconstructPoly i) ∈
          fixedSliceSparseIdeal fixedSliceShapeSystem := by
      intro i
      have hm : fixedSliceSparseMv (fixedSliceShapeByVariable i) ∈
          fixedSliceSparseIdeal fixedSliceShapeSystem :=
        Ideal.subset_span ⟨_, fixedSliceShapeByVariable_mem i, rfl⟩
      rw [fixedSliceShapeByVariable_mv] at hm
      have hm' := (fixedSliceSparseIdeal fixedSliceShapeSystem).mul_mem_left
        (MvPolynomial.C (fixedSliceShapeCoordinateScale : ℂ)⁻¹) hm
      simpa only [← mul_assoc, ← MvPolynomial.C_mul,
        inv_mul_cancel₀ fixedSliceShapeCoordinateScale_ne_zero, MvPolynomial.C_1, one_mul] using hm'
    apply Ideal.span_le.mpr
    intro f hf
    simp only [traceGraphGenerators, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact htrace'
    · exact hvar' 0
    · exact hvar' 1
    · exact hvar' 2
    · exact hvar' 3
    · exact hvar' 4

/-- The multivariate coordinate ring of the original affine fixed slice,
with its redundant trace coordinate. -/
abbrev FixedSliceSchemeCoordinateAlgebra :=
  FixedSliceAffinePolynomial ⧸ fixedSliceSparseIdeal fixedSliceOriginalSystem

/-- The original quadric ideal has the degree-32 trace algebra as its actual
coordinate ring; this is an algebra isomorphism, not merely a point bijection. -/
def fixedSliceSchemeCoordinateAlgebraEquivTrace :
    FixedSliceSchemeCoordinateAlgebra ≃ₐ[ℂ] FixedSliceTraceComplexCoordinateAlgebra :=
  (Ideal.quotientEquivAlgOfEq ℂ
    (fixedSliceOriginalIdeal_eq_shapeIdeal.trans fixedSliceShapeIdeal_eq_graphIdeal)).trans
    (traceGraphAlgebraEquivRoot fixedSliceTraceComplexPolynomial fixedSliceReconstructPoly)

theorem fixedSliceSchemeCoordinateAlgebra_finrank :
    Module.finrank ℂ FixedSliceSchemeCoordinateAlgebra = 32 := by
  rw [fixedSliceSchemeCoordinateAlgebraEquivTrace.toLinearEquiv.finrank_eq]
  exact fixedSliceTraceComplexCoordinateAlgebra_finrank

instance fixedSliceSchemeCoordinateAlgebra_isReduced :
    IsReduced FixedSliceSchemeCoordinateAlgebra :=
  isReduced_of_injective fixedSliceSchemeCoordinateAlgebraEquivTrace.toRingHom
    fixedSliceSchemeCoordinateAlgebraEquivTrace.injective

theorem fixedSliceOriginalIdeal_isRadical :
    (fixedSliceSparseIdeal fixedSliceOriginalSystem).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  infer_instance

end
end Biunimodular.F11
