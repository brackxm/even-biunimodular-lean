/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceSchemeCoordinateAlgebra
import Biunimodular.F11.RedundantCoordinateAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Biunimodular.F11
noncomputable section

abbrev FixedSliceFivePolynomial := MvPolynomial (Fin 5) ℂ

/-- Interpret a trace-free sparse certificate in the five actual affine
coordinates, ordered `(x5,x4,x3,x2,x1)`. -/
def fixedSliceSparseMv5 (p : FixedSliceSparsePolynomial) : FixedSliceFivePolynomial :=
  (p.map fun t => MvPolynomial.C (fixedSliceAlphaEval t.coefficient) *
    MvPolynomial.X 0 ^ t.exponent.x5 * MvPolynomial.X 1 ^ t.exponent.x4 *
    MvPolynomial.X 2 ^ t.exponent.x3 * MvPolynomial.X 3 ^ t.exponent.x2 *
    MvPolynomial.X 4 ^ t.exponent.x1).sum

def fixedSliceSparseTraceFree (p : FixedSliceSparsePolynomial) : Prop :=
  ∀ a ∈ p, a.exponent.trace = 0

theorem fixedSliceSparseMv5_include (p : FixedSliceSparsePolynomial)
    (hp : fixedSliceSparseTraceFree p) :
    RedundantCoordinate.includeVariables (fixedSliceSparseMv5 p) = fixedSliceSparseMv p := by
  induction p with
  | nil => simp [fixedSliceSparseMv5, fixedSliceSparseMv]
  | cons a tail ih =>
    have ha := hp a (by simp)
    have htail : fixedSliceSparseTraceFree tail := fun b hb => hp b (by simp [hb])
    simpa [fixedSliceSparseMv5, fixedSliceSparseMv, RedundantCoordinate.includeVariables,
      ha] using (ih htail)

def fixedSliceFiveGenerators : List FixedSliceFivePolynomial :=
  [fixedSliceSparseMv5 fixedSliceOriginal1, fixedSliceSparseMv5 fixedSliceOriginal2,
   fixedSliceSparseMv5 fixedSliceOriginal3, fixedSliceSparseMv5 fixedSliceOriginal4,
   fixedSliceSparseMv5 fixedSliceOriginal5]

private theorem fixedSliceOriginalQuadrics_traceFree :
    ∀ p ∈ [fixedSliceOriginal1, fixedSliceOriginal2, fixedSliceOriginal3,
      fixedSliceOriginal4, fixedSliceOriginal5], fixedSliceSparseTraceFree p := by
  unfold fixedSliceSparseTraceFree
  native_decide

def fixedSliceFiveTracePolynomial : FixedSliceFivePolynomial :=
  1 + 2 * (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 +
    MvPolynomial.X 3 + MvPolynomial.X 4)

private theorem fixedSliceOriginalTrace_mv :
    fixedSliceSparseMv fixedSliceOriginal6 =
      MvPolynomial.X (Fin.last 5) -
        RedundantCoordinate.includeVariables fixedSliceFiveTracePolynomial := by
  norm_num [fixedSliceSparseMv, fixedSliceOriginal6, fixedSliceAlphaEval,
    RedundantCoordinate.includeVariables, fixedSliceFiveTracePolynomial,
    map_ofNat]
  change _ = MvPolynomial.X (5 : Fin 6) -
    (1 + 2 * (MvPolynomial.X (0 : Fin 6) + MvPolynomial.X (1 : Fin 6) +
      MvPolynomial.X (2 : Fin 6) + MvPolynomial.X (3 : Fin 6) + MvPolynomial.X (4 : Fin 6)))
  ring

/-- The original six equations are exactly the five quadrics with the
defining equation for the redundant trace appended. -/
theorem fixedSliceOriginalIdeal_eq_extendedFiveIdeal :
    fixedSliceSparseIdeal fixedSliceOriginalSystem =
      RedundantCoordinate.extendedIdeal fixedSliceFiveGenerators fixedSliceFiveTracePolynomial := by
  have h1 := fixedSliceSparseMv5_include fixedSliceOriginal1
    (fixedSliceOriginalQuadrics_traceFree _ (by simp))
  have h2 := fixedSliceSparseMv5_include fixedSliceOriginal2
    (fixedSliceOriginalQuadrics_traceFree _ (by simp))
  have h3 := fixedSliceSparseMv5_include fixedSliceOriginal3
    (fixedSliceOriginalQuadrics_traceFree _ (by simp))
  have h4 := fixedSliceSparseMv5_include fixedSliceOriginal4
    (fixedSliceOriginalQuadrics_traceFree _ (by simp))
  have h5 := fixedSliceSparseMv5_include fixedSliceOriginal5
    (fixedSliceOriginalQuadrics_traceFree _ (by simp))
  have hgenerators : fixedSliceOriginalSystem.map fixedSliceSparseMv =
      RedundantCoordinate.extendedGenerators fixedSliceFiveGenerators fixedSliceFiveTracePolynomial := by
    simp [fixedSliceOriginalSystem, RedundantCoordinate.extendedGenerators,
      fixedSliceFiveGenerators, h1, h2, h3, h4, h5, fixedSliceOriginalTrace_mv]
  unfold fixedSliceSparseIdeal RedundantCoordinate.extendedIdeal
  congr 1
  ext f
  rw [← hgenerators]
  simp only [Set.mem_ofPred_eq, List.mem_map]

/-- The actual five-quadric affine coordinate ring, without a trace variable. -/
abbrev FixedSliceFiveCoordinateAlgebra :=
  RedundantCoordinate.BaseAlgebra fixedSliceFiveGenerators

def fixedSliceSchemeCoordinateAlgebraEquivFive :
    FixedSliceSchemeCoordinateAlgebra ≃ₐ[ℂ] FixedSliceFiveCoordinateAlgebra :=
  (Ideal.quotientEquivAlgOfEq ℂ fixedSliceOriginalIdeal_eq_extendedFiveIdeal).trans
    (RedundantCoordinate.algebraEquiv fixedSliceFiveGenerators fixedSliceFiveTracePolynomial)

/-- Eliminating the redundant trace gives the same exact degree-32 algebra
for the original five affine quadrics. -/
def fixedSliceFiveCoordinateAlgebraEquivTrace :
    FixedSliceFiveCoordinateAlgebra ≃ₐ[ℂ] FixedSliceTraceComplexCoordinateAlgebra :=
  fixedSliceSchemeCoordinateAlgebraEquivFive.symm.trans
    fixedSliceSchemeCoordinateAlgebraEquivTrace

theorem fixedSliceFiveCoordinateAlgebra_finrank :
    Module.finrank ℂ FixedSliceFiveCoordinateAlgebra = 32 := by
  rw [fixedSliceFiveCoordinateAlgebraEquivTrace.toLinearEquiv.finrank_eq]
  exact fixedSliceTraceComplexCoordinateAlgebra_finrank

instance fixedSliceFiveCoordinateAlgebra_isReduced : IsReduced FixedSliceFiveCoordinateAlgebra :=
  isReduced_of_injective fixedSliceFiveCoordinateAlgebraEquivTrace.toRingHom
    fixedSliceFiveCoordinateAlgebraEquivTrace.injective

theorem fixedSliceFiveIdeal_isRadical :
    (RedundantCoordinate.baseIdeal fixedSliceFiveGenerators).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  infer_instance

end
end Biunimodular.F11
