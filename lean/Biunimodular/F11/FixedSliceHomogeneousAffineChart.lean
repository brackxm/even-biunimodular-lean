/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceHomogeneousDegree
import Biunimodular.F11.FixedSliceFiveCoordinateAlgebra
import Biunimodular.F11.Even11FixedSliceGeometryCertificate

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

/-- Set `h₀ = 1`, retaining the certificate's reversed affine coordinate order. -/
def fixedSliceHomogeneousAffineMap :
    MvPolynomial (Fin 6) ℂ →ₐ[ℂ] FixedSliceFivePolynomial :=
  aeval (Fin.cases 1 (fun i : Fin 5 => X i.rev))

theorem fixedSliceSparseMv5_eval (p : FixedSliceSparsePolynomial) (x : Fin 5 → ℂ) :
    aeval x (fixedSliceSparseMv5 p) =
      fixedSliceSparseEval p (x 0) (x 1) (x 2) (x 3) (x 4) 1 := by
  induction p with
  | nil => simp [fixedSliceSparseMv5, fixedSliceSparseEval]
  | cons a tail ih =>
    simpa [fixedSliceSparseMv5, fixedSliceSparseEval, fixedSliceSparseTermEval]
      using congrArg (fun z : ℂ =>
        fixedSliceAlphaEval a.coefficient * x 0 ^ a.exponent.x5 *
          x 1 ^ a.exponent.x4 * x 2 ^ a.exponent.x3 * x 3 ^ a.exponent.x2 *
          x 4 ^ a.exponent.x1 + z) ih

theorem fixedSliceHomogeneousAffineMap_eval (x : Fin 5 → ℂ)
    (p : MvPolynomial (Fin 6) ℂ) :
    aeval x (fixedSliceHomogeneousAffineMap p) =
      aeval (even11FixedSliceAffineVector (x 4) (x 3) (x 2) (x 1) (x 0)) p := by
  rw [fixedSliceHomogeneousAffineMap, comp_aeval_apply]
  have hv : (fun i : Fin 6 => aeval x
      (Fin.cases (1 : FixedSliceFivePolynomial) (fun i : Fin 5 => X i.rev) i)) =
      even11FixedSliceAffineVector (x 4) (x 3) (x 2) (x 1) (x 0) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [even11FixedSliceAffineVector]
    · simp only [Fin.cases_succ, aeval_X]
      fin_cases i <;> rfl
  rw [hv]

/-- Dehomogenization gives exactly the five original certified quadrics,
as polynomials, including their coefficient normalization and variable order. -/
theorem fixedSliceHomogeneousAffineGenerators_eq :
    (fixedSliceHomogeneousGenerators even11Fourier).map fixedSliceHomogeneousAffineMap =
      fixedSliceFiveGenerators := by
  simp only [fixedSliceHomogeneousGenerators, List.ofFn_succ, List.ofFn_zero,
    List.map_cons, List.map_nil, fixedSliceFiveGenerators]
  simp only [List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, True.intro⟩
  all_goals apply MvPolynomial.funext
  all_goals intro x
  all_goals change aeval x _ = aeval x _
  all_goals rw [fixedSliceHomogeneousAffineMap_eval,
    fixedSliceHomogeneousQuadric_eval, fixedSliceSparseMv5_eval]
  all_goals simp only [fourierCoordProduct]
  all_goals rw [show even11Fourier
      (even11FixedSliceAffineVector (x 4) (x 3) (x 2) (x 1) (x 0)) =
        even11FixedSliceAffineFourier (x 4) (x 3) (x 2) (x 1) (x 0) from
      even11Fourier_affine_apply _ _ _ _ _]
  all_goals norm_num [fourierCoordProduct, even11FixedSliceAffineVector,
    even11FixedSliceAffineFourier, fixedSliceOriginal1, fixedSliceOriginal2,
    fixedSliceOriginal3, fixedSliceOriginal4, fixedSliceOriginal5,
    fixedSliceSparseEval, fixedSliceSparseTermEval, fixedSliceAlphaEval]
  all_goals ring_nf

/-- The dehomogenized ring of the actual homogeneous Fourier equations. -/
abbrev FixedSliceHomogeneousAffineChartAlgebra :=
  RedundantCoordinate.BaseAlgebra
    ((fixedSliceHomogeneousGenerators even11Fourier).map fixedSliceHomogeneousAffineMap)

theorem fixedSliceHomogeneousAffineChart_finrank :
    Module.finrank ℂ FixedSliceHomogeneousAffineChartAlgebra = 32 := by
  unfold FixedSliceHomogeneousAffineChartAlgebra
  rw [fixedSliceHomogeneousAffineGenerators_eq]
  exact fixedSliceFiveCoordinateAlgebra_finrank

instance fixedSliceHomogeneousAffineChart_isReduced :
    IsReduced FixedSliceHomogeneousAffineChartAlgebra := by
  unfold FixedSliceHomogeneousAffineChartAlgebra
  rw [fixedSliceHomogeneousAffineGenerators_eq]
  infer_instance

end
end Biunimodular.F11
