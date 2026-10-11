/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber2LaurentRankModularInverse
import Biunimodular.F11.GaussianFiberCoefficientField

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

noncomputable section
theorem h252Fiber2LaurentRank_det_isUnit :
    IsUnit (torusMacaulaySparseMatrix 1250 h252Fiber2LaurentRankRows
      (AdjoinRoot.root gaussianFiberRationalPolynomial)).det := by
  apply isUnit_iff_ne_zero.mpr
  have h := torusMacaulay_det_ne_zero_of_reduction gaussianFiberIntegralEmbedding
    gaussianFiberModularReduction gaussianFiberIntegralEmbedding_injective
    (torusMacaulaySparseMatrix 1250 h252Fiber2LaurentRankRows
      (AdjoinRoot.root gaussianFiberIntegerPolynomial))
    (torusMacaulayIntegerMatrix 1250 h252Fiber2LaurentRankInverse)
    (by
      rw [torusMacaulaySparseMatrix_map, gaussianFiberModularReduction_root]
      exact h252Fiber2LaurentRank_modular_inverse)
  simpa only [torusMacaulaySparseMatrix_map, gaussianFiberIntegralEmbedding_root] using h

theorem h252Fiber2LaurentRank_det_isUnit_of_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a [1,1,1,1,1,1,1,1,1,1,1] = 0) :
    IsUnit (torusMacaulaySparseMatrix 1250 h252Fiber2LaurentRankRows a).det := by
  have hu := h252Fiber2LaurentRank_det_isUnit.map (gaussianFiberRationalRootHom a h)
  rw [RingHom.map_det, torusMacaulaySparseMatrix_map, gaussianFiberRationalRootHom_root] at hu
  exact hu
end

end Biunimodular.F11
