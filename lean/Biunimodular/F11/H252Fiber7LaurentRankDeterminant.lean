/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7LaurentRankModularInverse
import Biunimodular.F11.H252Fiber7LaurentRankRootScalingCheck
import Biunimodular.F11.H252Fiber7CoefficientField

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

noncomputable section
theorem h252Fiber7LaurentRank_det_isUnit :
    IsUnit (torusMacaulaySparseMatrix 1250 h252Fiber7LaurentRankIntegralRows
      (AdjoinRoot.root h252Fiber7PolynomialQ)).det := by
  apply isUnit_iff_ne_zero.mpr
  have h := torusMacaulay_det_ne_zero_of_reduction h252Fiber7IntegralEmbedding
    h252Fiber7ModularReduction h252Fiber7IntegralEmbedding_injective
    (torusMacaulaySparseMatrix 1250 h252Fiber7LaurentRankIntegralRows (AdjoinRoot.root h252Fiber7PolynomialZ))
    (torusMacaulayIntegerMatrix 1250 h252Fiber7LaurentRankInverse)
    (by rw [torusMacaulaySparseMatrix_map, h252Fiber7ModularReduction_root]
        exact h252Fiber7LaurentRank_modular_inverse)
  simpa only [torusMacaulaySparseMatrix_map, h252Fiber7IntegralEmbedding_root] using h
theorem h252Fiber7LaurentRank_det_isUnit_of_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ7 = 0) :
    IsUnit (torusMacaulaySparseMatrix 1250 h252Fiber7LaurentRankRows a).det := by
  have hu := h252Fiber7LaurentRank_det_isUnit.map (h252Fiber7OriginalRootHom a h)
  rw [RingHom.map_det, torusMacaulaySparseMatrix_map, h252Fiber7OriginalRootHom_root,
    h252Fiber7LaurentRank_root_scaling, Matrix.det_smul] at hu
  exact isUnit_of_mul_isUnit_right hu
end

end Biunimodular.F11
