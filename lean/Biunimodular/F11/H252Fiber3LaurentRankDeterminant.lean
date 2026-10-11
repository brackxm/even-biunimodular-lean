/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3LaurentRankModularInverse
import Biunimodular.F11.H252Fiber3CoefficientField

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

noncomputable section
theorem h252Fiber3LaurentRank_det_isUnit :
    IsUnit (torusMacaulaySparseMatrix 1250 h252Fiber3LaurentRankRows
      (AdjoinRoot.root h252Fiber3PolynomialQ)).det := by
  apply isUnit_iff_ne_zero.mpr
  have h := torusMacaulay_det_ne_zero_of_reduction h252Fiber3IntegralEmbedding
    h252Fiber3ModularReduction h252Fiber3IntegralEmbedding_injective
    (torusMacaulaySparseMatrix 1250 h252Fiber3LaurentRankRows
      (AdjoinRoot.root h252Fiber3PolynomialZ))
    (torusMacaulayIntegerMatrix 1250 h252Fiber3LaurentRankInverse)
    (by
      rw [torusMacaulaySparseMatrix_map, h252Fiber3ModularReduction_root]
      exact h252Fiber3LaurentRank_modular_inverse)
  simpa only [torusMacaulaySparseMatrix_map, h252Fiber3IntegralEmbedding_root] using h

theorem h252Fiber3LaurentRank_det_isUnit_of_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ3 = 0) :
    IsUnit (torusMacaulaySparseMatrix 1250 h252Fiber3LaurentRankRows a).det := by
  have hu := h252Fiber3LaurentRank_det_isUnit.map (h252Fiber3RationalRootHom a h)
  rw [RingHom.map_det, torusMacaulaySparseMatrix_map, h252Fiber3RationalRootHom_root] at hu
  exact hu
end

end Biunimodular.F11
