/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs27Data
import Biunimodular.F11.HomogeneousCompletion4LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair14_15L : FixedSliceSparseExponent := ⟨0, 0, 3, 4, 1, 0⟩

theorem homogeneousCompletion4Pair14_15_monomials_check :
    homogeneousCompletion4Pair14_15U = rationalSparseMonomial ⟨0, 0, 0, 3, 1, 0⟩ ∧
      homogeneousCompletion4Pair14_15V = rationalSparseMonomial ⟨0, 0, 3, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion4Pair14_15_degree_bounds_check :
    ∀ k : Fin 15, ∀ t ∈ (homogeneousCompletion4Pair14_15D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion4Leading k)) homogeneousCompletion4Pair14_15L := by
  native_decide

end Biunimodular.F11
