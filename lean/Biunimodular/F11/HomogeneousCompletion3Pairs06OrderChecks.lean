/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3Pairs06Data
import Biunimodular.F11.HomogeneousCompletion3LeadingChecks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion3Pair6_7L : FixedSliceSparseExponent := ⟨0, 1, 2, 1, 1, 0⟩

theorem homogeneousCompletion3Pair6_7_monomials_check :
    homogeneousCompletion3Pair6_7U = rationalSparseMonomial ⟨0, 0, 1, 0, 1, 0⟩ ∧
      homogeneousCompletion3Pair6_7V = rationalSparseMonomial ⟨0, 1, 0, 0, 0, 0⟩ := by
  native_decide

theorem homogeneousCompletion3Pair6_7_degree_bounds_check :
    ∀ k : Fin 7, ∀ t ∈ (homogeneousCompletion3Pair6_7D k).numerator,
      homogeneousExponentLT
        (fixedSliceSparseExponentMul t.exponent (homogeneousCompletion3Leading k)) homogeneousCompletion3Pair6_7L := by
  native_decide

end Biunimodular.F11
