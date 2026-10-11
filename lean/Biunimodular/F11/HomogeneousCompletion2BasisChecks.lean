/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion2BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion2_forward_check :
    ∀ j : Fin 3, rationalSparseZeroCheck (homogeneousCompletion2ForwardDen j)
      (homogeneousCompletion2ForwardTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion2_reverse_check :
    ∀ j : Fin 2, rationalSparseZeroCheck (homogeneousCompletion2ReverseDen j)
      (homogeneousCompletion2ReverseTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion2_residual_check :
    ∀ j : Fin 2, rationalSparseZeroCheck (homogeneousCompletion2ResidualDen j)
      (homogeneousCompletion2ResidualTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
