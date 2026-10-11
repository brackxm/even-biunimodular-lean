/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion3BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion3_forward_check :
    ∀ j : Fin 7, rationalSparseZeroCheck (homogeneousCompletion3ForwardDen j)
      (homogeneousCompletion3ForwardTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion3_reverse_check :
    ∀ j : Fin 3, rationalSparseZeroCheck (homogeneousCompletion3ReverseDen j)
      (homogeneousCompletion3ReverseTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion3_residual_check :
    ∀ j : Fin 3, rationalSparseZeroCheck (homogeneousCompletion3ResidualDen j)
      (homogeneousCompletion3ResidualTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
