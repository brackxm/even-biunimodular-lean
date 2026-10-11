/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion1BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion1_forward_check :
    ∀ j : Fin 1, rationalSparseZeroCheck (homogeneousCompletion1ForwardDen j)
      (homogeneousCompletion1ForwardTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion1_reverse_check :
    ∀ j : Fin 1, rationalSparseZeroCheck (homogeneousCompletion1ReverseDen j)
      (homogeneousCompletion1ReverseTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion1_residual_check :
    ∀ j : Fin 1, rationalSparseZeroCheck (homogeneousCompletion1ResidualDen j)
      (homogeneousCompletion1ResidualTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
