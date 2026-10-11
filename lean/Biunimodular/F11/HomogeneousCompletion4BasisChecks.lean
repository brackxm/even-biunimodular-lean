/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion4_forward_check :
    ∀ j : Fin 15, rationalSparseZeroCheck (homogeneousCompletion4ForwardDen j)
      (homogeneousCompletion4ForwardTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion4_reverse_check :
    ∀ j : Fin 4, rationalSparseZeroCheck (homogeneousCompletion4ReverseDen j)
      (homogeneousCompletion4ReverseTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion4_residual_check :
    ∀ j : Fin 4, rationalSparseZeroCheck (homogeneousCompletion4ResidualDen j)
      (homogeneousCompletion4ResidualTerms j) := by
  unfold rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
