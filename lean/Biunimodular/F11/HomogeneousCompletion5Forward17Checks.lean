/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion5_forward_column16_check :
    rationalSparseZeroCheck (homogeneousCompletion5ForwardDen 16)
      (homogeneousCompletion5ForwardTerms 16) := by
  unfold rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
