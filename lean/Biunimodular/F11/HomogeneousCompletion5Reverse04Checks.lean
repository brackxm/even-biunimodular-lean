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

theorem homogeneousCompletion5_reverse_column3_check :
    rationalSparseZeroCheck (homogeneousCompletion5ReverseDen 3)
      (homogeneousCompletion5ReverseTerms 3) := by
  unfold rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
