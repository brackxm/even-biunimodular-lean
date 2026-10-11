/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4Pairs27Data

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion4Pair14_15_sp_check :
    rationalSparseZeroCheck 844841178746628601604489567 homogeneousCompletion4Pair14_15SPTerms := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion4Pair14_15_last_check :
    rationalSparseZeroCheck 9293252966212914617649385237 homogeneousCompletion4Pair14_15LastTerms := by
  unfold rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
