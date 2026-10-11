/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5LeadingData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion5_leading_column4_check :
    rationalSparseLeadingCheck (homogeneousCompletion5G 4) (homogeneousCompletion5Leading 4) := by
  unfold rationalSparseLeadingCheck rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
