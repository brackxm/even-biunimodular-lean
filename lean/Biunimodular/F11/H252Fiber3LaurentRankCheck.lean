/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3LaurentRankData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

theorem h252Fiber3LaurentRank_check :
    torusMacaulayModularCheck 1250 103 6
      h252Fiber3LaurentRankRows h252Fiber3LaurentRankInverse := by native_decide

end Biunimodular.F11
