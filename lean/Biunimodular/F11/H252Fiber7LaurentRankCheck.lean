/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7LaurentRankReductionCheck

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

theorem h252Fiber7LaurentRank_check :
    torusMacaulayModularCheck 1250 353 140 h252Fiber7LaurentRankReducedRows h252Fiber7LaurentRankInverse := by native_decide

end Biunimodular.F11
