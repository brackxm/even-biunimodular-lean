/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6LaurentRankData
import Biunimodular.F11.H252Fiber6LaurentRankRelationsData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber6LaurentRank_transpose_check :
    torusMacaulayTransposeCheck 1250 h252Fiber6LaurentRankRows h252Fiber6LaurentRankColumns := by native_decide

end Biunimodular.F11
