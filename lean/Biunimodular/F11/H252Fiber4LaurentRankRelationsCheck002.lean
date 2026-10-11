/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4LaurentRankRelationsParents

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber4LaurentRank_original_check002 : ∀ j : Fin 125,
    torusMacaulayColumnZeroCheck h252Fiber4LaurentRankColumns h252Fiber4LaurentRankMonomials h252Fiber4LaurentRankConstants
      h252Fiber4LaurentRankGlobal (h252Fiber4LaurentRankOriginalParents[125+j.val]?.getD []) (125+j.val) := by native_decide

end Biunimodular.F11
