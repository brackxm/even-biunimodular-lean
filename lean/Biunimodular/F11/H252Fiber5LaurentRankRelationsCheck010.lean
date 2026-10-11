/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber5LaurentRankRelationsParents

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber5LaurentRank_original_check010 : ∀ j : Fin 125,
    torusMacaulayColumnZeroCheck h252Fiber5LaurentRankColumns h252Fiber5LaurentRankMonomials h252Fiber5LaurentRankConstants
      h252Fiber5LaurentRankGlobal (h252Fiber5LaurentRankOriginalParents[1125+j.val]?.getD []) (1125+j.val) := by native_decide

end Biunimodular.F11
