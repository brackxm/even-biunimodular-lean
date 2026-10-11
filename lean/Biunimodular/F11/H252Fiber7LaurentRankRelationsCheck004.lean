/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7LaurentRankRelationsParents

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber7LaurentRank_original_check004 : ∀ j : Fin 125,
    torusMacaulayColumnZeroCheck h252Fiber7LaurentRankColumns h252Fiber7LaurentRankMonomials h252Fiber7LaurentRankConstants
      h252Fiber7LaurentRankGlobal (h252Fiber7LaurentRankOriginalParents[375+j.val]?.getD []) (375+j.val) := by native_decide

end Biunimodular.F11
