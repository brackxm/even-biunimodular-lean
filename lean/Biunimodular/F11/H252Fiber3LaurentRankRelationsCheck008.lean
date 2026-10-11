/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3LaurentRankRelationsParents

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber3LaurentRank_original_check008 : ∀ j : Fin 125,
    torusMacaulayColumnZeroCheck h252Fiber3LaurentRankColumns h252Fiber3LaurentRankMonomials h252Fiber3LaurentRankConstants
      h252Fiber3LaurentRankGlobal (h252Fiber3LaurentRankOriginalParents[875+j.val]?.getD []) (875+j.val) := by native_decide

end Biunimodular.F11
