/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber2LaurentRankRelationsParents

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

theorem h252Fiber2LaurentRank_original_check004 : ∀ j : Fin 125,
    torusMacaulayColumnZeroCheck h252Fiber2LaurentRankColumns h252Fiber2LaurentRankMonomials h252Fiber2LaurentRankConstants
      h252Fiber2LaurentRankGlobal (h252Fiber2LaurentRankOriginalParents[375+j.val]?.getD []) (375+j.val) := by native_decide

theorem h252Fiber2LaurentRank_point_check004 : ∀ j : Fin 125,
    torusMacaulayColumnZeroCheck h252Fiber2LaurentRankColumns h252Fiber2LaurentRankPoints h252Fiber2LaurentRankConstants
      rurInverseSparseOne (h252Fiber2LaurentRankPointParents[375+j.val]?.getD []) (375+j.val) := by native_decide

end Biunimodular.F11
