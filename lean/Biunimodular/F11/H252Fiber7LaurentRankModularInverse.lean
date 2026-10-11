/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7LaurentRankCheck

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

theorem h252Fiber7LaurentRank_modular_inverse :
    torusMacaulaySparseMatrix 1250 h252Fiber7LaurentRankIntegralRows (140 : ZMod 353) *
      torusMacaulayIntegerMatrix 1250 h252Fiber7LaurentRankInverse = 1 := by
  rw [h252Fiber7LaurentRank_reduced_matrix]
  exact torusMacaulayModularCheck_sound _ _ _ _ _ h252Fiber7LaurentRank_check

end Biunimodular.F11
