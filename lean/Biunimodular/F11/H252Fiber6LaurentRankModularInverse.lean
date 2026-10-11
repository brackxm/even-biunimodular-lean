/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6LaurentRankCheck

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

theorem h252Fiber6LaurentRank_modular_inverse :
    torusMacaulaySparseMatrix 1250 h252Fiber6LaurentRankRows (29 : ZMod 307) *
      torusMacaulayIntegerMatrix 1250 h252Fiber6LaurentRankInverse = 1 := by
  rw [h252Fiber6LaurentRank_reduced_matrix]
  exact torusMacaulayModularCheck_sound _ _ _ _ _ h252Fiber6LaurentRank_check

end Biunimodular.F11
