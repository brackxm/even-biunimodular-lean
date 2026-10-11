/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3LaurentRankCheck

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

theorem h252Fiber3LaurentRank_modular_inverse :
    torusMacaulaySparseMatrix 1250 h252Fiber3LaurentRankRows (6 : ZMod 103) *
      torusMacaulayIntegerMatrix 1250 h252Fiber3LaurentRankInverse = 1 :=
  torusMacaulayModularCheck_sound _ _ _ _ _ h252Fiber3LaurentRank_check

end Biunimodular.F11
