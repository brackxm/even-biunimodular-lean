/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber2LaurentRankCheck

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

theorem h252Fiber2LaurentRank_modular_inverse :
    torusMacaulaySparseMatrix 1250 h252Fiber2LaurentRankRows (3088 : ZMod 6007) *
      torusMacaulayIntegerMatrix 1250 h252Fiber2LaurentRankInverse = 1 :=
  torusMacaulayModularCheck_sound _ _ _ _ _ h252Fiber2LaurentRank_check

end Biunimodular.F11
