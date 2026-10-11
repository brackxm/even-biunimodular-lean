/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7LaurentRankData
import Biunimodular.F11.TorusMacaulayRootScaling
import Biunimodular.F11.H252Fiber7MonicTransform

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0
theorem h252Fiber7LaurentRank_root_scaling_check :
    torusMacaulayRootScalingCheck 1250 h252Fiber7RootScale 79 h252Fiber7LaurentRankRows h252Fiber7LaurentRankIntegralRows := by native_decide
theorem h252Fiber7LaurentRank_root_scaling {R : Type*} [CommRing R] (a : R) :
    torusMacaulaySparseMatrix 1250 h252Fiber7LaurentRankIntegralRows ((h252Fiber7RootScale : R)*a) =
      (h252Fiber7RootScale : R)^79 • torusMacaulaySparseMatrix 1250 h252Fiber7LaurentRankRows a :=
  torusMacaulayRootScalingCheck_sound _ _ _ _ _ h252Fiber7LaurentRank_root_scaling_check a

end Biunimodular.F11
