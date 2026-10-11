/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurInputData
import Biunimodular.F11.H252RurQ6Data

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

set_option maxHeartbeats 0

def h252RurP6Coeffs : List ℤ :=
  [integerCoefficientPow (h252RurN5Coeffs) 2,
    integerCoefficientScale (-2) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) ([0,1])) (h252RurN5Coeffs)) (h252RurDCoeffs)),
    integerCoefficientScale (-1) (integerCoefficientPow (h252RurDCoeffs) 2)].foldr integerCoefficientAdd []

theorem h252RurIdentity6_coefficients :
    integerCoefficientEqual
      (integerCoefficientScale (h252RurQ6Den) (h252RurP6Coeffs))
      (integerCoefficientScale (h252RurCommonDen ^ 1) (integerCoefficientMul (h252RurQ6Coeffs) (h252RurHCoeffs))) = true := by
  native_decide

end Biunimodular.F11
