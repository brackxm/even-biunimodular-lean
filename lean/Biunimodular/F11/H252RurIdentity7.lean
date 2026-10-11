/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurInputData
import Biunimodular.F11.H252RurQ7Data

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

set_option maxHeartbeats 0

def h252RurP7Coeffs : List ℤ :=
  [integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN6Coeffs)) (h252RurN1Coeffs)) (h252RurN2Coeffs)) (h252RurN3Coeffs)) (h252RurN4Coeffs)) (h252RurN5Coeffs),
    integerCoefficientScale (-1) (integerCoefficientPow (h252RurDCoeffs) 6)].foldr integerCoefficientAdd []

theorem h252RurIdentity7_coefficients :
    integerCoefficientEqual
      (integerCoefficientScale (h252RurQ7Den) (h252RurP7Coeffs))
      (integerCoefficientScale (h252RurCommonDen ^ 5) (integerCoefficientMul (h252RurQ7Coeffs) (h252RurHCoeffs))) = true := by
  native_decide

end Biunimodular.F11
