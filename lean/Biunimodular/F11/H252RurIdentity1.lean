/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurInputData
import Biunimodular.F11.H252RurQ1Data

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

set_option maxHeartbeats 0

def h252RurP1Coeffs : List ℤ :=
  [integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN1Coeffs)) (h252RurN2Coeffs)) (h252RurN3Coeffs)) (h252RurN4Coeffs)) (h252RurN5Coeffs)) (h252RurDCoeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (integerCoefficientPow (h252RurN1Coeffs) 2)) (h252RurN2Coeffs)) (h252RurN3Coeffs)) (h252RurN4Coeffs)) (h252RurN5Coeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN2Coeffs)) (h252RurN3Coeffs)) (h252RurN4Coeffs)) (h252RurN5Coeffs)) (integerCoefficientPow (h252RurDCoeffs) 2)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (integerCoefficientPow (h252RurN1Coeffs) 2)) (h252RurN3Coeffs)) (h252RurN4Coeffs)) (h252RurN5Coeffs)) (h252RurDCoeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (integerCoefficientPow (h252RurN2Coeffs) 2)) (h252RurN3Coeffs)) (h252RurN4Coeffs)) (h252RurN5Coeffs)) (h252RurDCoeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN1Coeffs)) (integerCoefficientPow (h252RurN2Coeffs) 2)) (h252RurN4Coeffs)) (h252RurN5Coeffs)) (h252RurDCoeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN1Coeffs)) (integerCoefficientPow (h252RurN3Coeffs) 2)) (h252RurN4Coeffs)) (h252RurN5Coeffs)) (h252RurDCoeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN1Coeffs)) (h252RurN2Coeffs)) (integerCoefficientPow (h252RurN3Coeffs) 2)) (h252RurN5Coeffs)) (h252RurDCoeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN1Coeffs)) (h252RurN2Coeffs)) (integerCoefficientPow (h252RurN4Coeffs) 2)) (h252RurN5Coeffs)) (h252RurDCoeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN1Coeffs)) (h252RurN2Coeffs)) (h252RurN3Coeffs)) (integerCoefficientPow (h252RurN4Coeffs) 2)) (h252RurDCoeffs)),
    integerCoefficientScale (1) (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul (integerCoefficientMul ([1]) (h252RurN1Coeffs)) (h252RurN2Coeffs)) (h252RurN3Coeffs)) (integerCoefficientPow (h252RurN5Coeffs) 2)) (h252RurDCoeffs))].foldr integerCoefficientAdd []

theorem h252RurIdentity1_coefficients :
    integerCoefficientEqual
      (integerCoefficientScale (h252RurQ1Den) (h252RurP1Coeffs))
      (integerCoefficientScale (h252RurCommonDen ^ 5) (integerCoefficientMul (h252RurQ1Coeffs) (h252RurHCoeffs))) = true := by
  native_decide

end Biunimodular.F11
