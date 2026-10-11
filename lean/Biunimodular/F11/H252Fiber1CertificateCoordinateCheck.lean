/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber1CertificateData
import Biunimodular.F11.TorusFiberLinearCertificate

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def h252Fiber1CertificateCoordinateIndices : Fin 9 → ℕ := ![59, 58, 57, 56, 55, 54, 53, 52, 51]

def h252Fiber1CertificateCoordinateScales : Fin 9 → ℤ := ![1, 1, 1, 1, 1, 1, 1, 1, 1]

def h252Fiber1CertificateCoordinateRemainders : Fin 9 → List ℤ := ![[0, -1], [0, -1], [0, -1], [0, -1], [9, 1], [9, 1], [9, 1], [9, 1], [9, 1]]

theorem h252Fiber1CertificateCoordinate_bounds : ∀ i, h252Fiber1CertificateCoordinateIndices i < 60 := by native_decide

theorem h252Fiber1CertificateCoordinate_positive : ∀ i, 0 < h252Fiber1CertificateCoordinateScales i := by native_decide

theorem h252Fiber1CertificateCoordinate_check : ∀ i,
    torusFiberLinearCheck (h252Fiber1CertificateBasis (h252Fiber1CertificateCoordinateIndices i)) (torusFiberCoordinates i)
      (h252Fiber1CertificateCoordinateRemainders i) (h252Fiber1CertificateCoordinateScales i) := by native_decide

end Biunimodular.F11
