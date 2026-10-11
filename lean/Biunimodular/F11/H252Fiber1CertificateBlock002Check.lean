/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber1CertificateData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
theorem h252Fiber1CertificateBlock002_check : ∀ j : Fin 1,
    torusSparseStepCheck h252Fiber1CertificateBasis (12+j.val) (h252Fiber1CertificateSteps (12+j.val)) := by native_decide

end Biunimodular.F11
