/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber1CertificateBlock042Check
import Biunimodular.F11.H252Fiber1CertificateBlock041Semantics

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
noncomputable section
theorem h252Fiber1CertificateBlock042_mem (I : Ideal (MvPolynomial (Fin 7) ℂ))
    (hbase : ∀ i, i < 11 → torusSparsePolynomial (h252Fiber1CertificateBasis i) ∈ I) :
    ∀ i, i < 53 → torusSparsePolynomial (h252Fiber1CertificateBasis i) ∈ I := by
  apply torusSparseStepBlock_mem I h252Fiber1CertificateBasis h252Fiber1CertificateSteps 52 53
    (h252Fiber1CertificateBlock041_mem I hbase)
  intro i hlo hhi
  let j : Fin 1 := ⟨i-52, by omega⟩
  have he : 52+j.val = i := by dsimp [j]; omega
  simpa only [he] using h252Fiber1CertificateBlock042_check j
end

end Biunimodular.F11
