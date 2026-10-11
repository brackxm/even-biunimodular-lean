/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber1CertificateBlock038Check
import Biunimodular.F11.H252Fiber1CertificateBlock037Semantics

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
noncomputable section
theorem h252Fiber1CertificateBlock038_mem (I : Ideal (MvPolynomial (Fin 7) ℂ))
    (hbase : ∀ i, i < 11 → torusSparsePolynomial (h252Fiber1CertificateBasis i) ∈ I) :
    ∀ i, i < 49 → torusSparsePolynomial (h252Fiber1CertificateBasis i) ∈ I := by
  apply torusSparseStepBlock_mem I h252Fiber1CertificateBasis h252Fiber1CertificateSteps 48 49
    (h252Fiber1CertificateBlock037_mem I hbase)
  intro i hlo hhi
  let j : Fin 1 := ⟨i-48, by omega⟩
  have he : 48+j.val = i := by dsimp [j]; omega
  simpa only [he] using h252Fiber1CertificateBlock038_check j
end

end Biunimodular.F11
