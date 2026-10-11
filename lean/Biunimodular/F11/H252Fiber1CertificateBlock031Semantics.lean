/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber1CertificateBlock031Check
import Biunimodular.F11.H252Fiber1CertificateBlock030Semantics

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
noncomputable section
theorem h252Fiber1CertificateBlock031_mem (I : Ideal (MvPolynomial (Fin 7) ℂ))
    (hbase : ∀ i, i < 11 → torusSparsePolynomial (h252Fiber1CertificateBasis i) ∈ I) :
    ∀ i, i < 42 → torusSparsePolynomial (h252Fiber1CertificateBasis i) ∈ I := by
  apply torusSparseStepBlock_mem I h252Fiber1CertificateBasis h252Fiber1CertificateSteps 41 42
    (h252Fiber1CertificateBlock030_mem I hbase)
  intro i hlo hhi
  let j : Fin 1 := ⟨i-41, by omega⟩
  have he : 41+j.val = i := by dsimp [j]; omega
  simpa only [he] using h252Fiber1CertificateBlock031_check j
end

end Biunimodular.F11
