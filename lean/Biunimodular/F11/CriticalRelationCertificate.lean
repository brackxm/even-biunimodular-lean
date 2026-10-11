/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.SchreyerCriticalBounds

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

/-- A critical relation packaged with its proved properties. Keeping these
properties as projections avoids rechecking a large case split when assembling
all relations of an exported basis. -/
structure CriticalRelationCertificate {σ K : Type*} [Field K] {b : ℕ}
    (m : MonomialOrder σ) (g labels : Fin b → MvPolynomial σ K)
    (I : Ideal (MvPolynomial σ K)) (pair : Fin b × Fin b) where
  v : Fin b → MvPolynomial σ K
  relation : (∑ k, v k * g k) = 0
  label : relationLabelMap labels v ∈ I
  top : v pair.2 * g pair.2 ≠ 0 ∧
    m.degree (v pair.2 * g pair.2) = m.degree (g pair.1) ⊔ m.degree (g pair.2) ∧
    ∀ k, schreyerKey m g v k ≤ schreyerKey m g v pair.2

end
end Biunimodular.F11
