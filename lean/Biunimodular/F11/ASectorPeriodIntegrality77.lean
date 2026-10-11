/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodSubfields77

set_option autoImplicit false

namespace Biunimodular.F11
noncomputable section

/-- The displayed monic sextic proves integer integrality of the chosen period. -/
theorem periodEta77_isIntegral_int : IsIntegral ℤ periodEta77 := by
  exact ⟨periodC77, periodC77_monic, periodEta77_isRoot_periodC77⟩

/-- Every coset period is an algebraic integer in the ambient cyclotomic field. -/
theorem periodOrbit77_isIntegral_int (i : Fin 6) : IsIntegral ℤ (periodOrbit77 i) := by
  rw [← conductor77PeriodAutomorphism_periodEta i]
  exact IsIntegral.map (conductor77PeriodAutomorphism i) periodEta77_isIntegral_int

end
end Biunimodular.F11
