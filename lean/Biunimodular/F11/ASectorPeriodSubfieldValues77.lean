/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodSubfieldIdentities77
import Biunimodular.F11.ASectorPeriodField

set_option autoImplicit false

namespace Biunimodular.F11
noncomputable section

/-- The six explicit periods in the actual conductor-77 cyclotomic field. -/
def periodOrbit77 (m : Fin 6) : Conductor77Cyclotomic :=
  conductor77PeriodOrbitValue zeta77 m

@[simp] theorem periodOrbit77_zero : periodOrbit77 0 = periodEta77 := by
  unfold periodOrbit77 conductor77PeriodOrbitValue periodEta77
  congr 1
  simp only [conductor77PeriodOrbitPolynomials, conductor77PeriodPolynomial]
  norm_num

/-- The quadratic period difference, before selecting a real square-root sign. -/
def periodQuadraticGenerator77 : Conductor77Cyclotomic :=
  2 * (periodOrbit77 0 + periodOrbit77 2 + periodOrbit77 4) - 1

/-- The real conductor-7 coordinate given by a pair of opposite periods. -/
def periodCubicGenerator77 : Conductor77Cyclotomic :=
  periodOrbit77 0 + periodOrbit77 3

theorem periodOrbit77_sum :
    periodOrbit77 0 + periodOrbit77 1 + periodOrbit77 2 +
      periodOrbit77 3 + periodOrbit77 4 + periodOrbit77 5 = 1 :=
  conductor77PeriodSum_identity zeta77 zeta77_cyclotomic_root

theorem periodOrbit77_pair (m : Fin 6) :
    periodOrbit77 m + periodOrbit77 ⟨(m.1 + 3) % 6, Nat.mod_lt _ (by decide)⟩ =
      -(zeta77 ^ ((22 * 3 ^ m.1) % 77) +
        zeta77 ^ ((77 - (22 * 3 ^ m.1) % 77) % 77)) :=
  conductor77PeriodPair_identity zeta77 zeta77_cyclotomic_root m

/-- The candidate quadratic-subfield generator satisfies its exact relation
in the actual field, rather than only as a finite character certificate. -/
theorem periodQuadraticGenerator77_square : periodQuadraticGenerator77 ^ 2 = 77 :=
  conductor77QuadraticPeriod_square zeta77 zeta77_cyclotomic_root

theorem periodQuadraticGenerator77_ne_zero : periodQuadraticGenerator77 ≠ 0 := by
  intro h
  have hs := periodQuadraticGenerator77_square
  rw [h] at hs
  norm_num at hs

/-- The candidate cubic-subfield generator satisfies the conductor-7 cubic. -/
theorem periodCubicGenerator77_relation :
    periodCubicGenerator77 ^ 3 - periodCubicGenerator77 ^ 2 -
      2 * periodCubicGenerator77 + 1 = 0 :=
  conductor77CubicPeriod_relation zeta77 zeta77_cyclotomic_root

theorem periodCubicGenerator77_eq_realCyclotomic :
    periodCubicGenerator77 = -(zeta77 ^ 22 + zeta77 ^ 55) := by
  simpa [periodCubicGenerator77] using periodOrbit77_pair 0

/-- Exact even-period half identity with the algebraic square-root sign. -/
theorem periodOrbit77_even_half :
    2 * (periodOrbit77 0 + periodOrbit77 2 + periodOrbit77 4) =
      1 + periodQuadraticGenerator77 := by
  unfold periodQuadraticGenerator77
  ring

/-- The other period half has the opposite quadratic sign. -/
theorem periodOrbit77_odd_half :
    2 * (periodOrbit77 1 + periodOrbit77 3 + periodOrbit77 5) =
      1 - periodQuadraticGenerator77 := by
  unfold periodQuadraticGenerator77
  linear_combination 2 * periodOrbit77_sum

end
end Biunimodular.F11
