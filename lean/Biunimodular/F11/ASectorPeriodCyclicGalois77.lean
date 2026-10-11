/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodField
import Mathlib.GroupTheory.SpecificGroups.ZGroup

set_option autoImplicit false

namespace Biunimodular.F11
open scoped IsMulCommutative
noncomputable section

local instance : IsAbelianGalois ℚ conductor77PeriodField :=
  conductor77PeriodField_isAbelianGalois

/-- The automorphism group of the actual sextic period field has order six. -/
theorem conductor77PeriodGalois_card :
    Nat.card (conductor77PeriodField ≃ₐ[ℚ] conductor77PeriodField) = 6 := by
  rw [IsGalois.card_aut_eq_finrank, conductor77PeriodField_finrank]

/-- An abelian group of squarefree order six is cyclic. Applied here to the
actual period field's automorphisms, this proves its cyclic Galois group. -/
theorem conductor77PeriodGalois_isCyclic :
    IsCyclic (conductor77PeriodField ≃ₐ[ℚ] conductor77PeriodField) := by
  let : Finite (conductor77PeriodField ≃ₐ[ℚ] conductor77PeriodField) :=
    Nat.finite_of_card_ne_zero (by rw [conductor77PeriodGalois_card]; decide)
  let : IsZGroup (conductor77PeriodField ≃ₐ[ℚ] conductor77PeriodField) :=
    IsZGroup.of_squarefree (by rw [conductor77PeriodGalois_card]; native_decide)
  infer_instance

/-- A group isomorphism with the cyclic group of order six. -/
def conductor77PeriodGaloisEquivC6 :
    Multiplicative (ZMod 6) ≃*
      (conductor77PeriodField ≃ₐ[ℚ] conductor77PeriodField) := by
  rw [← conductor77PeriodGalois_card]
  exact zmodCyclicMulEquiv conductor77PeriodGalois_isCyclic

end
end Biunimodular.F11
