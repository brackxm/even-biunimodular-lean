/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorX77RealCoordinate

set_option autoImplicit false

namespace Biunimodular.F11

local instance : IsAbelianGalois ℚ Conductor77Cyclotomic :=
  conductor77_isAbelianGalois

local instance : IsAbelianGalois ℚ Conductor77MaxReal := by
  exact IsAbelianGalois.of_algHom
    (IsScalarTower.toAlgHom ℚ Conductor77MaxReal Conductor77Cyclotomic)

local instance : IsGalois conductor77RealPeriodField Conductor77MaxReal := by
  infer_instance

/-- The real conductor-77 field has exactly five automorphisms over its
explicit Gaussian-period sextic field. -/
theorem conductor77_real_relative_galois_card :
    Nat.card (Conductor77MaxReal ≃ₐ[conductor77RealPeriodField]
      Conductor77MaxReal) = 5 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact conductor77_real_relative_finrank

/-- The relative Galois group is cyclic because its order is prime. -/
theorem conductor77_real_relative_galois_cyclic :
    IsCyclic (Conductor77MaxReal ≃ₐ[conductor77RealPeriodField]
      Conductor77MaxReal) := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact isCyclic_of_prime_card conductor77_real_relative_galois_card

/-- The relative Galois group is (noncanonically) isomorphic to `C₅`. -/
noncomputable def conductor77_real_relative_galois_equiv_C5 :
    Multiplicative (ZMod 5) ≃*
      (Conductor77MaxReal ≃ₐ[conductor77RealPeriodField]
        Conductor77MaxReal) := by
  rw [← conductor77_real_relative_galois_card]
  exact zmodCyclicMulEquiv conductor77_real_relative_galois_cyclic

end Biunimodular.F11
