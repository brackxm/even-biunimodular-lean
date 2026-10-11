/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorFiniteArithmetic
import Biunimodular.F11.FiniteFieldFrobeniusCycle

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Biunimodular.F11

open Polynomial

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 37) := ⟨by decide⟩
private instance : Fact (Nat.Prime 211) := ⟨by decide⟩

private noncomputable instance :
    DecidableEq (invariantB5.rootSet invariantB5.SplittingField) := Classical.decEq _
private noncomputable instance :
    DecidableEq (B37seven.rootSet B37seven.SplittingField) := Classical.decEq _
private noncomputable instance :
    DecidableEq (B211five.rootSet B211five.SplittingField) := Classical.decEq _

private theorem b5_degree : invariantB5.natDegree = 8 := by
  norm_num [invariantB5]
  compute_degree <;> norm_num

private theorem b37_degree : B37seven.natDegree = 7 := by
  norm_num [B37seven]
  compute_degree <;> norm_num

private theorem b211_degree : B211five.natDegree = 5 := by
  norm_num [B211five]
  compute_degree <;> norm_num

/-- The checked mod-5 irreducibility yields a single Frobenius cycle on the
eight roots in the finite-field splitting field. -/
theorem b_mod5_frobenius_isCycle :
    (finiteFieldFrobPerm invariantB5).IsCycle := by
  apply finiteFieldFrobPerm_isCycle invariantB5 B_mod5_cycle8
  rw [b5_degree]
  decide

/-- The irreducible degree-seven factor mod 37 is one Frobenius cycle. -/
theorem b_mod37_seven_frobenius_isCycle :
    (finiteFieldFrobPerm B37seven).IsCycle := by
  apply finiteFieldFrobPerm_isCycle B37seven B37seven_irreducible
  rw [b37_degree]
  decide

/-- The irreducible degree-five factor mod 211 is one Frobenius cycle. -/
theorem b_mod211_five_frobenius_isCycle :
    (finiteFieldFrobPerm B211five).IsCycle := by
  apply finiteFieldFrobPerm_isCycle B211five B211five_irreducible
  rw [b211_degree]
  decide

theorem b_mod5_frobenius_support_card :
    (finiteFieldFrobPerm invariantB5).support.card = 8 := by
  rw [finiteFieldFrobPerm_support_card invariantB5 B_mod5_cycle8
    (by rw [b5_degree]; decide), b5_degree]

theorem b_mod37_seven_frobenius_support_card :
    (finiteFieldFrobPerm B37seven).support.card = 7 := by
  rw [finiteFieldFrobPerm_support_card B37seven B37seven_irreducible
    (by rw [b37_degree]; decide), b37_degree]

theorem b_mod211_five_frobenius_support_card :
    (finiteFieldFrobPerm B211five).support.card = 5 := by
  rw [finiteFieldFrobPerm_support_card B211five B211five_irreducible
    (by rw [b211_degree]; decide), b211_degree]

end Biunimodular.F11
