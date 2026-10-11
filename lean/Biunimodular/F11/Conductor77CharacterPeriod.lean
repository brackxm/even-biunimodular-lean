/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Conductor77PrimitiveCharacter
import Biunimodular.F11.ASectorPeriodField

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial
noncomputable section

/-- The existing period polynomial sums precisely over the kernel of the
the primitive conductor-77 character. -/
theorem conductor77PeriodPolynomial_character_kernel :
    conductor77PeriodPolynomial =
      ∑ a : ZMod 77, if conductor77PrimitiveCharacter a = 1 then
        (X : ℤ[X]) ^ a.val else 0 := by
  have h : (Finset.univ.filter fun a : ZMod 77 => conductor77PrimitiveCharacter a = 1) =
      {1, 6, 13, 15, 36, 41, 62, 64, 71, 76} := by native_decide
  rw [← Finset.sum_filter, h]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  norm_num [conductor77PeriodPolynomial, ZMod.val_ofNat, ZMod.val_one_eq_one_mod]
 ; ring

/-- The actual generator of the certified sextic field is the Gaussian
period associated with that primitive character's kernel. -/
theorem periodEta77_character_kernel :
    periodEta77 = ∑ a : ZMod 77, if conductor77PrimitiveCharacter a = 1 then
      zeta77 ^ a.val else 0 := by
  rw [periodEta77, conductor77PeriodPolynomial_character_kernel]
  simp only [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_zero]

end
end Biunimodular.F11
