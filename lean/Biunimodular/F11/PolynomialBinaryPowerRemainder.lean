/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Biunimodular.F11

theorem binaryPowerRemainder_double {R : Type*} [CommRing R]
    (f base previous next : R) (n : ℕ)
    (h : f ∣ base^n-previous) (hstep : f ∣ previous*previous-next) :
    f ∣ base^(2*n)-next := by
  have hm := dvd_mul_sub_mul h h
  have ht := dvd_add hm hstep
  convert ht using 1; rw [Nat.mul_comm 2 n, pow_mul, pow_two]; ring

theorem binaryPowerRemainder_add_one {R : Type*} [CommRing R]
    (f base previous next : R) (n : ℕ)
    (h : f ∣ base^n-previous) (hstep : f ∣ previous*base-next) :
    f ∣ base^(n+1)-next := by
  have hz : f ∣ base-base := by simp
  have hm := dvd_mul_sub_mul h hz
  have ht := dvd_add hm hstep
  convert ht using 1; rw [pow_succ]; ring

end Biunimodular.F11
