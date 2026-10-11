/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Biunimodular.F11

/-- Polynomial relations annihilated after multiplying by a fixed projection
form an ideal. No idempotence or reducedness assumption is required. -/
def algebraProjectionIdeal {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (e : A) : Ideal R where
  carrier := {p | e * f p = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change e * f (p + q) = 0
    rw [map_add, mul_add, hp, hq, add_zero]
  smul_mem' := by
    intro r p hp
    change e * f (r * p) = 0
    rw [map_mul, mul_left_comm, hp, mul_zero]

@[simp] theorem mem_algebraProjectionIdeal {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (e : A) (p : R) :
    p ∈ algebraProjectionIdeal f e ↔ e * f p = 0 := Iff.rfl

end Biunimodular.F11
