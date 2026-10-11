/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

theorem adjoinRoot_map_mk
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (h : q ∣ p.map f) (g : Polynomial R) :
    AdjoinRoot.map f p q h (AdjoinRoot.mk p g) = AdjoinRoot.mk q (g.map f) := by
  rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
  change Polynomial.aeval (AdjoinRoot.root q) (g.map f) = _
  exact AdjoinRoot.aeval_eq _

/-- Monic quotient presentations preserve an injective coefficient map.
This connects integral certificate matrices to their rational counterparts. -/
theorem adjoinRoot_monic_map_injective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f)
    (p : Polynomial R) (hp : p.Monic) :
    Function.Injective (AdjoinRoot.map f p (p.map f) dvd_rfl) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinRoot_map_mk, AdjoinRoot.mk_eq_zero] at hx
  exact AdjoinRoot.mk_eq_zero.mpr ((Polynomial.map_dvd_map f hf hp).mp hx)

end
end Biunimodular.F11
