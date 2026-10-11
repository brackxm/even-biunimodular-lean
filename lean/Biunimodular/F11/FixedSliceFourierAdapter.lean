/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Fourier.ZMod
import Biunimodular.F11.FixedSliceBoundaryReduction

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Adapter from a full finite Fourier transform to the six-coordinate slice

The intrinsic fixed-slice modules only need `NoDisjointFourierSupport` on the
six even coordinates.  This file proves that consequence from a full-support
uncertainty statement plus an exact lift/intertwining equivalence.  Thus the
hypothesis at this interface is full-support Fourier uncertainty. The concrete
prime-eleven instance is proved in `Even11FourierLift`.
-/

section Adapter

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinatewise support-disjointness for a full finite Fourier model. -/
def FullNoDisjointFourierSupport
    (Ffull : (ι → K) →ₗ[K] (ι → K)) : Prop :=
  ∀ f : ι → K, f ≠ 0 → ¬ (∀ x, f x = 0 ∨ Ffull f x = 0)

/-- Exact data identifying the six-coordinate even model with a subspace of a
full Fourier model.  `lift` need only be injective; `intertwine` states that
Fourier followed by lifting agrees with lifting followed by the six-coordinate
operator. -/
structure EvenFourierLift
    (F6 : Even6 K →ₗ[K] Even6 K)
    (Ffull : (ι → K) →ₗ[K] (ι → K)) where
  lift : Even6 K →ₗ[K] (ι → K)
  lift_injective : Function.Injective lift
  coord_of_full : ι → Fin 6
  lift_apply : ∀ h x, lift h x = h (coord_of_full x)
  intertwine : ∀ h, lift (F6 h) = Ffull (lift h)

omit [Fintype ι] [DecidableEq ι] in
/-- Full support uncertainty descends to the six-coordinate model. -/
theorem noDisjointFourierSupport_of_full
    {F6 : Even6 K →ₗ[K] Even6 K}
    {Ffull : (ι → K) →ₗ[K] (ι → K)}
    (L : EvenFourierLift F6 Ffull)
    (hu : FullNoDisjointFourierSupport Ffull) :
    NoDisjointFourierSupport F6 := by
  intro h hnz hdis
  have hlift_ne : L.lift h ≠ 0 := by
    intro hz
    apply hnz
    apply L.lift_injective
    simpa using hz
  apply hu (L.lift h) hlift_ne
  intro x
  rcases hdis (L.coord_of_full x) with hx | hFx
  · left
    simpa [L.lift_apply] using hx
  · right
    rw [← L.intertwine]
    simpa [L.lift_apply] using hFx

omit [Fintype ι] [DecidableEq ι] in
/-- Once a concrete length-11 lift and Tao's prime support theorem are
available, the fixed slice has no projective boundary. -/
theorem fixedSlice_common_ne_zero_of_full_uncertainty
    {F6 : Even6 K →ₗ[K] Even6 K}
    {Ffull : (ι → K) →ₗ[K] (ι → K)}
    (L : EvenFourierLift F6 Ffull)
    (hu : FullNoDisjointFourierSupport Ffull)
    {h : Even6 K}
    (hnz : h ≠ 0)
    (hh : FixedSliceEq F6 h) :
    fourierCoordProduct F6 h 0 ≠ 0 :=
  fixedSlice_common_ne_zero_of_uncertainty
    (noDisjointFourierSupport_of_full L hu) hnz hh

end Adapter

end Biunimodular.F11
