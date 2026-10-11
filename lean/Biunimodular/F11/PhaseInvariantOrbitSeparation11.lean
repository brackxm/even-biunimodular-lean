/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PhaseFixedSliceExistence11

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# The physical invariant separates normalized even orbits

The exact fixed-slice realization and the independent physical upper bound
give a bijection between the eight split quotient roots and the eight orbits
of actual phase solutions.  This file extracts the pointwise consequence used
in the full Fourier symmetry argument: preserving `u` forces a physical point
to stay in its concrete dilation/conjugation orbit.
-/

/-- Distinct normalized even physical orbits have distinct `u` values. -/
theorem phaseSolution11OrbitInvariantU_injective :
    Function.Injective phaseSolution11OrbitInvariantU := by
  intro a b hab
  obtain ⟨r, rfl⟩ := splitRootPhaseOrbit11_bijective.2 a
  obtain ⟨s, rfl⟩ := splitRootPhaseOrbit11_bijective.2 b
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  change phaseInvariantU11 (splitRootPhaseSolution11 r).1 =
    phaseInvariantU11 (splitRootPhaseSolution11 s).1 at hab
  have hc := congrArg ((↑) : ℝ → ℂ) hab
  simpa using hc

/-- Equality of the numerical physical invariant is equivalent to equality
in the actual dilation/conjugation quotient. -/
theorem phaseSolution11_same_orbit_iff_u_eq (s t : PhaseSolution11) :
    Quotient.mk'' s = (Quotient.mk'' t : PhaseSolution11Orbit) ↔
      phaseInvariantU11 s.1 = phaseInvariantU11 t.1 := by
  constructor
  · intro h
    exact congrArg phaseSolution11OrbitInvariantU h
  · intro h
    exact phaseSolution11OrbitInvariantU_injective h

/-- Any transformation of the physical solution set preserving `u` acts
within each concrete normalized even symmetry orbit. -/
theorem phaseSolution11_orbit_of_invariant_preserving
    (T : PhaseSolution11 → PhaseSolution11)
    (hT : ∀ s, phaseInvariantU11 (T s).1 = phaseInvariantU11 s.1)
    (s : PhaseSolution11) :
    ∃ g : EvenSymmetry11, T s = g • s := by
  have horbit :
      (Quotient.mk'' (T s) : PhaseSolution11Orbit) = Quotient.mk'' s :=
    (phaseSolution11_same_orbit_iff_u_eq (T s) s).2 (hT s)
  have hrel := Quotient.exact horbit
  change MulAction.orbitRel EvenSymmetry11 PhaseSolution11 (T s) s at hrel
  rw [MulAction.orbitRel_apply] at hrel
  rcases hrel with ⟨g, hg⟩
  exact ⟨g, hg.symm⟩

end Biunimodular.F11
