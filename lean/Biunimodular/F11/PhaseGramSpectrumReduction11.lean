/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PhaseGramQuotient11

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Concrete reduction of the F11 Gram spectrum certificate

The image of the physical phase solutions has a spectrum certificate when:

* every physical invariant is a root of the degree-sixteen polynomial;
* equality of the invariant implies equality modulo dilation and conjugation;
* every admissible split root is realized by a physical solution.

This module packages these properties as `PhaseGramSpectrumCertificate`.
The concrete certificate is constructed in `PhaseFixedSliceExistence11`.
-/

/-- The concrete physical content of the Gram spectrum statement, before
passing to either symmetry quotient. -/
structure PhaseInvariantSpectrumCertificate11 where
  u_isRoot : ∀ s : PhaseSolution11,
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
      (phaseInvariantU11 s.1 : ℂ)
  u_complete : ∀ s t : PhaseSolution11,
    phaseInvariantU11 s.1 = phaseInvariantU11 t.1 →
      MulAction.orbitRel EvenSymmetry11 PhaseSolution11 s t
  u_realized : ∀ r : SplitQuotientRoot, ∃ s : PhaseSolution11,
    (phaseInvariantU11 s.1 : ℂ) = (r : ℂ)

/-- Polynomial necessity descends from physical solutions to their symmetry
orbits. -/
theorem PhaseInvariantSpectrumCertificate11.orbit_u_isRoot
    (C : PhaseInvariantSpectrumCertificate11)
    (q : PhaseSolution11Orbit) :
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
      (phaseSolution11OrbitInvariantU q : ℂ) := by
  refine Quotient.inductionOn' q ?_
  intro s
  exact C.u_isRoot s

/-- The completeness field says intrinsically that `u` separates physical
dilation/conjugation orbits. -/
theorem PhaseInvariantSpectrumCertificate11.orbitInvariantU_injective
    (C : PhaseInvariantSpectrumCertificate11) :
    Function.Injective phaseSolution11OrbitInvariantU := by
  intro q r hqr
  refine Quotient.inductionOn₂' q r ?_ hqr
  intro s t hst
  exact Quotient.sound (C.u_complete s t hst)

/-- Via the already-proved Gram reconstruction equivalence, the affine Gram
coordinate separates cyclic Gram orbits as soon as the physical invariant
separates dilation/conjugation orbits. -/
theorem PhaseInvariantSpectrumCertificate11.gramInvariantU_injective
    (C : PhaseInvariantSpectrumCertificate11) :
    Function.Injective phaseGramOrbitInvariantU11 := by
  intro q r hqr
  apply phaseSolution11OrbitGramEquiv.symm.injective
  apply C.orbitInvariantU_injective
  let q' : PhaseSolution11Orbit := phaseSolution11OrbitGramEquiv.symm q
  let r' : PhaseSolution11Orbit := phaseSolution11OrbitGramEquiv.symm r
  have hq : phaseGramOrbitInvariantU11 q =
      phaseSolution11OrbitInvariantU q' := by
    rw [← phaseSolution11OrbitGramEquiv_value q']
    simp [q']
  have hr : phaseGramOrbitInvariantU11 r =
      phaseSolution11OrbitInvariantU r' := by
    rw [← phaseSolution11OrbitGramEquiv_value r']
    simp [r']
  exact hq.symm.trans (hqr.trans hr)

/-- The three concrete phase-coordinate statements construct the complete
value-preserving spectrum certificate on the rank-two Gram quotient. -/
theorem PhaseInvariantSpectrumCertificate11.toPhaseGramSpectrumCertificate
    (C : PhaseInvariantSpectrumCertificate11) :
    PhaseGramSpectrumCertificate where
  gram_u_isRoot q := by
    let p : PhaseSolution11Orbit := phaseSolution11OrbitGramEquiv.symm q
    have hvalue : phaseGramOrbitInvariantU11 q =
        phaseSolution11OrbitInvariantU p := by
      rw [← phaseSolution11OrbitGramEquiv_value p]
      simp [p]
    rw [hvalue]
    exact C.orbit_u_isRoot p
  gram_u_bijective := by
    constructor
    · intro q r hqr
      apply C.gramInvariantU_injective
      have hvalue := congrArg
        (fun z : SplitQuotientRoot ↦ ((z : SplitQuotientRoot) : ℂ)) hqr
      change (phaseGramOrbitInvariantU11 q : ℂ) =
        (phaseGramOrbitInvariantU11 r : ℂ) at hvalue
      exact Complex.ofReal_injective hvalue
    · intro r
      obtain ⟨s, hs⟩ := C.u_realized r
      let q : PhaseGramOrbit11 :=
        phaseSolution11OrbitGramEquiv (Quotient.mk'' s)
      refine ⟨q, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change (phaseGramOrbitInvariantU11 q : ℂ) = (r : ℂ)
      calc
        (phaseGramOrbitInvariantU11 q : ℂ) =
            (phaseInvariantU11 s.1 : ℂ) := by
          exact congrArg ((↑) : ℝ → ℂ)
            (phaseSolution11OrbitGramEquiv_value (Quotient.mk'' s))
        _ = (r : ℂ) := hs

/-- Conversely, a Gram spectrum certificate contains exactly the three
physical statements above.  Thus the reduction loses no mathematical
content; it only removes the quotient/Gram packaging from the obligations
that a concrete certificate producer must prove. -/
theorem PhaseGramSpectrumCertificate.toPhaseInvariantSpectrumCertificate11
    (C : PhaseGramSpectrumCertificate) :
    PhaseInvariantSpectrumCertificate11 where
  u_isRoot s := by
    have hroot := C.gram_u_isRoot
      (phaseSolution11OrbitGramEquiv (Quotient.mk'' s))
    rw [phaseSolution11OrbitGramEquiv_value] at hroot
    exact hroot
  u_complete s t hst := by
    apply Quotient.exact
    apply phaseSolution11OrbitGramEquiv.injective
    apply C.gramRootEquiv.injective
    apply Subtype.ext
    apply Subtype.ext
    change
      (phaseGramOrbitInvariantU11
          (phaseSolution11OrbitGramEquiv (Quotient.mk'' s)) : ℂ) =
        (phaseGramOrbitInvariantU11
          (phaseSolution11OrbitGramEquiv (Quotient.mk'' t)) : ℂ)
    rw [phaseSolution11OrbitGramEquiv_value,
      phaseSolution11OrbitGramEquiv_value]
    exact congrArg ((↑) : ℝ → ℂ) hst
  u_realized r := by
    obtain ⟨q, hq⟩ := C.gram_u_bijective.2 r
    let p : PhaseSolution11Orbit := phaseSolution11OrbitGramEquiv.symm q
    obtain ⟨s, hs⟩ := Quotient.exists_rep p
    refine ⟨s, ?_⟩
    have horbit : phaseSolution11OrbitInvariantU p =
        phaseInvariantU11 s.1 := by
      rw [← hs]
      rfl
    have hvalue : phaseGramOrbitInvariantU11 q =
        phaseSolution11OrbitInvariantU p := by
      rw [← phaseSolution11OrbitGramEquiv_value p]
      simp [p]
    have hrootValue := congrArg
      (fun z : SplitQuotientRoot ↦ ((z : SplitQuotientRoot) : ℂ)) hq
    change (phaseGramOrbitInvariantU11 q : ℂ) = (r : ℂ) at hrootValue
    exact (congrArg ((↑) : ℝ → ℂ) horbit).symm.trans <|
      (congrArg ((↑) : ℝ → ℂ) hvalue).symm.trans hrootValue

end

end Biunimodular.F11
