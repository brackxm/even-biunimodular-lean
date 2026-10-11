/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ProofTactics
import Biunimodular.F11.P150PhaseExhaustionBridge11
import Biunimodular.F11.PhaseGramSpectrumReduction11

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Finite P150 route to the F11 Gram spectrum

The P150 root cover and exact scanner put every phase solution into one of 80
boxes.  If each accepted box contains at most one actual solution, this gives
at most 80 solutions and hence, by the already-proved free order-ten symmetry
action, at most eight physical orbits.

Once polynomial necessity and realization of the eight admissible roots are
known, cardinality forces the physical invariant map to be bijective.  Thus
no separate orbit-separation field is needed for `PhaseGramSpectrumCertificate`.
-/

/-- Local uniqueness input for the 80 wide boxes emitted by the exact scan. -/
structure PhaseAcceptedBoxUniquenessCertificate11 where
  unique : ∀ (q : AcceptedPhaseCandidate11) (s t : PhaseSolution11),
    phaseCandidateQuintupleBox11 (1 / 10000) s.1 q.1 →
    phaseCandidateQuintupleBox11 (1 / 10000) t.1 q.1 →
    s = t

/-- Choose one accepted scanner box containing each actual phase solution. -/
noncomputable def P150KRootCoverCertificate11.acceptedBox
    (C : P150KRootCoverCertificate11) (s : PhaseSolution11) :
    AcceptedPhaseCandidate11 :=
  ⟨Classical.choose (C.phase_solution_in_accepted_box s), by
    simpa using (Classical.choose_spec
      (C.phase_solution_in_accepted_box s)).1⟩

theorem P150KRootCoverCertificate11.acceptedBox_contains
    (C : P150KRootCoverCertificate11) (s : PhaseSolution11) :
    phaseCandidateQuintupleBox11 (1 / 10000) s.1
      (C.acceptedBox s).1 := by
  simpa [P150KRootCoverCertificate11.acceptedBox] using
    (Classical.choose_spec (C.phase_solution_in_accepted_box s)).2

theorem P150KRootCoverCertificate11.acceptedBox_injective
    (C : P150KRootCoverCertificate11)
    (U : PhaseAcceptedBoxUniquenessCertificate11) :
    Function.Injective C.acceptedBox := by
  intro s t hst
  apply U.unique (C.acceptedBox s) s t (C.acceptedBox_contains s)
  have hval : (C.acceptedBox s).1 = (C.acceptedBox t).1 :=
    congrArg Subtype.val hst
  rw [hval]
  exact C.acceptedBox_contains t

/-- Finiteness of the physical solution set follows from root cover plus
local uniqueness; it is not assumed. -/
theorem P150KRootCoverCertificate11.phaseSolutionFinite
    (C : P150KRootCoverCertificate11)
    (U : PhaseAcceptedBoxUniquenessCertificate11) :
    Finite PhaseSolution11 :=
  Finite.of_injective C.acceptedBox (C.acceptedBox_injective U)

/-- The P150/scanner lane gives the sharp upper bound needed for the spectrum
argument.  Existence is deliberately not used here. -/
theorem P150KRootCoverCertificate11.phaseSolution_card_le_80
    (C : P150KRootCoverCertificate11)
    (U : PhaseAcceptedBoxUniquenessCertificate11) :
    Nat.card PhaseSolution11 ≤ 80 := by
  let _ := C.phaseSolutionFinite U
  calc
    Nat.card PhaseSolution11 ≤ Nat.card AcceptedPhaseCandidate11 :=
      Nat.card_le_card_of_injective C.acceptedBox
        (C.acceptedBox_injective U)
    _ = 80 := by
      simpa only [Nat.card_eq_fintype_card] using acceptedPhaseCandidate11_card

/-- Dividing the at-most-80 solutions by the free order-ten action leaves at
most eight physical orbits. -/
theorem P150KRootCoverCertificate11.phaseSolutionOrbit_card_le_8
    (C : P150KRootCoverCertificate11)
    (U : PhaseAcceptedBoxUniquenessCertificate11) :
    Nat.card PhaseSolution11Orbit ≤ 8 := by
  let _ := C.phaseSolutionFinite U
  let E : PhaseSolution11 ≃ PhaseSolution11Orbit × EvenSymmetry11 :=
    MulAction.selfEquivOrbitsQuotientProd
      (fun s : PhaseSolution11 => IsCancelSMul.stabilizer_eq_bot s)
  have hprod :
      Nat.card PhaseSolution11 =
        Nat.card PhaseSolution11Orbit * Nat.card EvenSymmetry11 := by
    calc
      Nat.card PhaseSolution11 =
          Nat.card (PhaseSolution11Orbit × EvenSymmetry11) :=
        Nat.card_congr E
      _ = Nat.card PhaseSolution11Orbit * Nat.card EvenSymmetry11 :=
        Nat.card_prod PhaseSolution11Orbit EvenSymmetry11
  have hgroup : Nat.card EvenSymmetry11 = 10 := by
    simpa only [Nat.card_eq_fintype_card] using evenSymmetry11_card
  have hsolutions := C.phaseSolution_card_le_80 U
  rw [hgroup] at hprod
  omega

/-- Root necessity on phase solutions transports to the equivalent Gram
orbit quotient. -/
theorem phase_u_isRoot_to_gram_u_isRoot
    (hroot : ∀ s : PhaseSolution11,
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (phaseInvariantU11 s.1 : ℂ)) :
    ∀ q : PhaseGramOrbit11,
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (phaseGramOrbitInvariantU11 q : ℂ) := by
  intro q
  let p : PhaseSolution11Orbit := phaseSolution11OrbitGramEquiv.symm q
  have hp :
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (phaseSolution11OrbitInvariantU p : ℂ) := by
    refine Quotient.inductionOn' p ?_
    intro s
    exact hroot s
  have hvalue : phaseGramOrbitInvariantU11 q =
      phaseSolution11OrbitInvariantU p := by
    rw [← phaseSolution11OrbitGramEquiv_value p]
    simp [p]
  rwa [hvalue]

/-- Root cover, local box uniqueness, polynomial necessity, and root
realization construct the full Gram spectrum certificate.  Injectivity is a
cardinality consequence of surjectivity between two types of size at most and
exactly eight. -/
theorem p150_phaseGramSpectrumCertificate
    (C : P150KRootCoverCertificate11)
    (U : PhaseAcceptedBoxUniquenessCertificate11)
    (hroot : ∀ s : PhaseSolution11,
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (phaseInvariantU11 s.1 : ℂ))
    (hrealized : ∀ r : SplitQuotientRoot, ∃ s : PhaseSolution11,
      (phaseInvariantU11 s.1 : ℂ) = (r : ℂ)) :
    PhaseGramSpectrumCertificate := by
  let _ := C.phaseSolutionFinite U
  let _ : Finite PhaseSolution11Orbit := inferInstance
  let _ : Finite PhaseGramOrbit11 :=
    Finite.of_injective phaseSolution11OrbitGramEquiv.symm
      phaseSolution11OrbitGramEquiv.symm.injective
  let hgramroot := phase_u_isRoot_to_gram_u_isRoot hroot
  have hsurj : Function.Surjective
      (phaseGramOrbitSplitRootMap hgramroot) := by
    intro r
    obtain ⟨s, hs⟩ := hrealized r
    let q : PhaseGramOrbit11 :=
      phaseSolution11OrbitGramEquiv (Quotient.mk'' s)
    refine ⟨q, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((phaseGramOrbitSplitRootMap hgramroot q : SplitQuotientRoot) : ℂ) =
      (r : ℂ)
    rw [phaseGramOrbitSplitRootMap_value]
    calc
      (phaseGramOrbitInvariantU11 q : ℂ) =
          (phaseSolution11OrbitInvariantU (Quotient.mk'' s) : ℂ) :=
        congrArg ((↑) : ℝ → ℂ)
          (phaseSolution11OrbitGramEquiv_value (Quotient.mk'' s))
      _ = (phaseInvariantU11 s.1 : ℂ) := rfl
      _ = (r : ℂ) := hs
  refine
    { gram_u_isRoot := hgramroot
      gram_u_bijective := ?_ }
  apply hsurj.bijective_of_nat_card_le
  calc
    Nat.card PhaseGramOrbit11 = Nat.card PhaseSolution11Orbit :=
      Nat.card_congr phaseSolution11OrbitGramEquiv.symm
    _ ≤ 8 := C.phaseSolutionOrbit_card_le_8 U
    _ = Nat.card SplitQuotientRoot := by
      simpa only [Nat.card_eq_fintype_card] using splitQuotientRoot_card.symm

/-- The same finite inputs fill the exact phase-coordinate certificate used
by `PhaseGramSpectrumReduction11`. -/
theorem p150_phaseInvariantSpectrumCertificate11
    (C : P150KRootCoverCertificate11)
    (U : PhaseAcceptedBoxUniquenessCertificate11)
    (hroot : ∀ s : PhaseSolution11,
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (phaseInvariantU11 s.1 : ℂ))
    (hrealized : ∀ r : SplitQuotientRoot, ∃ s : PhaseSolution11,
      (phaseInvariantU11 s.1 : ℂ) = (r : ℂ)) :
    PhaseInvariantSpectrumCertificate11 :=
  (p150_phaseGramSpectrumCertificate C U hroot hrealized).toPhaseInvariantSpectrumCertificate11

/-- Bundled finite-certificate interface for the P150 lane. -/
structure P150PhaseGramSpectrumInputs11 where
  rootCover : P150KRootCoverCertificate11
  boxUniqueness : PhaseAcceptedBoxUniquenessCertificate11
  u_isRoot : ∀ s : PhaseSolution11,
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
      (phaseInvariantU11 s.1 : ℂ)
  u_realized : ∀ r : SplitQuotientRoot, ∃ s : PhaseSolution11,
    (phaseInvariantU11 s.1 : ℂ) = (r : ℂ)

theorem P150PhaseGramSpectrumInputs11.toPhaseGramSpectrumCertificate
    (C : P150PhaseGramSpectrumInputs11) :
    PhaseGramSpectrumCertificate :=
  p150_phaseGramSpectrumCertificate C.rootCover C.boxUniqueness
    C.u_isRoot C.u_realized

end

end Biunimodular.F11
