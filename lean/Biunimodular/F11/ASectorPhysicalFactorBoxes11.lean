/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.P150PhaseBoxUniqueness11
import Biunimodular.F11.PhaseFixedSliceExistence11

set_option autoImplicit false

namespace Biunimodular.F11

/-- The exact squared-coordinate factor assigned to the final coordinate of
an accepted phase-box tuple. -/
def candidateLastFactor11 : PhaseCandidateQuintuple11 → KFactor
  | (_, _, _, _, ij) =>
      (squaredKRootIntervals40[ij / 4]!).factor

/-- The three non-Gaussian candidate orbits associated numerically with the
A rows, as they appear in the exact 80-box table. -/
def aSectorCandidateOrbitRepresentatives11 :
    List PhaseCandidateQuintuple11 :=
  (acceptedCandidateOrbitRepresentatives11.drop 1).take 3

/-- Every box in these three candidate orbits is tagged by the degree-thirty
squared-coordinate factor. -/
theorem aSectorCandidateOrbitBoxes_f30 :
    ∀ r ∈ aSectorCandidateOrbitRepresentatives11,
      ∀ q ∈ candidateSymmetryOrbit11 r,
        candidateLastFactor11 q = .f30 := by
  native_decide

/-- A physical phase solution in one of the three tagged A candidate orbits
has its last squared imaginary coordinate on the degree-thirty factor. -/
theorem phaseSolution_f30_of_aSectorCandidateBox
    (s : PhaseSolution11) (r q : PhaseCandidateQuintuple11)
    (hr : r ∈ aSectorCandidateOrbitRepresentatives11)
    (hq : q ∈ candidateSymmetryOrbit11 r)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 q) :
    (p150FactorPolynomialR11 .f30).IsRoot (s.1.k ^ 2) := by
  have haccepted : q ∈ acceptedCandidateQuintuples := by
    have hrep : r ∈ acceptedCandidateOrbitRepresentatives11 := by
      have h : ∀ x ∈ aSectorCandidateOrbitRepresentatives11,
          x ∈ acceptedCandidateOrbitRepresentatives11 := by native_decide
      exact h r hr
    have hq' : q ∈ (acceptedCandidateOrbitRepresentatives11.flatMap
        candidateSymmetryOrbit11).toFinset := by
      simp only [List.mem_toFinset, List.mem_flatMap]
      exact ⟨r, hrep, hq⟩
    rw [← acceptedCandidateQuintuples_eq_symmetry_orbits] at hq'
    simpa using hq'
  have hfactor := phaseSolution_last_tagged_factor_root11 s q haccepted hbox
  have htag := aSectorCandidateOrbitBoxes_f30 r hr q hq
  change (p150FactorPolynomialR11 (candidateLastFactor11 q)).IsRoot
    (s.1.k ^ 2) at hfactor
  rw [htag] at hfactor
  exact hfactor

/-- Cardinality equality upgrades the certified phase-box injection to a
bijection: every accepted box contains one physical phase solution. -/
theorem everyAcceptedPhaseBox_realized11
    (q : AcceptedPhaseCandidate11) :
    ∃ s : PhaseSolution11,
      phaseCandidateQuintupleBox11 (1 / 10000) s.1 q.1 := by
  let C := p150KRootCoverCertificate11
  let U := phaseAcceptedBoxUniquenessCertificate11
  let _ : Finite PhaseSolution11 := C.phaseSolutionFinite U
  have hcard : Nat.card AcceptedPhaseCandidate11 ≤
      Nat.card PhaseSolution11 := by
    rw [show Nat.card AcceptedPhaseCandidate11 = 80 by
      simpa only [Nat.card_eq_fintype_card] using
        acceptedPhaseCandidate11_card]
    exact (phaseSolution11_classification_complete.2.1).ge
  have hsurj : Function.Surjective C.acceptedBox :=
    (C.acceptedBox_injective U).bijective_of_nat_card_le hcard |>.2
  obtain ⟨s, hs⟩ := hsurj q
  refine ⟨s, ?_⟩
  rw [← hs]
  exact C.acceptedBox_contains s

set_option maxRecDepth 2048 in
/-- In particular, each of the three A-tagged candidate orbits contains a
genuine physical solution. -/
theorem aSectorCandidateRepresentative_realized11
    (r : PhaseCandidateQuintuple11)
    (hr : r ∈ aSectorCandidateOrbitRepresentatives11) :
    ∃ s : PhaseSolution11,
      phaseCandidateQuintupleBox11 (1 / 10000) s.1 r := by
  have hrep : r ∈ acceptedCandidateOrbitRepresentatives11 := by
    have h : ∀ x ∈ aSectorCandidateOrbitRepresentatives11,
        x ∈ acceptedCandidateOrbitRepresentatives11 := by native_decide
    exact h r hr
  have haccepted : r ∈ acceptedCandidateQuintuples := by
    have hq' : r ∈ (acceptedCandidateOrbitRepresentatives11.flatMap
        candidateSymmetryOrbit11).toFinset := by
      simp only [List.mem_toFinset, List.mem_flatMap]
      exact ⟨r, hrep, by
        simp [candidateSymmetryOrbit11, candidateDilationOrbit11]⟩
    rw [← acceptedCandidateQuintuples_eq_symmetry_orbits] at hq'
    simpa using hq'
  exact everyAcceptedPhaseBox_realized11 ⟨r, haccepted⟩

end Biunimodular.F11
