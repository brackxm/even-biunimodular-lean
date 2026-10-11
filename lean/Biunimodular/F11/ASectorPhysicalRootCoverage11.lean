/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPhysicalCoordinateDistinct11

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-- A concrete accepted A-sector box for each tagged root interval. -/
def aSectorF30BoxForRootIndex11 (i : Fin 40) : PhaseCandidateQuintuple11 :=
  ((aSectorCandidateOrbitRepresentatives11.flatMap candidateSymmetryOrbit11).find?
    (fun q => decide ((match q with | (_, _, _, _, ij) => ij / 4) = i.1))).getD
      (0, 0, 0, 0, 0)

/-- The exact accepted-box table hits every one of the fifteen F30 root
intervals with the selected A-sector candidate. -/
theorem aSectorF30BoxForRootIndex11_certificate :
    ∀ i : Fin 40, i ∈ p150FactorRootIndices11 .f30 →
      aSectorF30BoxForRootIndex11 i ∈
        aSectorCandidateOrbitRepresentatives11.flatMap candidateSymmetryOrbit11 ∧
      aSectorF30BoxForRootIndex11 i ∈ acceptedCandidateQuintuples ∧
        (match aSectorF30BoxForRootIndex11 i with
          | (_, _, _, _, ij) => ij / 4) = i.1 := by
  native_decide

/-- Every isolated physical F30 root interval contains the squared imaginary
coordinate of an actual A-sector phase solution. -/
theorem everyF30RootInterval_physically_realized11
    (i : Fin 40) (hi : i ∈ p150FactorRootIndices11 .f30) :
    ∃ s : PhaseSolution11,
      invariantAR.IsRoot (phaseInvariantU11 s.1) ∧
        squaredKInInterval11 s.1.k (squaredKRootIntervals40[i.1]!) ∧
          (p150FactorPolynomialR11 .f30).IsRoot (s.1.k ^ 2) := by
  let q := aSectorF30BoxForRootIndex11 i
  obtain ⟨hflat, haccepted, hindex⟩ :=
    aSectorF30BoxForRootIndex11_certificate i hi
  obtain ⟨r, hr, hq⟩ := List.mem_flatMap.mp hflat
  let accepted : AcceptedPhaseCandidate11 :=
    ⟨q, List.mem_toFinset.mpr haccepted⟩
  obtain ⟨s, hbox⟩ := everyAcceptedPhaseBox_realized11 accepted
  refine ⟨s, phaseSolution_invariantA_of_taggedBox11 s r q hr hq hbox,
    ?_, phaseSolution_f30_of_aSectorCandidateBox s r q hr hq hbox⟩
  have hinterval := phaseSolution_last_interval_of_acceptedBox11
    s q haccepted hbox
  change q.2.2.2.2 / 4 = i.1 at hindex
  simpa only [hindex] using hinterval

/-- Every real F30 root in the unit squared-coordinate range is the last
coordinate square of an actual physical A-sector phase. -/
theorem everyF30RootInUnitInterval_physically_realized11
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hroot : (p150FactorPolynomialR11 .f30).IsRoot y) :
    ∃ s : PhaseSolution11,
      invariantAR.IsRoot (phaseInvariantU11 s.1) ∧ s.1.k ^ 2 = y := by
  obtain ⟨i, hi, hybox⟩ :=
    p150FactorPolynomialR11_root_in_interval .f30 y hy0 hy1 hroot
  obtain ⟨s, hA, hsbox, hsroot⟩ :=
    everyF30RootInterval_physically_realized11 i hi
  have htag := p150FactorRootIndices11_tags .f30 i hi
  have hsroot' : (p150FactorPolynomialR11
      (squaredKRootIntervals40[i.1]!).factor).IsRoot (s.1.k ^ 2) := by
    rw [htag]
    exact hsroot
  have hyroot' : (p150FactorPolynomialR11
      (squaredKRootIntervals40[i.1]!).factor).IsRoot y := by
    rw [htag]
    exact hroot
  refine ⟨s, hA, ?_⟩
  exact p150FactorPolynomialR11_root_unique_in_interval i
    (s.1.k ^ 2) y hsbox.1 hsbox.2 hybox.1 hybox.2
      hsroot' hyroot'

/-- The physical A-sector scaled squared coordinates are exactly the roots
of the degree-thirty polynomial in the interval `[0,4]`. -/
theorem aSectorG30_root_in_four_iff_physicalCoordinate11 (x : ℝ) :
    (0 ≤ x ∧ x ≤ 4 ∧
      (aSectorG30.map (Int.castRingHom ℝ)).IsRoot x) ↔
      ∃ s : PhaseSolution11,
        invariantAR.IsRoot (phaseInvariantU11 s.1) ∧
          4 * s.1.k ^ 2 = x := by
  constructor
  · rintro ⟨hx0, hx4, hroot⟩
    have hy0 : 0 ≤ x / 4 := by positivity
    have hy1 : x / 4 ≤ 1 := by linarith
    have hyroot : (p150FactorPolynomialR11 .f30).IsRoot (x / 4) := by
      rw [Polynomial.IsRoot, p150F30_factor_eval_eq_G30_scaled]
      simpa only [show 4 * (x / 4) = x by ring] using hroot.eq_zero
    obtain ⟨s, hA, hs⟩ :=
      everyF30RootInUnitInterval_physically_realized11
        (x / 4) hy0 hy1 hyroot
    refine ⟨s, hA, ?_⟩
    linarith
  · rintro ⟨s, hA, hcoord⟩
    have hcircle := s.2.1.2.2.2.2
    have hbound : s.1.k ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg s.1.j]
    obtain ⟨r, hr, q, hq, hbox⟩ := everyASectorPhase_in_taggedBox11 s hA
    have hroot := phaseSolution_G30_of_aSectorCandidateBox s r q hr hq hbox
    constructor
    · rw [← hcoord]
      positivity
    constructor
    · rw [← hcoord]
      nlinarith
    · rw [← hcoord]
      exact hroot

/-- At the specified analytic embedding of the conductor-77 field, a
canonical coordinate is physical precisely when its real value lies in the
unit-circle range. -/
theorem analyticASectorCoordinate_physical_iff11
    (e : ℕ) (he : e ∈ aSectorCanonicalAnalyticExponents77) :
    (0 ≤ analyticASectorCoordinate e ∧ analyticASectorCoordinate e ≤ 4) ↔
      ∃ s : PhaseSolution11,
        invariantAR.IsRoot (phaseInvariantU11 s.1) ∧
          4 * s.1.k ^ 2 = analyticASectorCoordinate e := by
  have hmin := aSectorCanonicalAnalyticExponents77_minpoly e he
  have hroot : (aSectorG30.map (Int.castRingHom ℝ)).IsRoot
      (analyticASectorCoordinate e) := by
    have hae : (aeval (analyticASectorCoordinate e))
        (aSectorG30.map (Int.castRingHom ℚ)) = 0 := by
      rw [← hmin]
      exact minpoly.aeval ℚ _
    have hcomp : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) =
        Int.castRingHom ℝ := by
      ext n
      simp
    rw [Polynomial.IsRoot]
    simpa only [aeval_def, eval₂_eq_eval_map, map_map,
      hcomp] using hae
  constructor
  · intro hbound
    exact (aSectorG30_root_in_four_iff_physicalCoordinate11
      (analyticASectorCoordinate e)).mp ⟨hbound.1, hbound.2, hroot⟩
  · intro hphysical
    have h := (aSectorG30_root_in_four_iff_physicalCoordinate11
      (analyticASectorCoordinate e)).mpr hphysical
    exact ⟨h.1, h.2.1⟩

end Biunimodular.F11
