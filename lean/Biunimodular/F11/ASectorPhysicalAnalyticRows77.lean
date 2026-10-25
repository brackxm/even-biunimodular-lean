/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorAnalyticRootMatch77

set_option autoImplicit false

namespace Biunimodular.F11

/-- Phase boxes with the signs and order of the three analytic rows. -/
def aSectorAnalyticRowBoxes77 : List (List ℕ × PhaseCandidateQuintuple11) :=
  [([32, 18, 31, 38, 3], (47, 72, 37, 51, 57)),
   ([30, 12, 5, 26, 2], (27, 60, 41, 54, 64)),
   ([20, 8, 29, 34, 27], (23, 77, 70, 32, 30))]

def phaseCandidateIndicesList77 : PhaseCandidateQuintuple11 → List ℕ
  | (ia, ic, ie, ig, ij) => [ia, ic, ie, ig, ij]

def phaseCirclePairsList77 (x : PhaseCoords11) : List (ℝ × ℝ) :=
  [(x.a, x.b), (x.c, x.d), (x.e, x.f), (x.g, x.h), (x.j, x.k)]

theorem aSectorAnalyticRowBoxes77_rows :
    aSectorAnalyticRowBoxes77.map Prod.fst = aSectorPhaseExponents := by
  rfl

theorem aSectorAnalyticRowBoxes77_index_certificate :
    ∀ p ∈ aSectorAnalyticRowBoxes77,
      List.Forall₂ (fun i e => i < 160 ∧ e ∈ aSectorPhaseExponents.flatten ∧
        i / 4 = aSectorAnalyticRootIndex77 e)
        (phaseCandidateIndicesList77 p.2) p.1 := by
  native_decide

theorem aSectorAnalyticRowBoxes77_accepted_certificate :
    ∀ p ∈ aSectorAnalyticRowBoxes77,
      p.2 ∈ acceptedCandidateQuintuples ∧
        p.2 ∈ aSectorCandidateOrbitRepresentatives11.flatMap candidateSymmetryOrbit11 := by
  native_decide

private theorem phaseCirclePairsList77_close_to_box
    (s : PhaseSolution11) (q : PhaseCandidateQuintuple11)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 q) :
    List.Forall₂ (fun p i => p.1 ^ 2 + p.2 ^ 2 = 1 ∧
      p150KR11.IsRoot p.2 ∧
        |p.2 - centerCoordR (phaseCenters160[i]!).im| < 1 / 10000)
      (phaseCirclePairsList77 s.1) (phaseCandidateIndicesList77 q) := by
  rcases q with ⟨ia, ic, ie, ig, ij⟩
  rcases s.2.1 with ⟨hca, hcc, hce, hcg, hcj⟩
  rcases phaseSolution_imaginary_p150_roots11 s with ⟨hrb, hrd, hrf, hrh, hrk⟩
  rcases hbox with ⟨_, hb, _, hd, _, hf, _, hh, _, hk⟩
  exact .cons ⟨hca, hrb, hb⟩ (.cons ⟨hcc, hrd, hd⟩
    (.cons ⟨hce, hrf, hf⟩ (.cons ⟨hcg, hrh, hh⟩ (.cons ⟨hcj, hrk, hk⟩ .nil))))

private theorem phaseCirclePairsList77_match_analytic
    (ps : List (ℝ × ℝ)) (indices es : List ℕ)
    (hphase : List.Forall₂ (fun p i => p.1 ^ 2 + p.2 ^ 2 = 1 ∧
      p150KR11.IsRoot p.2 ∧
        |p.2 - centerCoordR (phaseCenters160[i]!).im| < 1 / 10000) ps indices)
    (hindices : List.Forall₂ (fun i e => i < 160 ∧ e ∈ aSectorPhaseExponents.flatten ∧
      i / 4 = aSectorAnalyticRootIndex77 e) indices es) :
    ps.map (fun p => 4 * p.2 ^ 2) = es.map analyticASectorCoordinate := by
  induction hindices generalizing ps with
  | nil => cases hphase; rfl
  | @cons i e indices es hindex htail ih =>
    cases hphase with
    | cons hp hptail =>
      simp only [List.map_cons]
      congr 1
      · exact phasePair_eq_analyticCoordinate_of_displayedExponent77
          e hindex.2.1 ⟨i, hindex.1⟩ hindex.2.2
            _ _ hp.1 hp.2.1 hp.2.2
      · exact ih _ hptail

/-- The five squared coordinates in each certified phase box equal
the displayed analytic conductor-77 row at `exp(2πi/77)`. -/
theorem phaseSolution_in_phaseBox_analytic_row77
    (p : List ℕ × PhaseCandidateQuintuple11)
    (hp : p ∈ aSectorAnalyticRowBoxes77)
    (s : PhaseSolution11)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 p.2) :
    [4 * s.1.b ^ 2, 4 * s.1.d ^ 2, 4 * s.1.f ^ 2,
     4 * s.1.h ^ 2, 4 * s.1.k ^ 2] = p.1.map analyticASectorCoordinate := by
  exact phaseCirclePairsList77_match_analytic
    (phaseCirclePairsList77 s.1) (phaseCandidateIndicesList77 p.2) p.1
      (phaseCirclePairsList77_close_to_box s p.2 hbox)
      (aSectorAnalyticRowBoxes77_index_certificate p hp)

set_option maxRecDepth 2048 in
/-- Every displayed analytic row is realized by an actual A-sector phase
solution, with the specified coordinate order. -/
theorem every_aSector_analytic_row_realized77
    (row : List ℕ) (hrow : row ∈ aSectorPhaseExponents) :
    ∃ s : PhaseSolution11,
      invariantAR.IsRoot (phaseInvariantU11 s.1) ∧
      [4 * s.1.b ^ 2, 4 * s.1.d ^ 2, 4 * s.1.f ^ 2,
       4 * s.1.h ^ 2, 4 * s.1.k ^ 2] = row.map analyticASectorCoordinate := by
  rw [← aSectorAnalyticRowBoxes77_rows] at hrow
  obtain ⟨p, hp, hprow⟩ := List.mem_map.mp hrow
  obtain ⟨haccepted, horbit⟩ := aSectorAnalyticRowBoxes77_accepted_certificate p hp
  obtain ⟨s, hbox⟩ := everyAcceptedPhaseBox_realized11 ⟨p.2, haccepted⟩
  obtain ⟨r, hr, hq⟩ := List.mem_flatMap.mp horbit
  refine ⟨s, phaseSolution_invariantA_of_taggedBox11 s r p.2 hr hq hbox, ?_⟩
  rw [← hprow]
  exact phaseSolution_in_phaseBox_analytic_row77 p hp s hbox

end Biunimodular.F11
