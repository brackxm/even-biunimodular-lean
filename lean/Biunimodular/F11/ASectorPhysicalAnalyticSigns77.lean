/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPhysicalAnalyticRows77

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11

/-- Boolean sign convention used by the phase table. -/
def phaseSign77 (b : Bool) : ℝ := if b then 1 else -1

def phaseSignedCenterQ77 (b : Bool) (n : ℤ) : ℚ :=
  if b then centerCoordQ11 n else -centerCoordQ11 n

/-- The explicit phase formula at the specified analytic embedding. -/
noncomputable def analyticASectorPhasePair77 (e : ℕ) (signs : Bool × Bool) : ℝ × ℝ :=
  (phaseSign77 signs.1 * Real.sqrt (4 - analyticASectorCoordinate e) / 2,
   phaseSign77 signs.2 * Real.sqrt (analyticASectorCoordinate e) / 2)

/-- Exact rational center bounds certify both signs in every displayed row. -/
theorem aSectorAnalyticRowSigns77_certificate :
    ∀ r : Fin 3,
      List.Forall₂ (fun i es => i < 160 ∧
        es.1 ∈ aSectorPhaseExponents.flatten ∧
        i / 4 = aSectorAnalyticRootIndex77 es.1 ∧
        (1 / 10000 : ℚ) < phaseSignedCenterQ77 es.2.1 (phaseCenters160[i]!).re ∧
        (1 / 10000 : ℚ) < phaseSignedCenterQ77 es.2.2 (phaseCenters160[i]!).im)
        (phaseCandidateIndicesList77 (aSectorAnalyticRowBoxes77[r.1]!).2)
        ((aSectorPhaseExponents[r.1]!).zip (aSectorPhaseSigns[r.1]!)) := by
  native_decide

private theorem phase_sign_of_center77 (b : Bool) (n : ℤ) (x : ℝ)
    (hcenter : (1 / 10000 : ℚ) < phaseSignedCenterQ77 b n)
    (hclose : |x - centerCoordR n| < 1 / 10000) :
    0 < phaseSign77 b * x := by
  have hc : (1 / 10000 : ℝ) < (phaseSignedCenterQ77 b n : ℝ) := by
    have h := Rat.cast_lt (K := ℝ).mpr hcenter
    norm_num at h ⊢
    exact h
  have hb := abs_lt.mp hclose
  cases b <;>
    simp [phaseSignedCenterQ77, centerCoordQ11, centerCoordR, phaseSign77] at hc hb ⊢ <;>
    linarith

/-- On a unit circle, the squared imaginary coordinate and two signs
uniquely determine the displayed square-root formula. -/
theorem phasePair_eq_signed_sqrt77 (u v X : ℝ) (signs : Bool × Bool)
    (hc : u ^ 2 + v ^ 2 = 1) (hX : 4 * v ^ 2 = X)
    (hu : 0 < phaseSign77 signs.1 * u) (hv : 0 < phaseSign77 signs.2 * v) :
    (u, v) = (phaseSign77 signs.1 * Real.sqrt (4 - X) / 2,
      phaseSign77 signs.2 * Real.sqrt X / 2) := by
  have hr : 4 - X = (2 * u) ^ 2 := by nlinarith
  have hi : X = (2 * v) ^ 2 := by nlinarith
  rw [hr, hi, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  apply Prod.ext
  · cases h : signs.1 <;> simp [phaseSign77, h] at hu ⊢
    · rw [abs_of_neg hu]; ring
    · rw [abs_of_pos hu]
  · cases h : signs.2 <;> simp [phaseSign77, h] at hv ⊢
    · rw [abs_of_neg hv]; ring
    · rw [abs_of_pos hv]

private theorem phaseCirclePairsList77_close_both
    (s : PhaseSolution11) (q : PhaseCandidateQuintuple11)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 q) :
    List.Forall₂ (fun p i => p.1 ^ 2 + p.2 ^ 2 = 1 ∧
      p150KR11.IsRoot p.2 ∧
      |p.1 - centerCoordR (phaseCenters160[i]!).re| < 1 / 10000 ∧
      |p.2 - centerCoordR (phaseCenters160[i]!).im| < 1 / 10000)
      (phaseCirclePairsList77 s.1) (phaseCandidateIndicesList77 q) := by
  rcases q with ⟨ia, ic, ie, ig, ij⟩
  rcases s.2.1 with ⟨hca, hcc, hce, hcg, hcj⟩
  rcases phaseSolution_imaginary_p150_roots11 s with ⟨hrb, hrd, hrf, hrh, hrk⟩
  rcases hbox with ⟨ha, hb, hc, hd, he, hf, hg, hh, hj, hk⟩
  exact .cons ⟨hca, hrb, ha, hb⟩ (.cons ⟨hcc, hrd, hc, hd⟩
    (.cons ⟨hce, hrf, he, hf⟩ (.cons ⟨hcg, hrh, hg, hh⟩ (.cons ⟨hcj, hrk, hj, hk⟩ .nil))))

private theorem phaseCirclePairsList77_match_signed
    (ps : List (ℝ × ℝ)) (indices : List ℕ) (es : List (ℕ × (Bool × Bool)))
    (hphase : List.Forall₂ (fun p i => p.1 ^ 2 + p.2 ^ 2 = 1 ∧
      p150KR11.IsRoot p.2 ∧
      |p.1 - centerCoordR (phaseCenters160[i]!).re| < 1 / 10000 ∧
      |p.2 - centerCoordR (phaseCenters160[i]!).im| < 1 / 10000) ps indices)
    (hindices : List.Forall₂ (fun i es => i < 160 ∧
      es.1 ∈ aSectorPhaseExponents.flatten ∧ i / 4 = aSectorAnalyticRootIndex77 es.1 ∧
      (1 / 10000 : ℚ) < phaseSignedCenterQ77 es.2.1 (phaseCenters160[i]!).re ∧
      (1 / 10000 : ℚ) < phaseSignedCenterQ77 es.2.2 (phaseCenters160[i]!).im)
        indices es) :
    ps = es.map (fun es => analyticASectorPhasePair77 es.1 es.2) := by
  induction hindices generalizing ps with
  | nil => cases hphase; rfl
  | @cons i es indices tail hindex htail ih =>
    cases hphase with
    | cons hp hptail =>
      simp only [List.map_cons]
      congr 1
      · exact phasePair_eq_signed_sqrt77 _ _ _ _ hp.1
          (phasePair_eq_analyticCoordinate_of_displayedExponent77
            es.1 hindex.2.1 ⟨i, hindex.1⟩ hindex.2.2.1 _ _ hp.1 hp.2.1 hp.2.2.2)
          (phase_sign_of_center77 _ _ _ hindex.2.2.2.1 hp.2.2.1)
          (phase_sign_of_center77 _ _ _ hindex.2.2.2.2 hp.2.2.2)
      · exact ih _ hptail

/-- Every solution in a certified phase box has exactly the displayed analytic
phases, including the real and imaginary signs. -/
theorem phaseSolution_in_phaseBox_signed_analytic_row77
    (r : Fin 3) (s : PhaseSolution11)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1
      (aSectorAnalyticRowBoxes77[r.1]!).2) :
    phaseCirclePairsList77 s.1 =
      ((aSectorPhaseExponents[r.1]!).zip (aSectorPhaseSigns[r.1]!)).map
        (fun es => analyticASectorPhasePair77 es.1 es.2) := by
  exact phaseCirclePairsList77_match_signed _ _ _
    (phaseCirclePairsList77_close_both s _ hbox)
    (aSectorAnalyticRowSigns77_certificate r)

/-- The five explicit analytic phase pairs in one displayed row. -/
noncomputable def analyticASectorPhaseRow77 (r : Fin 3) : List (ℝ × ℝ) :=
  ((aSectorPhaseExponents[r.1]!).zip (aSectorPhaseSigns[r.1]!)).map
    (fun es => analyticASectorPhasePair77 es.1 es.2)

/-- The the analytic representative, in the original ten real coordinates. -/
noncomputable def analyticASectorRepresentative77 (r : Fin 3) : PhaseCoords11 :=
  let ps := analyticASectorPhaseRow77 r
  ⟨ps[0]!.1, ps[0]!.2, ps[1]!.1, ps[1]!.2, ps[2]!.1, ps[2]!.2,
   ps[3]!.1, ps[3]!.2, ps[4]!.1, ps[4]!.2⟩

theorem analyticASectorRepresentative77_pairs (r : Fin 3) :
    phaseCirclePairsList77 (analyticASectorRepresentative77 r) =
      analyticASectorPhaseRow77 r := by
  fin_cases r <;> rfl

theorem phaseCirclePairsList77_injective : Function.Injective phaseCirclePairsList77 := by
  intro x y h
  cases x
  cases y
  simpa [phaseCirclePairsList77, List.cons.injEq, Prod.mk.injEq, and_assoc] using h

/-- The explicit conductor-77 formulas, with the displayed signs, solve all
ten circle/phase equations and have an A-sector invariant. -/
theorem analyticASectorRepresentative77_isPhaseSolution (r : Fin 3) :
    (analyticASectorRepresentative77 r).IsPhaseSolution ∧
      invariantAR.IsRoot (phaseInvariantU11 (analyticASectorRepresentative77 r)) := by
  have hp : aSectorAnalyticRowBoxes77[r.1]! ∈ aSectorAnalyticRowBoxes77 := by
    fin_cases r <;> decide
  obtain ⟨haccepted, horbit⟩ :=
    aSectorAnalyticRowBoxes77_accepted_certificate _ hp
  obtain ⟨s, hbox⟩ := everyAcceptedPhaseBox_realized11 ⟨_, haccepted⟩
  have hs : s.1 = analyticASectorRepresentative77 r := by
    apply phaseCirclePairsList77_injective
    rw [analyticASectorRepresentative77_pairs]
    exact phaseSolution_in_phaseBox_signed_analytic_row77 r s hbox
  obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.mp horbit
  have hA := phaseSolution_invariantA_of_taggedBox11 s q _ hq hmem hbox
  rw [← hs]
  exact ⟨s.2, hA⟩

end Biunimodular.F11
