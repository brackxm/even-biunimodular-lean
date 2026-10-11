/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorAnalyticApproximation77
import Biunimodular.F11.ASectorPhysicalRootCount11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

/-- Exact root-interval indices for the fifteen displayed analytic exponents. -/
def aSectorAnalyticRootIndexTable77 : List (ℕ × ℕ) :=
  [(32, 11), (18, 18), (31, 9), (38, 12), (3, 14),
   (30, 6), (12, 15), (5, 10), (26, 13), (2, 16),
   (20, 5), (8, 19), (29, 17), (34, 8), (27, 7)]

def aSectorAnalyticRootIndex77 (e : ℕ) : ℕ :=
  ((aSectorAnalyticRootIndexTable77.find? (fun p => decide (p.1 = e))).getD (0, 0)).2

/-- Rational Taylor evaluation selects one root interval for each exponent;
the certified error window excludes all the other physical intervals. -/
theorem aSectorAnalyticRootIndex77_rational_certificate :
    ∀ e ∈ aSectorPhaseExponents.flatten,
      let a := analyticASectorCoordinateApproxQ77 e
      let ε : ℚ := 1 / 10 ^ 10
      e ∈ aSectorCanonicalAnalyticExponents77 ∧
        aSectorAnalyticRootIndex77 e < 40 ∧
        0 < a - ε ∧ a + ε < 4 ∧
        ∀ i : Fin 40, i ∈ p150FactorRootIndices11 .f30 →
          i.1 ≠ aSectorAnalyticRootIndex77 e →
          4 * (squaredKRootIntervals40[i.1]!).box.hi < a - ε ∨
            a + ε < 4 * (squaredKRootIntervals40[i.1]!).box.lo := by
  native_decide

/-- Each displayed exponent is physical and lies in its specified exact
F30 isolating interval at the analytic embedding `exp(2πi/77)`. -/
theorem analyticASectorCoordinate_displayed_root_interval77
    (e : ℕ) (he : e ∈ aSectorPhaseExponents.flatten) :
    0 < analyticASectorCoordinate e ∧ analyticASectorCoordinate e < 4 ∧
      (((squaredKRootIntervals40[aSectorAnalyticRootIndex77 e]!).box.lo : ℝ) ≤
        analyticASectorCoordinate e / 4 ∧
       analyticASectorCoordinate e / 4 ≤
        ((squaredKRootIntervals40[aSectorAnalyticRootIndex77 e]!).box.hi : ℝ)) ∧
      (p150FactorPolynomialR11 .f30).IsRoot (analyticASectorCoordinate e / 4) := by
  obtain ⟨hc, _, hlo, hhi, hexclude⟩ :=
    aSectorAnalyticRootIndex77_rational_certificate e he
  have herror := abs_le.mp (analyticASectorCoordinateApproxQ77_error e)
  have hloR : 0 < (analyticASectorCoordinateApproxQ77 e : ℝ) - 1 / 10 ^ 10 := by
    have h := Rat.cast_lt (K := ℝ).mpr hlo
    norm_num at h ⊢
    exact h
  have hhiR : (analyticASectorCoordinateApproxQ77 e : ℝ) + 1 / 10 ^ 10 < 4 := by
    have h := Rat.cast_lt (K := ℝ).mpr hhi
    norm_num at h ⊢
    exact h
  have hx0 : 0 < analyticASectorCoordinate e := by linarith
  have hx4 : analyticASectorCoordinate e < 4 := by linarith
  obtain ⟨s, hA, hcoord⟩ :=
    (analyticASectorCoordinate_physical_iff11 e hc).mp ⟨hx0.le, hx4.le⟩
  obtain ⟨r, hr, q, hq, hbox⟩ := everyASectorPhase_in_taggedBox11 s hA
  have hroot := phaseSolution_f30_of_aSectorCandidateBox s r q hr hq hbox
  have hy1 : s.1.k ^ 2 ≤ 1 := by
    have hcircle := s.2.1.2.2.2.2
    nlinarith [sq_nonneg s.1.j]
  obtain ⟨i, hi, hibox⟩ := p150FactorPolynomialR11_root_in_interval .f30
    (s.1.k ^ 2) (sq_nonneg _) hy1 hroot
  have hindex : i.1 = aSectorAnalyticRootIndex77 e := by
    by_contra hne
    rcases hexclude i hi hne with hsep | hsep
    · have hsepR : 4 * ((squaredKRootIntervals40[i.1]!).box.hi : ℝ) <
          (analyticASectorCoordinateApproxQ77 e : ℝ) - 1 / 10 ^ 10 := by
        have h := Rat.cast_lt (K := ℝ).mpr hsep
        norm_num at h ⊢
        exact h
      linarith [hibox.2]
    · have hsepR : (analyticASectorCoordinateApproxQ77 e : ℝ) + 1 / 10 ^ 10 <
          4 * ((squaredKRootIntervals40[i.1]!).box.lo : ℝ) := by
        have h := Rat.cast_lt (K := ℝ).mpr hsep
        norm_num at h ⊢
        exact h
      linarith [hibox.1]
  have hsquare : s.1.k ^ 2 = analyticASectorCoordinate e / 4 := by linarith
  refine ⟨hx0, hx4, ?_, ?_⟩
  · simpa only [hindex, hsquare] using hibox
  · rw [← hsquare]
    exact hroot

theorem aSectorAnalyticRootIndex77_tag :
    ∀ e ∈ aSectorPhaseExponents.flatten,
      (squaredKRootIntervals40[aSectorAnalyticRootIndex77 e]!).factor = .f30 := by
  native_decide

/-- An actual unit-circle phase near the recorded center has exactly the
displayed analytic squared coordinate, at the specified complex embedding. -/
theorem phasePair_eq_analyticCoordinate_of_displayedExponent77
    (e : ℕ) (he : e ∈ aSectorPhaseExponents.flatten)
    (i : Fin 160) (hindex : i.1 / 4 = aSectorAnalyticRootIndex77 e)
    (u v : ℝ) (hcircle : u ^ 2 + v ^ 2 = 1)
    (hroot : p150KR11.IsRoot v)
    (hclose : |v - centerCoordR (phaseCenters160[i.1]!).im| < 1 / 10000) :
    4 * v ^ 2 = analyticASectorCoordinate e := by
  have hphase := phasePair_tagged_factor_root11 u v i hcircle hroot hclose
  have hanalytic := analyticASectorCoordinate_displayed_root_interval77 e he
  let q := phaseCenterIntervalIndex11 i
  have hq : q.1 = aSectorAnalyticRootIndex77 e := hindex
  have habox : ((squaredKRootIntervals40[q.1]!).box.lo : ℝ) ≤
      analyticASectorCoordinate e / 4 ∧
      analyticASectorCoordinate e / 4 ≤
        ((squaredKRootIntervals40[q.1]!).box.hi : ℝ) := by
    simpa only [hq] using hanalytic.2.2.1
  have haroot : (p150FactorPolynomialR11
      (squaredKRootIntervals40[q.1]!).factor).IsRoot
        (analyticASectorCoordinate e / 4) := by
    rw [hq, aSectorAnalyticRootIndex77_tag e he]
    exact hanalytic.2.2.2
  have heq := p150FactorPolynomialR11_root_unique_in_interval q
    (v ^ 2) (analyticASectorCoordinate e / 4)
      hphase.2.1 hphase.2.2 habox.1 habox.2 hphase.1 haroot
  nlinarith

end Biunimodular.F11
