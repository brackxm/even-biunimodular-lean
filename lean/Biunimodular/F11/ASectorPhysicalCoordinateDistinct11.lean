/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorAnalyticCoordinateDistinct77

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Biunimodular.F11

/-- Imaginary center coordinates of an accepted phase box, in the scanner's
exact integer scale. -/
def aSectorBoxImagCenters11 : PhaseCandidateQuintuple11 → List ℤ
  | (ia, ic, ie, ig, ij) =>
      [(phaseCenters160[ia]!).im, (phaseCenters160[ic]!).im,
       (phaseCenters160[ie]!).im, (phaseCenters160[ig]!).im,
       (phaseCenters160[ij]!).im]

/-- The five A-sector centers in every symmetry box have separated absolute
values, with more than twice the box radius as margin. -/
theorem aSectorBoxImagCenters11_pairwise_separated :
    ∀ r ∈ aSectorCandidateOrbitRepresentatives11,
      ∀ q ∈ candidateSymmetryOrbit11 r,
        (aSectorBoxImagCenters11 q).Pairwise
          (fun a b =>
            (20000000000 : ℤ) < |a - b| ∧
              (20000000000 : ℤ) < |a + b|) := by
  native_decide

private theorem centerCoordR_separated_sq
    (a b : ℤ) (y z : ℝ)
    (hy : |y - centerCoordR a| < 1 / 10000)
    (hz : |z - centerCoordR b| < 1 / 10000)
    (hab : (20000000000 : ℤ) < |a - b| ∧
      (20000000000 : ℤ) < |a + b|) :
    y ^ 2 ≠ z ^ 2 := by
  have hsubInt : (20000000000 : ℝ) < |(a : ℝ) - (b : ℝ)| := by
    exact_mod_cast hab.1
  have haddInt : (20000000000 : ℝ) < |(a : ℝ) + (b : ℝ)| := by
    exact_mod_cast hab.2
  have hsub : (2 / 10000 : ℝ) < |centerCoordR a - centerCoordR b| := by
    calc
      (2 / 10000 : ℝ) = (20000000000 : ℝ) / 100000000000000 := by norm_num
      _ < |(a : ℝ) - (b : ℝ)| / 100000000000000 := by
        gcongr
      _ = |centerCoordR a - centerCoordR b| := by
        simp only [centerCoordR, phaseCenterScale]
        rw [← sub_div, abs_div]
        norm_num
  have hadd : (2 / 10000 : ℝ) < |centerCoordR a + centerCoordR b| := by
    calc
      (2 / 10000 : ℝ) = (20000000000 : ℝ) / 100000000000000 := by norm_num
      _ < |(a : ℝ) + (b : ℝ)| / 100000000000000 := by
        gcongr
      _ = |centerCoordR a + centerCoordR b| := by
        simp only [centerCoordR, phaseCenterScale]
        rw [← add_div, abs_div]
        norm_num
  intro hsquare
  have hfactor : (y - z) * (y + z) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · have htriangle : |centerCoordR a - centerCoordR b| ≤
        |y - centerCoordR a| + |z - centerCoordR b| := by
      have heq : centerCoordR a - centerCoordR b =
          -(y - centerCoordR a) + (z - centerCoordR b) := by
        rw [sub_eq_zero.mp h]
        ring
      rw [heq]
      simpa only [abs_neg] using
        abs_add_le (-(y - centerCoordR a)) (z - centerCoordR b)
    linarith
  · have htriangle : |centerCoordR a + centerCoordR b| ≤
        |y - centerCoordR a| + |z - centerCoordR b| := by
      have heq : centerCoordR a + centerCoordR b =
          -(y - centerCoordR a) - (z - centerCoordR b) := by
        have hyz : y = -z := by linarith
        rw [hyz]
        ring
      rw [heq]
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (-(y - centerCoordR a)) (-(z - centerCoordR b))
    linarith

/-- Within every physical A-sector solution, the five squared imaginary
coordinates are pairwise distinct. -/
theorem everyASectorPhase_squaredCoordinates_nodup11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ([s.1.b, s.1.d, s.1.f, s.1.h, s.1.k].map
      (fun y : ℝ => y ^ 2)).Nodup := by
  obtain ⟨r, hr, q, hq, hbox⟩ := everyASectorPhase_in_taggedBox11 s hA
  obtain ⟨ia, ic, ie, ig, ij⟩ := q
  have hsep := aSectorBoxImagCenters11_pairwise_separated r hr
    (ia, ic, ie, ig, ij) hq
  simp only [aSectorBoxImagCenters11, List.pairwise_cons,
    List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp] at hsep
  simp only [phaseCandidateQuintupleBox11] at hbox
  rcases hbox with ⟨_, hb, _, hd, _, hf, _, hh, _, hk⟩
  have hbd : s.1.b ^ 2 ≠ s.1.d ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hb hd (by aesop)
  have hbf : s.1.b ^ 2 ≠ s.1.f ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hb hf (by aesop)
  have hbh : s.1.b ^ 2 ≠ s.1.h ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hb hh (by aesop)
  have hbk : s.1.b ^ 2 ≠ s.1.k ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hb hk (by aesop)
  have hdf : s.1.d ^ 2 ≠ s.1.f ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hd hf (by aesop)
  have hdh : s.1.d ^ 2 ≠ s.1.h ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hd hh (by aesop)
  have hdk : s.1.d ^ 2 ≠ s.1.k ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hd hk (by aesop)
  have hfh : s.1.f ^ 2 ≠ s.1.h ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hf hh (by aesop)
  have hfk : s.1.f ^ 2 ≠ s.1.k ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hf hk (by aesop)
  have hhk : s.1.h ^ 2 ≠ s.1.k ^ 2 :=
    centerCoordR_separated_sq _ _ _ _ hh hk (by aesop)
  simp only [List.map_cons, List.map_nil, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or]
  aesop

/-- The five coordinates of a physical A-sector phase have five distinct
canonical analytic exponents. -/
theorem everyASectorPhase_five_distinct_analyticExponents11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∃ es : List ℕ,
      es.length = 5 ∧ es.Nodup ∧
        (∀ e ∈ es, e ∈ aSectorCanonicalAnalyticExponents77) ∧
        es.map analyticASectorCoordinate =
          [4 * s.1.b ^ 2, 4 * s.1.d ^ 2, 4 * s.1.f ^ 2,
           4 * s.1.h ^ 2, 4 * s.1.k ^ 2] := by
  have hmem (y : ℝ)
      (hy : y ∈ [s.1.b, s.1.d, s.1.f, s.1.h, s.1.k]) :=
    everyASectorPhase_coordinate_in_analyticThirty s hA y hy
  obtain ⟨eb, heb, hb⟩ := hmem s.1.b (by simp)
  obtain ⟨ed, hed, hd⟩ := hmem s.1.d (by simp)
  obtain ⟨ef, hef, hf⟩ := hmem s.1.f (by simp)
  obtain ⟨eh, heh, hh⟩ := hmem s.1.h (by simp)
  obtain ⟨ek, hek, hk⟩ := hmem s.1.k (by simp)
  let es : List ℕ := [eb, ed, ef, eh, ek]
  have hmap : es.map analyticASectorCoordinate =
      [4 * s.1.b ^ 2, 4 * s.1.d ^ 2, 4 * s.1.f ^ 2,
       4 * s.1.h ^ 2, 4 * s.1.k ^ 2] := by
    simp only [es, List.map_cons, List.map_nil]
    simp only [hb, hd, hf, hh, hk]
  have hscaled :
      ([4 * s.1.b ^ 2, 4 * s.1.d ^ 2, 4 * s.1.f ^ 2,
        4 * s.1.h ^ 2, 4 * s.1.k ^ 2] : List ℝ).Nodup := by
    have hsq := everyASectorPhase_squaredCoordinates_nodup11 s hA
    have hmul : Function.Injective (fun x : ℝ => 4 * x) := by
      intro x y hxy
      nlinarith
    have h := hsq.map hmul
    simpa only [List.map_cons, List.map_nil] using h
  refine ⟨es, by simp [es], ?_, ?_, hmap⟩
  · rw [← hmap] at hscaled
    exact hscaled.of_map
  · intro e he
    simp only [es, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    all_goals assumption

end Biunimodular.F11
