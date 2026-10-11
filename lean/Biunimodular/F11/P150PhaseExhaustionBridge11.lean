/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.FinitePhaseExhaustionCore
public import Biunimodular.F11.PhaseCandidateSymmetry11
public import Biunimodular.F11.PhaseSymmetry11
public import Biunimodular.F11.TailLinearSystemStd

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# P150 root cover to the exact F11 finite scan

The exact `P150` root-cover certificate eliminates the final imaginary coordinate
`k`.  Together with the circle equation, its isolated real roots give one of
the 160 fixed-point phase boxes for `(j,k)`.  Dilation symmetry then supplies
the same cover for the other four phase pairs.

This file defines the root-cover certificate and proves the subsequent
finite-exhaustion assembly. The concrete certificate is supplied in
`P150RootIsolation11`.  In particular, every actual phase
solution is forced into one of the 80 tuples accepted by the exact native
scan.
-/

/-- Radius of the certified fixed-point phase centers. -/
noncomputable def p150PhaseRootRadius11 : ℝ := 1 / 200000000000000

/-- A real phase pair lies in the fixed-point box with index `i`. -/
def closePhaseCandidate11 (δ x y : ℝ) (i : Fin 160) : Prop :=
  |x - centerCoordR (phaseCenters160[i.1]!).re| ≤ δ ∧
  |y - centerCoordR (phaseCenters160[i.1]!).im| ≤ δ

/-- The root-cover property of the `P150`
coordinate eliminant and its real-root isolation data.

Only the final phase `(j,k)` occurs here.  The other four phase pairs follow
from the order-five dilation already formalized in `PhaseSymmetry11`.
-/
structure P150KRootCoverCertificate11 where
  cover_last : ∀ (x : PhaseCoords11), x.IsPhaseSolution →
    ∃ i : Fin 160, closePhaseCandidate11 p150PhaseRootRadius11 x.j x.k i

/-- One `P150` cover theorem for `(j,k)` covers all five phase pairs after
applying the five powers of dilation. -/
theorem P150KRootCoverCertificate11.all_phase_pairs_covered
    (C : P150KRootCoverCertificate11)
    (x : PhaseCoords11) (hx : x.IsPhaseSolution) :
    ∃ ia ic ie ig ij : Fin 160,
      closeFirstThreeCandidates p150PhaseRootRadius11
        x.a x.b x.c x.d x.e x.f ia ic ie ∧
      closeTailCandidates p150PhaseRootRadius11 x.g x.h x.j x.k ig ij := by
  have hx1 : (phaseDilate11 x).IsPhaseSolution :=
    (phaseDilate11_isPhaseSolution_iff x).2 hx
  have hx2 : (phaseDilate11 (phaseDilate11 x)).IsPhaseSolution :=
    (phaseDilate11_isPhaseSolution_iff (phaseDilate11 x)).2 hx1
  have hx3 :
      (phaseDilate11 (phaseDilate11 (phaseDilate11 x))).IsPhaseSolution :=
    (phaseDilate11_isPhaseSolution_iff
      (phaseDilate11 (phaseDilate11 x))).2 hx2
  have hx4 :
      (phaseDilate11
        (phaseDilate11 (phaseDilate11 (phaseDilate11 x)))).IsPhaseSolution :=
    (phaseDilate11_isPhaseSolution_iff
      (phaseDilate11 (phaseDilate11 (phaseDilate11 x)))).2 hx3
  obtain ⟨ij, hij⟩ := C.cover_last x hx
  obtain ⟨ia, hia⟩ := C.cover_last (phaseDilate11 x) hx1
  obtain ⟨ic, hic⟩ := C.cover_last
    (phaseDilate11 (phaseDilate11 x)) hx2
  obtain ⟨ig, hig⟩ := C.cover_last
    (phaseDilate11 (phaseDilate11 (phaseDilate11 x))) hx3
  obtain ⟨ie, hie⟩ := C.cover_last
    (phaseDilate11
      (phaseDilate11 (phaseDilate11 (phaseDilate11 x)))) hx4
  rcases hia with ⟨hiaRe, hiaIm⟩
  rcases hic with ⟨hicRe, hicIm⟩
  rcases hie with ⟨hieRe, hieIm⟩
  rcases hig with ⟨higRe, higIm⟩
  rcases hij with ⟨hijRe, hijIm⟩
  change |x.a - centerCoordR (phaseCenters160[ia.1]!).re| ≤ _ at hiaRe
  change |x.b - centerCoordR (phaseCenters160[ia.1]!).im| ≤ _ at hiaIm
  change |x.c - centerCoordR (phaseCenters160[ic.1]!).re| ≤ _ at hicRe
  change |x.d - centerCoordR (phaseCenters160[ic.1]!).im| ≤ _ at hicIm
  change |x.e - centerCoordR (phaseCenters160[ie.1]!).re| ≤ _ at hieRe
  change |x.f - centerCoordR (phaseCenters160[ie.1]!).im| ≤ _ at hieIm
  change |x.g - centerCoordR (phaseCenters160[ig.1]!).re| ≤ _ at higRe
  change |x.h - centerCoordR (phaseCenters160[ig.1]!).im| ≤ _ at higIm
  change |x.j - centerCoordR (phaseCenters160[ij.1]!).re| ≤ _ at hijRe
  change |x.k - centerCoordR (phaseCenters160[ij.1]!).im| ≤ _ at hijIm
  refine ⟨ia, ic, ie, ig, ij, ?_, ?_⟩
  · unfold closeFirstThreeCandidates close6
    exact ⟨hiaRe, hiaIm, hicRe, hicIm, hieRe, hieIm⟩
  · unfold closeTailCandidates
    exact ⟨higRe, higIm, hijRe, hijIm⟩

private theorem abs_coordinates_le_one
    (x : PhaseCoords11) (hx : x.CircleEquations) :
    unit6 x.a x.b x.c x.d x.e x.f ∧
      |x.g| ≤ 1 ∧ |x.h| ≤ 1 ∧ |x.j| ≤ 1 ∧ |x.k| ≤ 1 := by
  rcases hx with ⟨hab, hcd, hef, hgh, hjk⟩
  have ha2 : x.a ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.b]
  have hb2 : x.b ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.a]
  have hc2 : x.c ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.d]
  have hd2 : x.d ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.c]
  have he2 : x.e ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.f]
  have hf2 : x.f ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.e]
  have hg2 : x.g ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.h]
  have hh2 : x.h ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.g]
  have hj2 : x.j ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.k]
  have hk2 : x.k ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.j]
  have ha := (sq_le_one_iff_abs_le_one x.a).mp ha2
  have hb := (sq_le_one_iff_abs_le_one x.b).mp hb2
  have hc := (sq_le_one_iff_abs_le_one x.c).mp hc2
  have hd := (sq_le_one_iff_abs_le_one x.d).mp hd2
  have he := (sq_le_one_iff_abs_le_one x.e).mp he2
  have hf := (sq_le_one_iff_abs_le_one x.f).mp hf2
  have hg := (sq_le_one_iff_abs_le_one x.g).mp hg2
  have hh := (sq_le_one_iff_abs_le_one x.h).mp hh2
  have hj := (sq_le_one_iff_abs_le_one x.j).mp hj2
  have hk := (sq_le_one_iff_abs_le_one x.k).mp hk2
  exact ⟨⟨ha, hb, hc, hd, he, hf⟩, hg, hh, hj, hk⟩

/-- **P150-to-80-box exhaustion.**

Once the single-coordinate `P150` root cover is available, every genuine
phase solution lies in a wide `10^-4` box around one of the 80 exact scanner
tuples.  Exceptional first-three tuples are ruled out by their rational
witnesses; regular tuples are reconstructed by the certified Cramer scan.
-/
theorem P150KRootCoverCertificate11.phase_solution_in_accepted_box
    (C : P150KRootCoverCertificate11) (s : PhaseSolution11) :
    ∃ q ∈ acceptedCandidateQuintuples,
      phaseCandidateQuintupleBox11 (1 / 10000) s.1 q := by
  let x := s.1
  have hx : x.IsPhaseSolution := s.2
  obtain ⟨ia, ic, ie, ig, ij, hfirst, htail⟩ :=
    C.all_phase_pairs_covered x hx
  have hδ : 0 ≤ p150PhaseRootRadius11 := by
    norm_num [p150PhaseRootRadius11]
  have hδsmall :
      p150PhaseRootRadius11 ≤ (1 / 200000000000000 : ℝ) := by
    rfl
  have hbounds := abs_coordinates_le_one x hx.1
  rcases hbounds with ⟨hu, hg, hh, hj, hk⟩
  have hsol :
      (tailMatrix x.a x.b x.c x.d x.e x.f).mulVec
          (tailVec x.g x.h x.j x.k) =
        tailRhs x.a x.b x.c x.d x.e x.f := by
    exact tail_linear_system_std_of_autocorr
      x.a x.b x.c x.d x.e x.f x.g x.h x.j x.k
      hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2
  cases hreg : exceptionalTriple ia.1 ic.1 ie.1 with
  | true =>
      exact False.elim <| exceptionalTriple_impossible_for_actual_solution
        ia ic ie hreg hδ hδsmall hfirst hu hg hh hj hk hsol
  | false =>
      obtain ⟨ig', ij', hscan, hmem, hgw, hhw, hjw, hkw⟩ :=
        regularTriple_scan_output_wide_capture ia ic ie ig ij hreg
          hδ hδsmall hfirst htail hu hg hh hj hk hsol
      refine ⟨(ia.1, ic.1, ie.1, ig', ij'), hmem, ?_⟩
      rcases hfirst with ⟨ha, hb, hc, hd, he, hf⟩
      simp only [phaseCandidateQuintupleBox11]
      have hwide : p150PhaseRootRadius11 < (1 / 10000 : ℝ) := by
        norm_num [p150PhaseRootRadius11]
      exact ⟨lt_of_le_of_lt ha hwide, lt_of_le_of_lt hb hwide,
        lt_of_le_of_lt hc hwide, lt_of_le_of_lt hd hwide,
        lt_of_le_of_lt he hwide, lt_of_le_of_lt hf hwide,
        hgw, hhw, hjw, hkw⟩

/-- Set-level form of the P150-to-scanner exhaustion theorem. -/
theorem P150KRootCoverCertificate11.phase_solution_set_subset_accepted_boxes
    (C : P150KRootCoverCertificate11) :
    Set.range (fun s : PhaseSolution11 => s.1) ⊆
      {x | ∃ q ∈ acceptedCandidateQuintuples,
        phaseCandidateQuintupleBox11 (1 / 10000) x q} := by
  rintro x ⟨s, rfl⟩
  exact C.phase_solution_in_accepted_box s

/-- Every genuine phase solution is captured by one of the ten boxes in one
of the eight exact candidate symmetry orbits. -/
theorem P150KRootCoverCertificate11.phase_solution_in_eight_candidate_orbits
    (C : P150KRootCoverCertificate11) (s : PhaseSolution11) :
    ∃ r ∈ acceptedCandidateOrbitRepresentatives11,
      ∃ q ∈ candidateSymmetryOrbit11 r,
        phaseCandidateQuintupleBox11 (1 / 10000) s.1 q := by
  obtain ⟨q, hq, hs⟩ := C.phase_solution_in_accepted_box s
  obtain ⟨r, hr, hqr⟩ := acceptedCandidate_mem_symmetry_orbit q hq
  exact ⟨r, hr, q, hqr, hs⟩

end Biunimodular.F11
