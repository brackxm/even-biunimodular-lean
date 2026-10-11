/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorF30PhysicalPolynomialBridge11
import Biunimodular.F11.PhaseInvariantOrbitSeparation11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

private def candidateCenterNumerator11 : PhaseCandidateQuintuple11 → ℤ
  | (ia, ic, ie, ig, ij) =>
    phaseCenterScale + 2 * (
      (phaseCenters160[ia]!).re + (phaseCenters160[ic]!).re +
      (phaseCenters160[ie]!).re + (phaseCenters160[ig]!).re +
      (phaseCenters160[ij]!).re)

private theorem candidateCenterNumerator_bounds11 :
    ∀ r ∈ aSectorCandidateOrbitRepresentatives11,
      r = (22, 76, 71, 33, 31) ∨
      r = (26, 61, 40, 55, 65) ∨
      r = (36, 56, 73, 46, 50) := by
  native_decide

private theorem phaseBox_numerator_close11
    (x : PhaseCoords11) (q : PhaseCandidateQuintuple11)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) x q) :
    |(1 + 2 * (x.a + x.c + x.e + x.g + x.j)) -
      (candidateCenterNumerator11 q : ℝ) / (phaseCenterScale : ℝ)| < 1/1000 := by
  rcases q with ⟨ia, ic, ie, ig, ij⟩
  rcases hbox with ⟨ha, _, hc, _, he, _, hg, _, hj, _⟩
  have ha' := abs_lt.mp ha
  have hc' := abs_lt.mp hc
  have he' := abs_lt.mp he
  have hg' := abs_lt.mp hg
  have hj' := abs_lt.mp hj
  have hcenter :
      (candidateCenterNumerator11 (ia, ic, ie, ig, ij) : ℝ) /
        (phaseCenterScale : ℝ) =
      1 + 2 * (centerCoordR (phaseCenters160[ia]!).re +
        centerCoordR (phaseCenters160[ic]!).re +
        centerCoordR (phaseCenters160[ie]!).re +
        centerCoordR (phaseCenters160[ig]!).re +
        centerCoordR (phaseCenters160[ij]!).re) := by
    simp only [candidateCenterNumerator11, centerCoordR]
    push_cast
    have hs : (phaseCenterScale : ℝ) = 100000000000000 := by rfl
    rw [hs]
    ring
  rw [hcenter]
  rw [abs_lt]
  constructor <;> linarith [ha', hc', he', hg', hj']

theorem aSectorRepresentativeBox_invariant_intervals11
    (s : PhaseSolution11) (r : PhaseCandidateQuintuple11)
    (hr : r ∈ aSectorCandidateOrbitRepresentatives11)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 r) :
    (r = (22, 76, 71, 33, 31) ∧
      (9/10 : ℝ) < phaseInvariantU11 s.1 ∧ phaseInvariantU11 s.1 < 93/100) ∨
    (r = (26, 61, 40, 55, 65) ∧
      (1/20 : ℝ) < phaseInvariantU11 s.1 ∧ phaseInvariantU11 s.1 < 1/10) ∨
    (r = (36, 56, 73, 46, 50) ∧
      (0 : ℝ) < phaseInvariantU11 s.1 ∧ phaseInvariantU11 s.1 < 1/50) := by
  have hb := candidateCenterNumerator_bounds11 r hr
  have hclose := abs_lt.mp (phaseBox_numerator_close11 s.1 r hbox)
  have hsqrt : (Real.sqrt 11) ^ 2 = 11 := by
    exact Real.sq_sqrt (by norm_num)
  have hu : phaseInvariantU11 s.1 =
      (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) ^ 2 / 11 := by
    rw [phaseInvariantU11, phaseInvariantQ11, div_pow, hsqrt]
  rcases hb with hb | hb | hb
  · left
    subst r
    have hc : (candidateCenterNumerator11 (22, 76, 71, 33, 31) : ℝ) /
        (phaseCenterScale : ℝ) = 318489039506530 / 100000000000000 := by
      norm_num [candidateCenterNumerator11, phaseCenters160, phaseCenterScale]
    rw [hc] at hclose
    refine ⟨rfl, ?_, ?_⟩
    · rw [hu]
      nlinarith [mul_pos
        (show (0 : ℝ) < (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) - 3183/1000 by linarith)
        (show (0 : ℝ) < (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) + 3183/1000 by linarith)]
    · rw [hu]
      nlinarith [mul_pos
        (show (0 : ℝ) < 3187/1000 - (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) by linarith)
        (show (0 : ℝ) < 3187/1000 + (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) by linarith)]
  · right; left
    subst r
    have hc : (candidateCenterNumerator11 (26, 61, 40, 55, 65) : ℝ) /
        (phaseCenterScale : ℝ) = 94656321017632 / 100000000000000 := by
      norm_num [candidateCenterNumerator11, phaseCenters160, phaseCenterScale]
    rw [hc] at hclose
    refine ⟨rfl, ?_, ?_⟩
    · rw [hu]
      nlinarith [mul_pos
        (show (0 : ℝ) < (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) - 945/1000 by linarith)
        (show (0 : ℝ) < (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) + 945/1000 by linarith)]
    · rw [hu]
      nlinarith [mul_pos
        (show (0 : ℝ) < 948/1000 - (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) by linarith)
        (show (0 : ℝ) < 948/1000 + (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) by linarith)]
  · right; right
    subst r
    have hc : (candidateCenterNumerator11 (36, 56, 73, 46, 50) : ℝ) /
        (phaseCenterScale : ℝ) = 31861761997412 / 100000000000000 := by
      norm_num [candidateCenterNumerator11, phaseCenters160, phaseCenterScale]
    rw [hc] at hclose
    refine ⟨rfl, ?_, ?_⟩
    · rw [hu]
      nlinarith [mul_pos
        (show (0 : ℝ) < (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) - 317/1000 by linarith)
        (show (0 : ℝ) < (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) + 317/1000 by linarith)]
    · rw [hu]
      nlinarith [mul_pos
        (show (0 : ℝ) < 321/1000 - (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) by linarith)
        (show (0 : ℝ) < 321/1000 + (1 + 2 * (s.1.a + s.1.c + s.1.e + s.1.g + s.1.j)) by linarith)]

private theorem bUnitRoot_exhausted11 (b : BUnitRoot) :
    b = bUnitRoot0 ∨ b = bUnitRoot1 ∨
    b = bUnitRoot2 ∨ b = bUnitRoot3 := by
  have h01 : (bUnitRoot0 : ℝ) < bUnitRoot1 := by
    linarith [bUnitRoot0_bounds, bUnitRoot1_bounds]
  have h12 : (bUnitRoot1 : ℝ) < bUnitRoot2 := by
    linarith [bUnitRoot1_bounds, bUnitRoot2_bounds]
  have h23 : (bUnitRoot2 : ℝ) < bUnitRoot3 := by
    linarith [bUnitRoot2_bounds, bUnitRoot3_bounds]
  have h02 := h01.trans h12
  have h03 := h02.trans h23
  have h13 := h12.trans h23
  let roots : Finset BUnitRoot :=
    {bUnitRoot0, bUnitRoot1, bUnitRoot2, bUnitRoot3}
  have hne : ∀ x y : BUnitRoot, (x : ℝ) < y → x ≠ y := by
    intro x y hxy heq
    have hv := congrArg (fun z : BUnitRoot => (z : ℝ)) heq
    linarith
  have hcard : roots.card = 4 := by
    simp [roots, hne _ _ h01, hne _ _ h02,
      hne _ _ h03, hne _ _ h12,
      hne _ _ h13, hne _ _ h23]
  have hall : roots = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ roots)
    rw [Finset.card_univ, BUnitRoot_card, hcard]
  have hb : b ∈ roots := by rw [hall]; exact Finset.mem_univ _
  simpa [roots] using hb

private theorem invariantBR_no_root_in_a_intervals11 (u : ℝ)
    (hlo : (0 : ℝ) < u) (hhi : u < 1)
    (hinterval : (u < 1/50) ∨
      (1/20 < u ∧ u < 1/10) ∨
      (9/10 < u ∧ u < 93/100)) :
    ¬invariantBR.IsRoot u := by
  intro hroot
  have hne : invariantBR ≠ 0 := by
    intro heq
    have heval := congrArg (fun p : ℝ[X] => p.eval 0) heq
    norm_num [invariantBR, invariantB] at heval
  let b : BUnitRoot := ⟨⟨u, by
    rw [mem_rootSet]
    exact ⟨hne, hroot.eq_zero⟩⟩, hlo, hhi⟩
  rcases bUnitRoot_exhausted11 b with h | h | h | h
  · have hv : u = (bUnitRoot0 : ℝ) := congrArg (fun x : BUnitRoot => (x : ℝ)) h
    rcases hinterval with hi | hi | hi <;> linarith [bUnitRoot0_bounds]
  · have hv : u = (bUnitRoot1 : ℝ) := congrArg (fun x : BUnitRoot => (x : ℝ)) h
    rcases hinterval with hi | hi | hi <;> linarith [bUnitRoot1_bounds]
  · have hv : u = (bUnitRoot2 : ℝ) := congrArg (fun x : BUnitRoot => (x : ℝ)) h
    rcases hinterval with hi | hi | hi <;> linarith [bUnitRoot2_bounds]
  · have hv : u = (bUnitRoot3 : ℝ) := congrArg (fun x : BUnitRoot => (x : ℝ)) h
    rcases hinterval with hi | hi | hi <;> linarith [bUnitRoot3_bounds]

private theorem phaseInvariantU11_sector_decomposition
    (s : PhaseSolution11) :
    phaseInvariantU11 s.1 = 0 ∨ phaseInvariantU11 s.1 = 176 ∨
      invariantAR.IsRoot (phaseInvariantU11 s.1) ∨
      invariantBR.IsRoot (phaseInvariantU11 s.1) := by
  let u := phaseInvariantU11 s.1
  have hrootC := phaseInvariantU11_is_fixedSliceQuotientRoot s
  have hmap :
      ((fixedSliceQuotientP16Q.map (algebraMap ℚ ℝ)).map Complex.ofRealHom) =
        fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]
    ext q
    simp
  rw [← hmap] at hrootC
  have hroot : (fixedSliceQuotientP16Q.map (algebraMap ℚ ℝ)).IsRoot u :=
    hrootC.of_map Complex.ofReal_injective
  have hfactor : fixedSliceQuotientP16Q.map (algebraMap ℚ ℝ) =
      X * (X - C 176) * invariantAR * invariantBR := by
    rw [fixedSliceQuotientP16Q_factor]
    simp [invariantAR, invariantBR, map_X, map_C, map_map]
  rw [hfactor] at hroot
  change (X * (X - C 176) * invariantAR * invariantBR).eval u = 0 at hroot
  simp only [eval_mul, eval_X, eval_sub, eval_C, mul_eq_zero] at hroot
  rcases hroot with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The three realized candidate boxes have invariants on the sextic A
factor. -/
theorem aSectorRepresentativeBox_invariantA11
    (s : PhaseSolution11) (r : PhaseCandidateQuintuple11)
    (hr : r ∈ aSectorCandidateOrbitRepresentatives11)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 r) :
    invariantAR.IsRoot (phaseInvariantU11 s.1) := by
  have hinterval := aSectorRepresentativeBox_invariant_intervals11 s r hr hbox
  have hunit := phaseInvariantU11_mem_unitInterval s.1 s.2
  have hpos : 0 < phaseInvariantU11 s.1 := by
    rcases hinterval with h | h | h <;> linarith [h.2.1]
  have hlt : phaseInvariantU11 s.1 < 1 := by
    rcases hinterval with h | h | h <;> linarith [h.2.2]
  have hAorB := phaseInvariantU11_sector_decomposition s
  rcases hAorB with h | h | h | h
  · linarith
  · linarith [hunit.2]
  · exact h
  · exact False.elim ((invariantBR_no_root_in_a_intervals11
      (phaseInvariantU11 s.1) hpos hlt (by
        rcases hinterval with h | h | h
        · exact Or.inr (Or.inr h.2)
        · exact Or.inr (Or.inl h.2)
        · exact Or.inl h.2.2)) h)

private theorem aUnitRoot_exhausted11 (a : AUnitRoot) :
    a = aUnitRoot0 ∨ a = aUnitRoot1 ∨ a = aUnitRoot2 := by
  have h01 : (aUnitRoot0 : ℝ) < aUnitRoot1 := by
    linarith [aUnitRoot0_bounds, aUnitRoot1_bounds]
  have h12 : (aUnitRoot1 : ℝ) < aUnitRoot2 := by
    linarith [aUnitRoot1_bounds, aUnitRoot2_bounds]
  have h02 := h01.trans h12
  have hne : ∀ x y : AUnitRoot, (x : ℝ) < y → x ≠ y := by
    intro x y hxy heq
    have hv := congrArg (fun z : AUnitRoot => (z : ℝ)) heq
    linarith
  let roots : Finset AUnitRoot := {aUnitRoot0, aUnitRoot1, aUnitRoot2}
  have hcard : roots.card = 3 := by
    simp [roots, hne _ _ h01, hne _ _ h02, hne _ _ h12]
  have hall : roots = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ roots)
    rw [Finset.card_univ, AUnitRoot_card, hcard]
  have ha : a ∈ roots := by rw [hall]; exact Finset.mem_univ _
  simpa [roots] using ha

private noncomputable def phaseInvariantU11_aUnitRoot
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    AUnitRoot := by
  have hunit := phaseInvariantU11_mem_unitInterval s.1 s.2
  have hzero : ¬invariantAR.IsRoot 0 := by
    intro h
    norm_num [invariantAR, invariantA, Polynomial.IsRoot] at h
  have hone : ¬invariantAR.IsRoot 1 := by
    intro h
    norm_num [invariantAR, invariantA, Polynomial.IsRoot] at h
  refine ⟨⟨phaseInvariantU11 s.1, ?_⟩, ?_, ?_⟩
  · rw [mem_rootSet]
    have hne : invariantAR ≠ 0 := by
      intro heq
      have heval := congrArg (fun p : ℝ[X] => p.eval 0) heq
      norm_num [invariantAR, invariantA] at heval
    exact ⟨hne, hA.eq_zero⟩
  · rcases hunit.1.eq_or_lt with h | h
    · exact False.elim (hzero (h ▸ hA))
    · exact h
  · rcases hunit.2.eq_or_lt with h | h
    · exact False.elim (hone (h.symm ▸ hA))
    · exact h

/-- The three A-tagged representative boxes realize all three admissible
sextic A invariant roots. -/
theorem aSectorRepresentativeBox_root_eq11
    (s : PhaseSolution11) (r : PhaseCandidateQuintuple11)
    (hr : r ∈ aSectorCandidateOrbitRepresentatives11)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 r) :
    (r = (22, 76, 71, 33, 31) ∧
      phaseInvariantU11 s.1 = (aUnitRoot2 : ℝ)) ∨
    (r = (26, 61, 40, 55, 65) ∧
      phaseInvariantU11 s.1 = (aUnitRoot1 : ℝ)) ∨
    (r = (36, 56, 73, 46, 50) ∧
      phaseInvariantU11 s.1 = (aUnitRoot0 : ℝ)) := by
  have hA := aSectorRepresentativeBox_invariantA11 s r hr hbox
  have hroot := aUnitRoot_exhausted11 (phaseInvariantU11_aUnitRoot s hA)
  have hinterval := aSectorRepresentativeBox_invariant_intervals11 s r hr hbox
  rcases hinterval with h | h | h
  · left
    refine ⟨h.1, ?_⟩
    rcases hroot with hroot | hroot | hroot
    · have hv : phaseInvariantU11 s.1 = (aUnitRoot0 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
      linarith [aUnitRoot0_bounds]
    · have hv : phaseInvariantU11 s.1 = (aUnitRoot1 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
      linarith [aUnitRoot1_bounds]
    · simpa only [phaseInvariantU11_aUnitRoot] using
        congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
  · right; left
    refine ⟨h.1, ?_⟩
    rcases hroot with hroot | hroot | hroot
    · have hv : phaseInvariantU11 s.1 = (aUnitRoot0 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
      linarith [aUnitRoot0_bounds]
    · simpa only [phaseInvariantU11_aUnitRoot] using
        congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
    · have hv : phaseInvariantU11 s.1 = (aUnitRoot2 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
      linarith [aUnitRoot2_bounds]
  · right; right
    refine ⟨h.1, ?_⟩
    rcases hroot with hroot | hroot | hroot
    · simpa only [phaseInvariantU11_aUnitRoot] using
        congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
    · have hv : phaseInvariantU11 s.1 = (aUnitRoot1 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
      linarith [aUnitRoot1_bounds]
    · have hv : phaseInvariantU11 s.1 = (aUnitRoot2 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) hroot
      linarith [aUnitRoot2_bounds]

/-- Every physical phase in the A sector has the same invariant, hence the
same normalized-even symmetry orbit, as one of the three realized A boxes. -/
theorem everyASectorPhase_matchesRepresentative11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∃ r ∈ aSectorCandidateOrbitRepresentatives11,
      ∃ t : PhaseSolution11,
        phaseCandidateQuintupleBox11 (1 / 10000) t.1 r ∧
        phaseInvariantU11 s.1 = phaseInvariantU11 t.1 := by
  rcases aUnitRoot_exhausted11 (phaseInvariantU11_aUnitRoot s hA) with h | h | h
  · let r : PhaseCandidateQuintuple11 := (36, 56, 73, 46, 50)
    have hr : r ∈ aSectorCandidateOrbitRepresentatives11 := by native_decide
    obtain ⟨t, hbox⟩ := aSectorCandidateRepresentative_realized11 r hr
    have ht := aSectorRepresentativeBox_root_eq11 t r hr hbox
    rcases ht with ht | ht | ht
    · simp [r] at ht
    · simp [r] at ht

    · refine ⟨r, hr, t, hbox, ?_⟩
      have hs : phaseInvariantU11 s.1 = (aUnitRoot0 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) h
      rw [hs, ht.2]
  · let r : PhaseCandidateQuintuple11 := (26, 61, 40, 55, 65)
    have hr : r ∈ aSectorCandidateOrbitRepresentatives11 := by native_decide
    obtain ⟨t, hbox⟩ := aSectorCandidateRepresentative_realized11 r hr
    have ht := aSectorRepresentativeBox_root_eq11 t r hr hbox
    rcases ht with ht | ht | ht
    · simp [r] at ht
    · refine ⟨r, hr, t, hbox, ?_⟩
      have hs : phaseInvariantU11 s.1 = (aUnitRoot1 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) h
      rw [hs, ht.2]
    · simp [r] at ht
  · let r : PhaseCandidateQuintuple11 := (22, 76, 71, 33, 31)
    have hr : r ∈ aSectorCandidateOrbitRepresentatives11 := by native_decide
    obtain ⟨t, hbox⟩ := aSectorCandidateRepresentative_realized11 r hr
    have ht := aSectorRepresentativeBox_root_eq11 t r hr hbox
    rcases ht with ht | ht | ht
    · refine ⟨r, hr, t, hbox, ?_⟩
      have hs : phaseInvariantU11 s.1 = (aUnitRoot2 : ℝ) := by
        simpa only [phaseInvariantU11_aUnitRoot] using
          congrArg (fun z : AUnitRoot => (z : ℝ)) h
      rw [hs, ht.2]
    · simp [r] at ht
    · simp [r] at ht

/-- The three tagged representatives are exactly the three normalized-even
orbits in the physical A sector. -/
theorem everyASectorPhase_sameOrbitRepresentative11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∃ r ∈ aSectorCandidateOrbitRepresentatives11,
      ∃ t : PhaseSolution11,
        phaseCandidateQuintupleBox11 (1 / 10000) t.1 r ∧
        (Quotient.mk'' s : PhaseSolution11Orbit) = Quotient.mk'' t := by
  obtain ⟨r, hr, t, hbox, hu⟩ :=
    everyASectorPhase_matchesRepresentative11 s hA
  exact ⟨r, hr, t, hbox, (phaseSolution11_same_orbit_iff_u_eq s t).2 hu⟩

end Biunimodular.F11
