/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252PhaseEliminationCertificate11
import Biunimodular.F11.P150PhaseGramSpectrum11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Exact uniqueness in the eighty accepted phase boxes

Every imaginary phase coordinate is a `P150` root, by applying the existing
last-coordinate elimination after a suitable dilation.  The forty rational
root intervals are locally unique (`P150RootIsolation11`), and their phase
centers are much farther apart than the scanner radius.  Consequently two
solutions in one accepted box have equal imaginary coordinates; the circle
equations and the fixed real-coordinate signs then give equality of the real
coordinates as well.
-/

def phaseCenterIntervalIndex11 (i : Fin 160) : Fin 40 :=
  ⟨i.1 / 4, by omega⟩

/-- Distinct squared-root blocks have imaginary centers separated by more
than the sum of the wide scanner radius and the certified root radius. -/
theorem phaseCenter_im_block_separationQ11 :
    ∀ i r : Fin 160,
      phaseCenterIntervalIndex11 i ≠ phaseCenterIntervalIndex11 r →
      (1 / 10000 : ℚ) + p150PhaseRootRadiusQ11 <
        |centerCoordQ11 (phaseCenters160[i.1]!).im -
          centerCoordQ11 (phaseCenters160[r.1]!).im| := by
  native_decide

/-- No real or imaginary center coordinate is close to zero at scanner
scale. -/
theorem phaseCenter_coordinates_away_from_zeroQ11 :
    ∀ i : Fin 160,
      (1 / 10000 : ℚ) <
          |centerCoordQ11 (phaseCenters160[i.1]!).re| ∧
        (1 / 10000 : ℚ) <
          |centerCoordQ11 (phaseCenters160[i.1]!).im| := by
  native_decide

private theorem phaseCenter_im_block_separation11
    (i r : Fin 160)
    (hir : phaseCenterIntervalIndex11 i ≠ phaseCenterIntervalIndex11 r) :
    (1 / 10000 : ℝ) + p150PhaseRootRadius11 <
      |centerCoordR (phaseCenters160[i.1]!).im -
        centerCoordR (phaseCenters160[r.1]!).im| := by
  have h := phaseCenter_im_block_separationQ11 i r hir
  have hc := (Rat.cast_lt (K := ℝ)).mpr h
  simpa [centerCoordQ11, centerCoordR, p150PhaseRootRadiusQ11,
    p150PhaseRootRadius11] using hc

private theorem phaseCenter_coordinates_away_from_zero11 (i : Fin 160) :
    (1 / 10000 : ℝ) <
        |centerCoordR (phaseCenters160[i.1]!).re| ∧
      (1 / 10000 : ℝ) <
        |centerCoordR (phaseCenters160[i.1]!).im| := by
  have h := phaseCenter_coordinates_away_from_zeroQ11 i
  constructor
  · have hc := (Rat.cast_lt (K := ℝ)).mpr h.1
    simpa [centerCoordQ11, centerCoordR] using hc
  · have hc := (Rat.cast_lt (K := ℝ)).mpr h.2
    simpa [centerCoordQ11, centerCoordR] using hc

private theorem eq_of_sq_eq_of_close_center
    (c δ x y : ℝ) (_hδ : 0 ≤ δ) (hc : δ < |c|)
    (hx : |x - c| < δ) (hy : |y - c| < δ)
    (hsq : x ^ 2 = y ^ 2) : x = y := by
  rw [abs_lt] at hx hy
  by_cases hcnonneg : 0 ≤ c
  · have hcpos : δ < c := by simpa [abs_of_nonneg hcnonneg] using hc
    have hxpos : 0 < x := by linarith [hx.1]
    have hypos : 0 < y := by linarith [hy.1]
    nlinarith
  · have hcneg : c < 0 := lt_of_not_ge hcnonneg
    have hc' : δ < -c := by simpa [abs_of_neg hcneg] using hc
    have hxneg : x < 0 := by linarith [hx.2]
    have hyneg : y < 0 := by linarith [hy.2]
    nlinarith

private theorem p150_root_has_factor11 (k : ℝ)
    (hk : p150KR11.IsRoot k) :
    ∃ factor : KFactor,
      (p150FactorPolynomialR11 factor).IsRoot (k ^ 2) := by
  rw [Polynomial.IsRoot, p150KR11_eval_factorization] at hk
  rcases mul_eq_zero.mp hk with hleft | h40
  · rcases mul_eq_zero.mp hleft with h5 | h30
    · exact ⟨.g5, by simpa [Polynomial.IsRoot] using h5⟩
    · exact ⟨.f30, by simpa [Polynomial.IsRoot] using h30⟩
  · exact ⟨.f40, by simpa [Polynomial.IsRoot] using h40⟩

theorem phasePair_tagged_factor_root11
    (u v : ℝ) (i : Fin 160)
    (hcircle : u ^ 2 + v ^ 2 = 1)
    (hvroot : p150KR11.IsRoot v)
    (hvclose : |v - centerCoordR (phaseCenters160[i.1]!).im| < 1 / 10000) :
    let q := phaseCenterIntervalIndex11 i
    (p150FactorPolynomialR11
      (squaredKRootIntervals40[q.1]!).factor).IsRoot (v ^ 2) ∧
    (squaredKRootIntervals40[q.1]!).box.lo ≤ v ^ 2 ∧
    v ^ 2 ≤ (squaredKRootIntervals40[q.1]!).box.hi := by
  let q := phaseCenterIntervalIndex11 i
  obtain ⟨factor, hfactor⟩ := p150_root_has_factor11 v hvroot
  have hv0 : 0 ≤ v ^ 2 := sq_nonneg v
  have hv1 : v ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
  obtain ⟨r, hrmem, hrbounds⟩ :=
    p150FactorPolynomialR11_root_in_interval factor (v ^ 2)
      hv0 hv1 hfactor
  obtain ⟨o, hcenter⟩ :=
    squaredK_interval_phase_center_block11 u v r hrbounds hcircle
  let center := phaseCenterBlockIndex11 r o
  have hblocks : phaseCenterIntervalIndex11 center = q := by
    by_contra hne
    have hsep := phaseCenter_im_block_separation11 i center (by
      intro heq
      exact hne heq.symm)
    rcases hcenter with ⟨_, hvnarrow⟩
    have htriangle :
        |centerCoordR (phaseCenters160[i.1]!).im -
            centerCoordR (phaseCenters160[center.1]!).im| <
          (1 / 10000 : ℝ) + p150PhaseRootRadius11 := by
      calc
        |centerCoordR (phaseCenters160[i.1]!).im -
            centerCoordR (phaseCenters160[center.1]!).im| =
            |(centerCoordR (phaseCenters160[i.1]!).im - v) +
              (v - centerCoordR (phaseCenters160[center.1]!).im)| := by ring_nf
        _ ≤ |centerCoordR (phaseCenters160[i.1]!).im - v| +
              |v - centerCoordR (phaseCenters160[center.1]!).im| :=
            abs_add_le _ _
        _ < (1 / 10000 : ℝ) + p150PhaseRootRadius11 := by
            rw [abs_sub_comm] at hvclose
            linarith
    exact (not_lt_of_ge hsep.le) htriangle
  have hcenterBlock : phaseCenterIntervalIndex11 center = r := by
    apply Fin.ext
    dsimp [center, phaseCenterIntervalIndex11, phaseCenterBlockIndex11]
    omega
  have hrq : r = q := hcenterBlock.symm.trans hblocks
  have htag := p150FactorRootIndices11_tags factor r hrmem
  have htagq : (squaredKRootIntervals40[q.1]!).factor = factor := by
    simpa [hrq] using htag
  have hrboundsq :
      (squaredKRootIntervals40[q.1]!).box.lo ≤ v ^ 2 ∧
        v ^ 2 ≤ (squaredKRootIntervals40[q.1]!).box.hi := by
    simpa [hrq] using hrbounds
  change
    (p150FactorPolynomialR11
      (squaredKRootIntervals40[q.1]!).factor).IsRoot (v ^ 2) ∧ _
  have hfactor' :
      (p150FactorPolynomialR11
        (squaredKRootIntervals40[q.1]!).factor).IsRoot (v ^ 2) := by
    rw [htagq]
    exact hfactor
  exact ⟨hfactor', hrboundsq⟩

private theorem phasePair_eq_of_same_center11
    (u₁ v₁ u₂ v₂ : ℝ) (i : Fin 160)
    (hcircle₁ : u₁ ^ 2 + v₁ ^ 2 = 1)
    (hcircle₂ : u₂ ^ 2 + v₂ ^ 2 = 1)
    (hvroot₁ : p150KR11.IsRoot v₁)
    (hvroot₂ : p150KR11.IsRoot v₂)
    (huclose₁ : |u₁ - centerCoordR (phaseCenters160[i.1]!).re| < 1 / 10000)
    (hvclose₁ : |v₁ - centerCoordR (phaseCenters160[i.1]!).im| < 1 / 10000)
    (huclose₂ : |u₂ - centerCoordR (phaseCenters160[i.1]!).re| < 1 / 10000)
    (hvclose₂ : |v₂ - centerCoordR (phaseCenters160[i.1]!).im| < 1 / 10000) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  let q := phaseCenterIntervalIndex11 i
  have h₁ := phasePair_tagged_factor_root11 u₁ v₁ i hcircle₁ hvroot₁ hvclose₁
  have h₂ := phasePair_tagged_factor_root11 u₂ v₂ i hcircle₂ hvroot₂ hvclose₂
  change
    (p150FactorPolynomialR11
      (squaredKRootIntervals40[q.1]!).factor).IsRoot (v₁ ^ 2) ∧ _ at h₁
  change
    (p150FactorPolynomialR11
      (squaredKRootIntervals40[q.1]!).factor).IsRoot (v₂ ^ 2) ∧ _ at h₂
  have hvsq : v₁ ^ 2 = v₂ ^ 2 :=
    p150FactorPolynomialR11_root_unique_in_interval q (v₁ ^ 2) (v₂ ^ 2)
      h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2 h₁.1 h₂.1
  have haway := phaseCenter_coordinates_away_from_zero11 i
  have hv : v₁ = v₂ := eq_of_sq_eq_of_close_center
    (centerCoordR (phaseCenters160[i.1]!).im) (1 / 10000) v₁ v₂
    (by norm_num) haway.2 hvclose₁ hvclose₂ hvsq
  have husq : u₁ ^ 2 = u₂ ^ 2 := by nlinarith
  have hu : u₁ = u₂ := eq_of_sq_eq_of_close_center
    (centerCoordR (phaseCenters160[i.1]!).re) (1 / 10000) u₁ u₂
    (by norm_num) haway.1 huclose₁ huclose₂ husq
  exact ⟨hu, hv⟩

theorem phaseSolution_imaginary_p150_roots11 (s : PhaseSolution11) :
    p150KR11.IsRoot s.1.b ∧ p150KR11.IsRoot s.1.d ∧
      p150KR11.IsRoot s.1.f ∧ p150KR11.IsRoot s.1.h ∧
      p150KR11.IsRoot s.1.k := by
  let x := s.1
  have hx : x.IsPhaseSolution := s.2
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
  have hk := h252PhaseEliminationCertificate11.phase_k_is_p150_root x hx
  have hb := h252PhaseEliminationCertificate11.phase_k_is_p150_root
    (phaseDilate11 x) hx1
  have hd := h252PhaseEliminationCertificate11.phase_k_is_p150_root
    (phaseDilate11 (phaseDilate11 x)) hx2
  have hh := h252PhaseEliminationCertificate11.phase_k_is_p150_root
    (phaseDilate11 (phaseDilate11 (phaseDilate11 x))) hx3
  have hf := h252PhaseEliminationCertificate11.phase_k_is_p150_root
    (phaseDilate11
      (phaseDilate11 (phaseDilate11 (phaseDilate11 x)))) hx4
  simpa [x, phaseDilate11] using And.intro hb
    (And.intro hd (And.intro hf (And.intro hh hk)))

/-- The last squared imaginary coordinate of a genuine phase solution lies
on the exact factor attached to its accepted phase-box center. -/
theorem phaseSolution_last_tagged_factor_root11
    (s : PhaseSolution11)
    (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 q) :
    (p150FactorPolynomialR11
      (squaredKRootIntervals40[(match q with | (_, _, _, _, ij) => ij) / 4]!).factor).IsRoot
        (s.1.k ^ 2) := by
  rcases q with ⟨ia, ic, ie, ig, ij⟩
  have hindices := acceptedCandidate_indices_lt
    (ia, ic, ie, ig, ij) hq
  dsimp only at hindices
  have hij := hindices.2.2.2.2
  simp only [phaseCandidateQuintupleBox11] at hbox
  have hclose := hbox.2.2.2.2.2.2.2.2.2
  have hcircle := s.2.1.2.2.2.2
  have hroot := (phaseSolution_imaginary_p150_roots11 s).2.2.2.2
  exact (phasePair_tagged_factor_root11 s.1.j s.1.k
    ⟨ij, hij⟩ hcircle hroot hclose).1

/-- The same exact isolation certificate also records the last squared
coordinate inside the tagged rational interval. -/
theorem phaseSolution_last_interval_of_acceptedBox11
    (s : PhaseSolution11)
    (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 q) :
    squaredKInInterval11 s.1.k
      (squaredKRootIntervals40[(match q with | (_, _, _, _, ij) => ij) / 4]!) := by
  rcases q with ⟨ia, ic, ie, ig, ij⟩
  have hindices := acceptedCandidate_indices_lt
    (ia, ic, ie, ig, ij) hq
  dsimp only at hindices
  have hij := hindices.2.2.2.2
  simp only [phaseCandidateQuintupleBox11] at hbox
  have hclose := hbox.2.2.2.2.2.2.2.2.2
  have hcircle := s.2.1.2.2.2.2
  have hroot := (phaseSolution_imaginary_p150_roots11 s).2.2.2.2
  exact (phasePair_tagged_factor_root11 s.1.j s.1.k
    ⟨ij, hij⟩ hcircle hroot hclose).2

/-- The P150 isolation and circle geometry prove uniqueness in every one of
the eighty accepted scanner boxes. -/
theorem phaseAcceptedBoxUniquenessCertificate11 :
    PhaseAcceptedBoxUniquenessCertificate11 where
  unique q s t hs ht := by
    rcases q with ⟨⟨ia, ic, ie, ig, ij⟩, hq⟩
    have hindices := acceptedCandidate_indices_lt
      (ia, ic, ie, ig, ij) (by simpa using hq)
    dsimp only at hindices
    rcases hindices with ⟨hia, hic, hie, hig, hij⟩
    simp only [phaseCandidateQuintupleBox11] at hs ht
    rcases hs with ⟨hsa, hsb, hsc, hsd, hse, hsf, hsg, hsh, hsj, hsk⟩
    rcases ht with ⟨hta, htb, htc, htd, hte, htf, htg, hth, htj, htk⟩
    have hsroots := phaseSolution_imaginary_p150_roots11 s
    have htroots := phaseSolution_imaginary_p150_roots11 t
    rcases s.2.1 with ⟨hsab, hscd, hsef, hsgh, hsjk⟩
    rcases t.2.1 with ⟨htab, htcd, htef, htgh, htjk⟩
    have hab := phasePair_eq_of_same_center11
      s.1.a s.1.b t.1.a t.1.b ⟨ia, hia⟩ hsab htab
      hsroots.1 htroots.1 hsa hsb hta htb
    have hcd := phasePair_eq_of_same_center11
      s.1.c s.1.d t.1.c t.1.d ⟨ic, hic⟩ hscd htcd
      hsroots.2.1 htroots.2.1 hsc hsd htc htd
    have hef := phasePair_eq_of_same_center11
      s.1.e s.1.f t.1.e t.1.f ⟨ie, hie⟩ hsef htef
      hsroots.2.2.1 htroots.2.2.1 hse hsf hte htf
    have hgh := phasePair_eq_of_same_center11
      s.1.g s.1.h t.1.g t.1.h ⟨ig, hig⟩ hsgh htgh
      hsroots.2.2.2.1 htroots.2.2.2.1 hsg hsh htg hth
    have hjk := phasePair_eq_of_same_center11
      s.1.j s.1.k t.1.j t.1.k ⟨ij, hij⟩ hsjk htjk
      hsroots.2.2.2.2 htroots.2.2.2.2 hsj hsk htj htk
    apply Subtype.ext
    rcases s with ⟨⟨sa, sb, sc, sd, se, sf, sg, sh, sj, sk⟩, _⟩
    rcases t with ⟨⟨ta, tb, tc, td, te, tf, tg, th, tj, tk⟩, _⟩
    simp only at hab hcd hef hgh hjk
    simp [hab.1, hab.2, hcd.1, hcd.2, hef.1, hef.2,
      hgh.1, hgh.2, hjk.1, hjk.2]

end

end Biunimodular.F11
