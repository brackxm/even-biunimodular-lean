/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.PhaseNearCompleteness
public import Biunimodular.F11.CenterTailScaling
public import Biunimodular.F11.TailCramerRatioBound
public import Biunimodular.F11.ExceptionalTripleNoSolution
public meta import Biunimodular.F11.ProofTactics
public meta import Biunimodular.F11.PhaseNearCompleteness
public meta import Biunimodular.F11.CenterTailScaling
public meta import Biunimodular.F11.TailCramerRatioBound
public meta import Biunimodular.F11.ExceptionalTripleNoSolution

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-- Tail coordinates lie in the two certified phase boxes `ig,ij`. -/
def closeTailCandidates (δ g h j k : ℝ) (ig ij : Fin 160) : Prop :=
  |g - centerCoordR (phaseCenters160[ig.1]!).re| ≤ δ ∧
  |h - centerCoordR (phaseCenters160[ig.1]!).im| ≤ δ ∧
  |j - centerCoordR (phaseCenters160[ij.1]!).re| ≤ δ ∧
  |k - centerCoordR (phaseCenters160[ij.1]!).im| ≤ δ

/-- The first three exact phases lie in the candidate boxes selected by
`ia,ic,ie`. -/
def closeFirstThreeCandidates (δ a b c d e f : ℝ)
    (ia ic ie : Fin 160) : Prop :=
  close6 δ a b c d e f
    (centerCoordR (phaseCenters160[ia.1]!).re)
    (centerCoordR (phaseCenters160[ia.1]!).im)
    (centerCoordR (phaseCenters160[ic.1]!).re)
    (centerCoordR (phaseCenters160[ic.1]!).im)
    (centerCoordR (phaseCenters160[ie.1]!).re)
    (centerCoordR (phaseCenters160[ie.1]!).im)

private lemma int_det_nonzero_of_margin
    (ia ic ie : Fin 160)
    (hreg : exceptionalTriple ia.1 ic.1 ie.1 = false) :
    (centerTailSystem ia.1 ic.1 ie.1).det ≠ 0 := by
  have hm := center_det_margin_all ia ic ie hreg
  have ht : 0 < centerDetThreshold := by
    norm_num [centerDetThreshold, phaseCenterScale]
  have habs : 0 < iabs (centerTailSystem ia.1 ic.1 ie.1).det :=
    lt_of_lt_of_le ht hm
  intro hz
  rw [hz] at habs
  norm_num [iabs] at habs

private lemma int_den_pos_of_margin
    (ia ic ie : Fin 160)
    (hreg : exceptionalTriple ia.1 ic.1 ie.1 = false) :
    0 < iabs (centerTailSystem ia.1 ic.1 ie.1).det := by
  have hm := center_det_margin_all ia ic ie hreg
  have ht : 0 < centerDetThreshold := by
    norm_num [centerDetThreshold, phaseCenterScale]
  exact lt_of_lt_of_le ht hm

/-- The exact scanner output lies in a much tighter box than the one used to
search for phase centers. -/
def acceptedTupleTight (ia ic ie ig ij : Nat) : Bool :=
  let s := centerTailSystem ia ic ie
  let den := iabs s.det
  let ng := if s.det < 0 then -s.ng else s.ng
  let nh := if s.det < 0 then -s.nh else s.nh
  let nj := if s.det < 0 then -s.nj else s.nj
  let nk := if s.det < 0 then -s.nk else s.nk
  nearScaledTight ng den (phaseCenters160[ig]!).re &&
    nearScaledTight nh den (phaseCenters160[ig]!).im &&
    nearScaledTight nj den (phaseCenters160[ij]!).re &&
    nearScaledTight nk den (phaseCenters160[ij]!).im

theorem acceptedCandidateQuintuples_tight :
    ∀ t ∈ acceptedCandidateQuintuples,
      match t with
      | (ia, ic, ie, ig, ij) => acceptedTupleTight ia ic ie ig ij = true := by
  native_decide

theorem scan_result_tight_fin
    (ia ic ie : Fin 160) {ig ij : Nat}
    (hscan : scanCenterTriple ia.1 ic.1 ie.1 = some (ig, ij)) :
    acceptedTupleTight ia.1 ic.1 ie.1 ig ij = true := by
  have hmem := scan_result_is_accepted ia ic ie
  rw [hscan] at hmem
  exact acceptedCandidateQuintuples_tight (ia.1, ic.1, ie.1, ig, ij) hmem

/-- **Regular finite-exhaustion bridge.**

Suppose all five exact phases are already known to lie in the 160 certified
root boxes (this is what the `P150` root-cover theorem supplies after the five
dilations).  If the first-three center triple is regular, the uniform Cramer
estimate forces the optimized exact scanner to succeed.  Its output is then
one of the 80 accepted quintuples by the exhaustive `native_decide` scan.
-/
theorem regularTriple_scan_succeeds_and_is_accepted
    (ia ic ie ig ij : Fin 160)
    {δ a b c d e f g h j k : ℝ}
    (hreg : exceptionalTriple ia.1 ic.1 ie.1 = false)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 200000000000000 : ℝ))
    (hfirst : closeFirstThreeCandidates δ a b c d e f ia ic ie)
    (htail : closeTailCandidates δ g h j k ig ij)
    (hu : unit6 a b c d e f)
    (hg : |g| ≤ 1) (hh : |h| ≤ 1) (hj : |j| ≤ 1) (hk : |k| ≤ 1)
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) =
      tailRhs a b c d e f) :
    ∃ ig' ij' : Nat,
      scanCenterTriple ia.1 ic.1 ie.1 = some (ig', ij') ∧
      (ia.1, ic.1, ie.1, ig', ij') ∈ acceptedCandidateQuintuples := by
  let A := centerCoordR (phaseCenters160[ia.1]!).re
  let B := centerCoordR (phaseCenters160[ia.1]!).im
  let C := centerCoordR (phaseCenters160[ic.1]!).re
  let D := centerCoordR (phaseCenters160[ic.1]!).im
  let E := centerCoordR (phaseCenters160[ie.1]!).re
  let F := centerCoordR (phaseCenters160[ie.1]!).im
  let s := centerTailSystem ia.1 ic.1 ie.1
  let den := iabs s.det
  let ng := if s.det < 0 then -s.ng else s.ng
  let nh := if s.det < 0 then -s.nh else s.nh
  let nj := if s.det < 0 then -s.nj else s.nj
  let nk := if s.det < 0 then -s.nk else s.nk
  have hU : unit6 A B C D E F := by
    simpa [A, B, C, D, E, F] using center_unit6 ia ic ie
  have hdetR : (1 / 1000000 : ℝ) ≤ |tailDetR A B C D E F| := by
    simpa [A, B, C, D, E, F] using center_real_det_margin ia ic ie hreg
  have hcr := tail_close_to_center_cramer_ratio
    hδ hδsmall (by simpa [closeFirstThreeCandidates, A, B, C, D, E, F] using hfirst)
    hu hU hg hh hj hk hsol hdetR
  rcases htail with ⟨htg, hth, htj, htk⟩
  have hnearG : |tailCramerG A B C D E F / tailDetR A B C D E F -
      centerCoordR (phaseCenters160[ig.1]!).re| < (1 / 10000 : ℝ) :=
    center_cramer_near_candidate hcr.1 htg hδsmall
  have hnearH : |tailCramerH A B C D E F / tailDetR A B C D E F -
      centerCoordR (phaseCenters160[ig.1]!).im| < (1 / 10000 : ℝ) :=
    center_cramer_near_candidate hcr.2.1 hth hδsmall
  have hnearJ : |tailCramerJ A B C D E F / tailDetR A B C D E F -
      centerCoordR (phaseCenters160[ij.1]!).re| < (1 / 10000 : ℝ) :=
    center_cramer_near_candidate hcr.2.2.1 htj hδsmall
  have hnearK : |tailCramerK A B C D E F / tailDetR A B C D E F -
      centerCoordR (phaseCenters160[ij.1]!).im| < (1 / 10000 : ℝ) :=
    center_cramer_near_candidate hcr.2.2.2 htk hδsmall
  have hdetI : s.det ≠ 0 := by
    simpa [s] using int_det_nonzero_of_margin ia ic ie hreg
  have hden : 0 < den := by
    simpa [s, den] using int_den_pos_of_margin ia ic ie hreg
  have hrat := centerTailSystem_normalized_ratios ia ic ie
    (by simpa [s] using hdetI)
  dsimp [A, B, C, D, E, F, s, den, ng, nh, nj, nk] at hrat
  rcases hrat with ⟨hrg, hrh, hrj, hrk⟩
  have hnrg : nearScaled ng den (phaseCenters160[ig.1]!).re = true := by
    apply nearScaled_of_physical_ratio_close _ _ _ hden
    rw [hrg]
    simpa [centerCoordR, A, B, C, D, E, F] using hnearG
  have hnrh : nearScaled nh den (phaseCenters160[ig.1]!).im = true := by
    apply nearScaled_of_physical_ratio_close _ _ _ hden
    rw [hrh]
    simpa [centerCoordR, A, B, C, D, E, F] using hnearH
  have hnrj : nearScaled nj den (phaseCenters160[ij.1]!).re = true := by
    apply nearScaled_of_physical_ratio_close _ _ _ hden
    rw [hrj]
    simpa [centerCoordR, A, B, C, D, E, F] using hnearJ
  have hnrk : nearScaled nk den (phaseCenters160[ij.1]!).im = true := by
    apply nearScaled_of_physical_ratio_close _ _ _ hden
    rw [hrk]
    simpa [centerCoordR, A, B, C, D, E, F] using hnearK
  have hgSome : (phaseNear s.ng s.nh s.det).isSome = true := by
    rw [phaseNear_eq_positive_normalized]
    simpa [s, den, ng, nh] using
      phaseNearPositive_isSome_of_candidate ig ng nh den hden hnrg hnrh
  have hjSome : (phaseNear s.nj s.nk s.det).isSome = true := by
    rw [phaseNear_eq_positive_normalized]
    simpa [s, den, nj, nk] using
      phaseNearPositive_isSome_of_candidate ij nj nk den hden hnrj hnrk
  cases hgscan : phaseNear s.ng s.nh s.det with
  | none => simp [hgscan] at hgSome
  | some ig' =>
    cases hjscan : phaseNear s.nj s.nk s.det with
    | none => simp [hjscan] at hjSome
    | some ij' =>
      have hm := center_det_margin_all ia ic ie hreg
      have hnotlt : ¬ iabs s.det < centerDetThreshold := by
        exact not_lt_of_ge (by simpa [s] using hm)
      have hscan : scanCenterTriple ia.1 ic.1 ie.1 = some (ig', ij') := by
        simp [scanCenterTriple, hreg, s, hnotlt, hgscan, hjscan]
      refine ⟨ig', ij', hscan, ?_⟩
      have hs := scan_result_is_accepted ia ic ie
      simpa [hscan] using hs

/-- Exceptional triples are impossible under the same candidate-box and unit
hypotheses.  This is the complementary half of the finite exhaustion. -/
theorem exceptionalTriple_impossible_for_actual_solution
    (ia ic ie : Fin 160)
    {δ a b c d e f g h j k : ℝ}
    (hex : exceptionalTriple ia.1 ic.1 ie.1 = true)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 200000000000000 : ℝ))
    (hfirst : closeFirstThreeCandidates δ a b c d e f ia ic ie)
    (hu : unit6 a b c d e f)
    (hg : |g| ≤ 1) (hh : |h| ≤ 1) (hj : |j| ≤ 1) (hk : |k| ≤ 1)
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) =
      tailRhs a b c d e f) :
    False := by
  exact exceptionalTriple_no_actual_tail ia ic ie hex hδ hδsmall
    (by simpa [closeFirstThreeCandidates] using hfirst) hu hg hh hj hk hsol

end Biunimodular.F11

namespace Biunimodular.F11

/-- The actual tail is captured by the two output phase centers of the exact
scan, with the wide `10^-4` radius used by the uniqueness boxes. -/
theorem regularTriple_scan_output_wide_capture
    (ia ic ie ig ij : Fin 160)
    {δ a b c d e f g h j k : ℝ}
    (hreg : exceptionalTriple ia.1 ic.1 ie.1 = false)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 200000000000000 : ℝ))
    (hfirst : closeFirstThreeCandidates δ a b c d e f ia ic ie)
    (htail : closeTailCandidates δ g h j k ig ij)
    (hu : unit6 a b c d e f)
    (hg : |g| ≤ 1) (hh : |h| ≤ 1) (hj : |j| ≤ 1) (hk : |k| ≤ 1)
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) =
      tailRhs a b c d e f) :
    ∃ ig' ij' : Nat,
      scanCenterTriple ia.1 ic.1 ie.1 = some (ig', ij') ∧
      (ia.1, ic.1, ie.1, ig', ij') ∈ acceptedCandidateQuintuples ∧
      |g - centerCoordR (phaseCenters160[ig']!).re| < (1 / 10000 : ℝ) ∧
      |h - centerCoordR (phaseCenters160[ig']!).im| < (1 / 10000 : ℝ) ∧
      |j - centerCoordR (phaseCenters160[ij']!).re| < (1 / 10000 : ℝ) ∧
      |k - centerCoordR (phaseCenters160[ij']!).im| < (1 / 10000 : ℝ) := by
  obtain ⟨ig', ij', hscan, hmem⟩ := regularTriple_scan_succeeds_and_is_accepted
    ia ic ie ig ij hreg hδ hδsmall hfirst htail hu hg hh hj hk hsol
  let A := centerCoordR (phaseCenters160[ia.1]!).re
  let B := centerCoordR (phaseCenters160[ia.1]!).im
  let C := centerCoordR (phaseCenters160[ic.1]!).re
  let D := centerCoordR (phaseCenters160[ic.1]!).im
  let E := centerCoordR (phaseCenters160[ie.1]!).re
  let F := centerCoordR (phaseCenters160[ie.1]!).im
  let s := centerTailSystem ia.1 ic.1 ie.1
  let den := iabs s.det
  let ng := if s.det < 0 then -s.ng else s.ng
  let nh := if s.det < 0 then -s.nh else s.nh
  let nj := if s.det < 0 then -s.nj else s.nj
  let nk := if s.det < 0 then -s.nk else s.nk
  have hU : unit6 A B C D E F := by
    simpa [A, B, C, D, E, F] using center_unit6 ia ic ie
  have hdetR : (1 / 1000000 : ℝ) ≤ |tailDetR A B C D E F| := by
    simpa [A, B, C, D, E, F] using center_real_det_margin ia ic ie hreg
  have hcr := tail_close_to_center_cramer_ratio
    hδ hδsmall (by simpa [closeFirstThreeCandidates, A, B, C, D, E, F] using hfirst)
    hu hU hg hh hj hk hsol hdetR
  have hdetI : s.det ≠ 0 := by
    simpa [s] using int_det_nonzero_of_margin ia ic ie hreg
  have hden : 0 < den := by
    simpa [s, den] using int_den_pos_of_margin ia ic ie hreg
  have hrat := centerTailSystem_normalized_ratios ia ic ie
    (by simpa [s] using hdetI)
  dsimp [A, B, C, D, E, F, s, den, ng, nh, nj, nk] at hrat
  rcases hrat with ⟨hrg, hrh, hrj, hrk⟩
  have htight := scan_result_tight_fin ia ic ie hscan
  change (nearScaledTight ng den (phaseCenters160[ig']!).re &&
    nearScaledTight nh den (phaseCenters160[ig']!).im &&
    nearScaledTight nj den (phaseCenters160[ij']!).re &&
    nearScaledTight nk den (phaseCenters160[ij']!).im) = true at htight
  have htk := (Bool.and_eq_true_iff.mp htight).2
  have htight := (Bool.and_eq_true_iff.mp htight).1
  have htj := (Bool.and_eq_true_iff.mp htight).2
  have htight := (Bool.and_eq_true_iff.mp htight).1
  have hth := (Bool.and_eq_true_iff.mp htight).2
  have htg := (Bool.and_eq_true_iff.mp htight).1
  have htgphys := physical_ratio_close_of_nearScaledTight
    ng den (phaseCenters160[ig']!).re hden htg
  have hthphys := physical_ratio_close_of_nearScaledTight
    nh den (phaseCenters160[ig']!).im hden hth
  have htjphys := physical_ratio_close_of_nearScaledTight
    nj den (phaseCenters160[ij']!).re hden htj
  have htkphys := physical_ratio_close_of_nearScaledTight
    nk den (phaseCenters160[ij']!).im hden htk
  rw [hrg] at htgphys
  rw [hrh] at hthphys
  rw [hrj] at htjphys
  rw [hrk] at htkphys
  change |tailCramerG A B C D E F / tailDetR A B C D E F -
    centerCoordR (phaseCenters160[ig']!).re| < (1 / 10000000000 : ℝ) at htgphys
  change |tailCramerH A B C D E F / tailDetR A B C D E F -
    centerCoordR (phaseCenters160[ig']!).im| < (1 / 10000000000 : ℝ) at hthphys
  change |tailCramerJ A B C D E F / tailDetR A B C D E F -
    centerCoordR (phaseCenters160[ij']!).re| < (1 / 10000000000 : ℝ) at htjphys
  change |tailCramerK A B C D E F / tailDetR A B C D E F -
    centerCoordR (phaseCenters160[ij']!).im| < (1 / 10000000000 : ℝ) at htkphys
  have hgwide : |g - centerCoordR (phaseCenters160[ig']!).re| < (1 / 10000 : ℝ) := by
    have htri : |g - centerCoordR (phaseCenters160[ig']!).re| ≤
        |g - tailCramerG A B C D E F / tailDetR A B C D E F| +
        |tailCramerG A B C D E F / tailDetR A B C D E F -
          centerCoordR (phaseCenters160[ig']!).re| := by
      calc
        |_| = |(g - tailCramerG A B C D E F / tailDetR A B C D E F) +
          (tailCramerG A B C D E F / tailDetR A B C D E F -
            centerCoordR (phaseCenters160[ig']!).re)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    nlinarith [hcr.1, htgphys]
  have hhwide : |h - centerCoordR (phaseCenters160[ig']!).im| < (1 / 10000 : ℝ) := by
    have htri : |h - centerCoordR (phaseCenters160[ig']!).im| ≤
        |h - tailCramerH A B C D E F / tailDetR A B C D E F| +
        |tailCramerH A B C D E F / tailDetR A B C D E F -
          centerCoordR (phaseCenters160[ig']!).im| := by
      calc |_| = |_ + _| := by congr 1; ring
           _ ≤ _ := abs_add_le _ _
    nlinarith [hcr.2.1, hthphys]
  have hjwide : |j - centerCoordR (phaseCenters160[ij']!).re| < (1 / 10000 : ℝ) := by
    have htri : |j - centerCoordR (phaseCenters160[ij']!).re| ≤
        |j - tailCramerJ A B C D E F / tailDetR A B C D E F| +
        |tailCramerJ A B C D E F / tailDetR A B C D E F -
          centerCoordR (phaseCenters160[ij']!).re| := by
      calc |_| = |_ + _| := by congr 1; ring
           _ ≤ _ := abs_add_le _ _
    nlinarith [hcr.2.2.1, htjphys]
  have hkwide : |k - centerCoordR (phaseCenters160[ij']!).im| < (1 / 10000 : ℝ) := by
    have htri : |k - centerCoordR (phaseCenters160[ij']!).im| ≤
        |k - tailCramerK A B C D E F / tailDetR A B C D E F| +
        |tailCramerK A B C D E F / tailDetR A B C D E F -
          centerCoordR (phaseCenters160[ij']!).im| := by
      calc |_| = |_ + _| := by congr 1; ring
           _ ≤ _ := abs_add_le _ _
    nlinarith [hcr.2.2.2, htkphys]
  exact ⟨ig', ij', hscan, hmem, hgwide, hhwide, hjwide, hkwide⟩

end Biunimodular.F11
