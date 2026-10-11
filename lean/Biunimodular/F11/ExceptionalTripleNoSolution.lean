/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.ExceptionalWitnessBounds
public import Biunimodular.F11.ExceptionalTailExclusion
public import Biunimodular.F11.CenterTailScaling

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-- Cast one exact rational exceptional witness to the real vector consumed by
the perturbation theorem. -/
def witnessVecR (w : ExceptionalWitness) : Vec4R :=
  fun i => (witnessVec w i : ℝ)

lemma witnessL1_cast (w : ExceptionalWitness) :
    wL1 (witnessVecR w) = (witnessL1 w : ℝ) := by
  simp [wL1, witnessL1, witnessVecR, witnessVec, Fin.sum_univ_four,
    Rat.cast_abs]

lemma witnessCenterR_cast (w : ExceptionalWitness) :
    let A := centerCoordR (phaseCenters160[w.aIdx]!).re
    let B := centerCoordR (phaseCenters160[w.aIdx]!).im
    let C := centerCoordR (phaseCenters160[w.cIdx]!).re
    let D := centerCoordR (phaseCenters160[w.cIdx]!).im
    let E := centerCoordR (phaseCenters160[w.eIdx]!).re
    let F := centerCoordR (phaseCenters160[w.eIdx]!).im
    wDotR (witnessVecR w) A B C D E F = (witnessCenterR w : ℝ) := by
  simp [centerCoordR, wDotR, witnessVecR, witnessCenterR, centerTailRhsQ,
    centerQ, tailRhs, dotWitness, witnessVec, Fin.sum_univ_four]

lemma witnessCenterM_cast (w : ExceptionalWitness) (j : Fin 4) :
    let A := centerCoordR (phaseCenters160[w.aIdx]!).re
    let B := centerCoordR (phaseCenters160[w.aIdx]!).im
    let C := centerCoordR (phaseCenters160[w.cIdx]!).re
    let D := centerCoordR (phaseCenters160[w.cIdx]!).im
    let E := centerCoordR (phaseCenters160[w.eIdx]!).re
    let F := centerCoordR (phaseCenters160[w.eIdx]!).im
    wDotMCol (witnessVecR w) A B C D E F j = (witnessCenterM w j : ℝ) := by
  fin_cases j <;>
    simp [centerCoordR, wDotMCol, witnessVecR, witnessCenterM,
      centerTailMatrixQ, centerQ, tailMatrix, dotWitness, witnessVec,
      Fin.sum_univ_four]

/-- An actual unit-bounded tail solution cannot have its first three phases in
one of the 20 exceptional candidate boxes.  This packages the finite witness
table with the generic perturbation contradiction. -/
theorem exceptionalTriple_no_actual_tail
    (ia ic ie : Fin 160)
    {δ a b c d e f g h j k : ℝ}
    (hex : exceptionalTriple ia.1 ic.1 ie.1 = true)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 200000000000000 : ℝ))
    (hclose : close6 δ a b c d e f
      (centerCoordR (phaseCenters160[ia.1]!).re)
      (centerCoordR (phaseCenters160[ia.1]!).im)
      (centerCoordR (phaseCenters160[ic.1]!).re)
      (centerCoordR (phaseCenters160[ic.1]!).im)
      (centerCoordR (phaseCenters160[ie.1]!).re)
      (centerCoordR (phaseCenters160[ie.1]!).im))
    (hu : unit6 a b c d e f)
    (hg : |g| ≤ 1) (hh : |h| ≤ 1) (hj : |j| ≤ 1) (hk : |k| ≤ 1)
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) =
      tailRhs a b c d e f) :
    False := by
  have hwSome : (witnessForTriple ia.1 ic.1 ie.1).isSome = true := by
    simpa [witnessForTriple_iff_exceptional ia ic ie] using hex
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hwSome
  have hwfind :
      List.find? (fun x : ExceptionalWitness =>
        decide (x.aIdx = ia.1) &&
          (decide (x.cIdx = ic.1) && decide (x.eIdx = ie.1)))
        exceptionalWitnesses20 = some w := by
    simpa [witnessForTriple] using hw
  have hwidxB := List.find?_some hwfind
  have hwidx : w.aIdx = ia.1 ∧ w.cIdx = ic.1 ∧ w.eIdx = ie.1 := by
    simpa using hwidxB
  rcases hwidx with ⟨hwa,hwc,hwe⟩
  have hb := witnessForTriple_bounds ia ic ie w hw
  rcases hb with ⟨hR,hM,hL1⟩
  let A := centerCoordR (phaseCenters160[ia.1]!).re
  let B := centerCoordR (phaseCenters160[ia.1]!).im
  let C := centerCoordR (phaseCenters160[ic.1]!).re
  let D := centerCoordR (phaseCenters160[ic.1]!).im
  let E := centerCoordR (phaseCenters160[ie.1]!).re
  let F := centerCoordR (phaseCenters160[ie.1]!).im
  let wr := witnessVecR w
  have hU : unit6 A B C D E F := by
    simpa [A,B,C,D,E,F] using center_unit6 ia ic ie
  have hL1' : witnessL1 w < 2 := by
    simpa [witnessL1, witnessVec, Fin.sum_univ_four, absQ_eq_abs] using hL1
  have hwR : wL1 wr ≤ 2 := by
    rw [witnessL1_cast]
    exact_mod_cast (le_of_lt hL1')
  have hR' : (1/100 : ℚ) < |witnessCenterR w| := by
    simpa [witnessCenterR, absQ_eq_abs] using hR
  have hRr : (1/100 : ℝ) < |wDotR wr A B C D E F| := by
    rw [show wDotR wr A B C D E F = (witnessCenterR w : ℝ) by
      simpa [A,B,C,D,E,F,wr,hwa,hwc,hwe] using witnessCenterR_cast w]
    have hRcast := (Rat.cast_lt (K := ℝ)).2 hR'
    norm_num at hRcast ⊢
    simpa only [Rat.cast_abs] using hRcast
  have hM' : ∀ q : Fin 4, |witnessCenterM w q| < (1/1000000000 : ℚ) := by
    intro q
    simpa [witnessCenterM, absQ_eq_abs] using hM q
  have hMr : ∀ q : Fin 4, |wDotMCol wr A B C D E F q| < (1/1000000000 : ℝ) := by
    intro q
    rw [show wDotMCol wr A B C D E F q = (witnessCenterM w q : ℝ) by
      simpa [A,B,C,D,E,F,wr,hwa,hwc,hwe] using witnessCenterM_cast w q]
    have hMcast := (Rat.cast_lt (K := ℝ)).2 (hM' q)
    norm_num at hMcast ⊢
    simpa only [Rat.cast_abs] using hMcast
  exact no_tail_solution_near_exceptional_witness
    hδ hδsmall (by simpa [A,B,C,D,E,F] using hclose) hu hU hg hh hj hk hsol
    hwR hRr hMr

end Biunimodular.F11
