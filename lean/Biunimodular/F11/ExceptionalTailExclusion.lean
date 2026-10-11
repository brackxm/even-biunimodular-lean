/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.TailPerturbationCore
public import Biunimodular.F11.TailLinearSystemStd

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

abbrev Vec4R := Fin 4 → ℝ

def wDotR (w : Vec4R) (a b c d e f : ℝ) : ℝ :=
  ∑ i : Fin 4, w i * tailRhs a b c d e f i

def wDotMCol (w : Vec4R) (a b c d e f : ℝ) (j : Fin 4) : ℝ :=
  ∑ i : Fin 4, w i * tailMatrix a b c d e f i j

def wL1 (w : Vec4R) : ℝ := ∑ i : Fin 4, |w i|

private lemma abs_add_four_le (x₀ x₁ x₂ x₃ : ℝ) :
    |x₀ + x₁ + x₂ + x₃| ≤ |x₀| + |x₁| + |x₂| + |x₃| := by
  calc
    |x₀ + x₁ + x₂ + x₃| ≤ |x₀ + x₁ + x₂| + |x₃| := abs_add_le _ _
    _ ≤ (|x₀ + x₁| + |x₂|) + |x₃| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|x₀| + |x₁|) + |x₂|) + |x₃| := by
      gcongr
      exact abs_add_le _ _

lemma abs_wDotR_diff_le
    {δ a b c d e f A B C D E F : ℝ} {w : Vec4R}
    (hδ : 0 ≤ δ)
    (hclose : close6 δ a b c d e f A B C D E F)
    (hu : unit6 a b c d e f) (hU : unit6 A B C D E F)
    (hw : wL1 w ≤ 2) :
    |wDotR w a b c d e f - wDotR w A B C D E F| ≤ 28*δ := by
  have hR := tailRhs_diff_le_fourteen_delta hδ hclose hu hU
  have h0 := hR 0; have h1 := hR 1; have h2 := hR 2; have h3 := hR 3
  simp [wDotR, Fin.sum_univ_four]
  rw [show
    w 0 * tailRhs a b c d e f 0 + w 1 * tailRhs a b c d e f 1 +
      w 2 * tailRhs a b c d e f 2 + w 3 * tailRhs a b c d e f 3 -
    (w 0 * tailRhs A B C D E F 0 + w 1 * tailRhs A B C D E F 1 +
      w 2 * tailRhs A B C D E F 2 + w 3 * tailRhs A B C D E F 3) =
    w 0*(tailRhs a b c d e f 0-tailRhs A B C D E F 0) +
    w 1*(tailRhs a b c d e f 1-tailRhs A B C D E F 1) +
    w 2*(tailRhs a b c d e f 2-tailRhs A B C D E F 2) +
    w 3*(tailRhs a b c d e f 3-tailRhs A B C D E F 3) by ring]
  calc
    |_ + _ + _ + _| ≤
        |w 0| * |tailRhs a b c d e f 0 - tailRhs A B C D E F 0| +
        |w 1| * |tailRhs a b c d e f 1 - tailRhs A B C D E F 1| +
        |w 2| * |tailRhs a b c d e f 2 - tailRhs A B C D E F 2| +
        |w 3| * |tailRhs a b c d e f 3 - tailRhs A B C D E F 3| := by
          simpa only [abs_mul] using abs_add_four_le
            (w 0 * (tailRhs a b c d e f 0 - tailRhs A B C D E F 0))
            (w 1 * (tailRhs a b c d e f 1 - tailRhs A B C D E F 1))
            (w 2 * (tailRhs a b c d e f 2 - tailRhs A B C D E F 2))
            (w 3 * (tailRhs a b c d e f 3 - tailRhs A B C D E F 3))
    _ ≤ (|w 0|+|w 1|+|w 2|+|w 3|)*(14*δ) := by
      calc
        _ ≤ |w 0| * (14 * δ) + |w 1| * (14 * δ) +
            |w 2| * (14 * δ) + |w 3| * (14 * δ) := by
          exact add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
        _ = _ := by ring
    _ ≤ 2*(14*δ) := by
      have hsum : |w 0|+|w 1|+|w 2|+|w 3| ≤ 2 := by simpa [wL1, Fin.sum_univ_four] using hw
      exact mul_le_mul_of_nonneg_right hsum (mul_nonneg (by norm_num) hδ)
    _ = 28*δ := by ring

lemma abs_wDotMCol_diff_le
    {δ a b c d e f A B C D E F : ℝ} {w : Vec4R}
    (hδ : 0 ≤ δ)
    (hclose : close6 δ a b c d e f A B C D E F)
    (hw : wL1 w ≤ 2) :
    ∀ j : Fin 4,
      |wDotMCol w a b c d e f j - wDotMCol w A B C D E F j| ≤ 4*δ := by
  have hM := tailMatrix_entry_diff_le_two_delta hδ hclose
  intro j
  have h0 := hM 0 j; have h1 := hM 1 j; have h2 := hM 2 j; have h3 := hM 3 j
  simp [wDotMCol, Fin.sum_univ_four]
  rw [show
    w 0 * tailMatrix a b c d e f 0 j + w 1 * tailMatrix a b c d e f 1 j +
      w 2 * tailMatrix a b c d e f 2 j + w 3 * tailMatrix a b c d e f 3 j -
    (w 0 * tailMatrix A B C D E F 0 j + w 1 * tailMatrix A B C D E F 1 j +
      w 2 * tailMatrix A B C D E F 2 j + w 3 * tailMatrix A B C D E F 3 j) =
    w 0*(tailMatrix a b c d e f 0 j-tailMatrix A B C D E F 0 j) +
    w 1*(tailMatrix a b c d e f 1 j-tailMatrix A B C D E F 1 j) +
    w 2*(tailMatrix a b c d e f 2 j-tailMatrix A B C D E F 2 j) +
    w 3*(tailMatrix a b c d e f 3 j-tailMatrix A B C D E F 3 j) by ring]
  calc
    |_ + _ + _ + _| ≤
      (|w 0|+|w 1|+|w 2|+|w 3|)*(2*δ) := by
        calc
          |_ + _ + _ + _| ≤
            |w 0| * |tailMatrix a b c d e f 0 j - tailMatrix A B C D E F 0 j| +
            |w 1| * |tailMatrix a b c d e f 1 j - tailMatrix A B C D E F 1 j| +
            |w 2| * |tailMatrix a b c d e f 2 j - tailMatrix A B C D E F 2 j| +
            |w 3| * |tailMatrix a b c d e f 3 j - tailMatrix A B C D E F 3 j| := by
              simpa only [abs_mul] using abs_add_four_le
                (w 0 * (tailMatrix a b c d e f 0 j - tailMatrix A B C D E F 0 j))
                (w 1 * (tailMatrix a b c d e f 1 j - tailMatrix A B C D E F 1 j))
                (w 2 * (tailMatrix a b c d e f 2 j - tailMatrix A B C D E F 2 j))
                (w 3 * (tailMatrix a b c d e f 3 j - tailMatrix A B C D E F 3 j))
          _ ≤ |w 0| * (2 * δ) + |w 1| * (2 * δ) +
              |w 2| * (2 * δ) + |w 3| * (2 * δ) := by
            exact add_le_add (add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
              (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
              (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
          _ = _ := by ring
    _ ≤ 2*(2*δ) := by
      have hsum : |w 0|+|w 1|+|w 2|+|w 3| ≤ 2 := by simpa [wL1, Fin.sum_univ_four] using hw
      exact mul_le_mul_of_nonneg_right hsum (mul_nonneg (by norm_num) hδ)
    _ = 4*δ := by ring

lemma weighted_tail_equation
    {a b c d e f g h j k : ℝ} {w : Vec4R}
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f) :
    wDotR w a b c d e f =
      wDotMCol w a b c d e f 0 * g +
      wDotMCol w a b c d e f 1 * h +
      wDotMCol w a b c d e f 2 * j +
      wDotMCol w a b c d e f 3 * k := by
  have h0 := congrFun hsol 0; have h1 := congrFun hsol 1
  have h2 := congrFun hsol 2; have h3 := congrFun hsol 3
  simp [wDotR, wDotMCol, Matrix.mulVec, dotProduct, tailVec, Fin.sum_univ_four] at h0 h1 h2 h3 ⊢
  linear_combination -(w 0)*h0 - (w 1)*h1 - (w 2)*h2 - (w 3)*h3

/-- Uniform contradiction used for all 20 exceptional candidate triples. -/
theorem no_tail_solution_near_exceptional_witness
    {δ a b c d e f A B C D E F g h j k : ℝ} {w : Vec4R}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 200000000000000 : ℝ))
    (hclose : close6 δ a b c d e f A B C D E F)
    (hu : unit6 a b c d e f) (hU : unit6 A B C D E F)
    (hg : |g| ≤ 1) (hh : |h| ≤ 1) (hj : |j| ≤ 1) (hk : |k| ≤ 1)
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f)
    (hw : wL1 w ≤ 2)
    (hR0 : (1 / 100 : ℝ) < |wDotR w A B C D E F|)
    (hM0 : ∀ q : Fin 4, |wDotMCol w A B C D E F q| < (1 / 1000000000 : ℝ)) :
    False := by
  have hRd := abs_wDotR_diff_le hδ hclose hu hU hw
  have hMd := abs_wDotMCol_diff_le hδ hclose hw
  have hEq := weighted_tail_equation (w := w) hsol
  have hm0 : |wDotMCol w a b c d e f 0| < (1/1000000000 : ℝ) + 4*δ := by
    have hd := hMd 0; have hc := hM0 0
    have htri : |wDotMCol w a b c d e f 0| ≤ |wDotMCol w A B C D E F 0| + |wDotMCol w a b c d e f 0 - wDotMCol w A B C D E F 0| := by
      calc |wDotMCol w a b c d e f 0| = |wDotMCol w A B C D E F 0 + (wDotMCol w a b c d e f 0-wDotMCol w A B C D E F 0)| := by congr 1; ring
           _ ≤ _ := abs_add_le _ _
    nlinarith
  have hm1 : |wDotMCol w a b c d e f 1| < (1/1000000000 : ℝ) + 4*δ := by
    have hd := hMd 1; have hc := hM0 1
    have htri : |wDotMCol w a b c d e f 1| ≤ |wDotMCol w A B C D E F 1| + |wDotMCol w a b c d e f 1 - wDotMCol w A B C D E F 1| := by
      calc |wDotMCol w a b c d e f 1| = |wDotMCol w A B C D E F 1 + (wDotMCol w a b c d e f 1-wDotMCol w A B C D E F 1)| := by congr 1; ring
           _ ≤ _ := abs_add_le _ _
    nlinarith
  have hm2 : |wDotMCol w a b c d e f 2| < (1/1000000000 : ℝ) + 4*δ := by
    have hd := hMd 2; have hc := hM0 2
    have htri : |wDotMCol w a b c d e f 2| ≤ |wDotMCol w A B C D E F 2| + |wDotMCol w a b c d e f 2 - wDotMCol w A B C D E F 2| := by
      calc |wDotMCol w a b c d e f 2| = |wDotMCol w A B C D E F 2 + (wDotMCol w a b c d e f 2-wDotMCol w A B C D E F 2)| := by congr 1; ring
           _ ≤ _ := abs_add_le _ _
    nlinarith
  have hm3 : |wDotMCol w a b c d e f 3| < (1/1000000000 : ℝ) + 4*δ := by
    have hd := hMd 3; have hc := hM0 3
    have htri : |wDotMCol w a b c d e f 3| ≤ |wDotMCol w A B C D E F 3| + |wDotMCol w a b c d e f 3 - wDotMCol w A B C D E F 3| := by
      calc |wDotMCol w a b c d e f 3| = |wDotMCol w A B C D E F 3 + (wDotMCol w a b c d e f 3-wDotMCol w A B C D E F 3)| := by congr 1; ring
           _ ≤ _ := abs_add_le _ _
    nlinarith
  have hRa : |wDotR w a b c d e f| < 4*((1/1000000000 : ℝ)+4*δ) := by
    rw [hEq]
    calc
      |_ + _ + _ + _| ≤ |wDotMCol w a b c d e f 0| * |g| +
        |wDotMCol w a b c d e f 1| * |h| +
        |wDotMCol w a b c d e f 2| * |j| + |wDotMCol w a b c d e f 3| * |k| := by
          simpa only [abs_mul] using abs_add_four_le
            (wDotMCol w a b c d e f 0 * g)
            (wDotMCol w a b c d e f 1 * h)
            (wDotMCol w a b c d e f 2 * j)
            (wDotMCol w a b c d e f 3 * k)
      _ < ((1/1000000000 : ℝ)+4*δ)*1 + ((1/1000000000 : ℝ)+4*δ)*1 +
          ((1/1000000000 : ℝ)+4*δ)*1 + ((1/1000000000 : ℝ)+4*δ)*1 := by
        have t0 : |wDotMCol w a b c d e f 0| * |g| < (1/1000000000 : ℝ) + 4*δ := by
          calc
            _ ≤ |wDotMCol w a b c d e f 0| * 1 :=
              mul_le_mul_of_nonneg_left hg (abs_nonneg _)
            _ < _ := by simpa using hm0
        have t1 : |wDotMCol w a b c d e f 1| * |h| < (1/1000000000 : ℝ) + 4*δ := by
          calc
            _ ≤ |wDotMCol w a b c d e f 1| * 1 :=
              mul_le_mul_of_nonneg_left hh (abs_nonneg _)
            _ < _ := by simpa using hm1
        have t2 : |wDotMCol w a b c d e f 2| * |j| < (1/1000000000 : ℝ) + 4*δ := by
          calc
            _ ≤ |wDotMCol w a b c d e f 2| * 1 :=
              mul_le_mul_of_nonneg_left hj (abs_nonneg _)
            _ < _ := by simpa using hm2
        have t3 : |wDotMCol w a b c d e f 3| * |k| < (1/1000000000 : ℝ) + 4*δ := by
          calc
            _ ≤ |wDotMCol w a b c d e f 3| * 1 :=
              mul_le_mul_of_nonneg_left hk (abs_nonneg _)
            _ < _ := by simpa using hm3
        nlinarith
      _ = 4*((1/1000000000 : ℝ)+4*δ) := by ring
  have hR0upper : |wDotR w A B C D E F| < 4*((1/1000000000 : ℝ)+4*δ) + 28*δ := by
    have htri : |wDotR w A B C D E F| ≤ |wDotR w a b c d e f| + |wDotR w a b c d e f - wDotR w A B C D E F| := by
      calc |wDotR w A B C D E F| = |wDotR w a b c d e f - (wDotR w a b c d e f-wDotR w A B C D E F)| := by congr 1; ring
           _ ≤ _ := abs_sub _ _
    nlinarith
  have hnum : 4*((1/1000000000 : ℝ)+4*δ) + 28*δ < 1/100 := by
    nlinarith
  linarith

end

end Biunimodular.F11
