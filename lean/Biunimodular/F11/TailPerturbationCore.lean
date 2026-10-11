/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.TailLinearSystem

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Biunimodular.F11

def close6 (δ a b c d e f A B C D E F : ℝ) : Prop :=
  |a - A| ≤ δ ∧ |b - B| ≤ δ ∧ |c - C| ≤ δ ∧
  |d - D| ≤ δ ∧ |e - E| ≤ δ ∧ |f - F| ≤ δ

def unit6 (a b c d e f : ℝ) : Prop :=
  |a| ≤ 1 ∧ |b| ≤ 1 ∧ |c| ≤ 1 ∧
  |d| ≤ 1 ∧ |e| ≤ 1 ∧ |f| ≤ 1

lemma abs_pair_sum_le_two_delta
    {δ x y X Y : ℝ}
    (_hδ : 0 ≤ δ)
    (hx : |x - X| ≤ δ)
    (hy : |y - Y| ≤ δ) :
    |(x + y) - (X + Y)| ≤ 2 * δ := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  rw [abs_le]
  constructor <;> nlinarith

lemma abs_pair_diff_le_two_delta
    {δ x y X Y : ℝ}
    (_hδ : 0 ≤ δ)
    (hx : |x - X| ≤ δ)
    (hy : |y - Y| ≤ δ) :
    |(x - y) - (X - Y)| ≤ 2 * δ := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  rw [abs_le]
  constructor <;> nlinarith

lemma abs_mul_sub_mul_le_two_delta
    {δ x y X Y : ℝ}
    (hδ : 0 ≤ δ)
    (hx : |x - X| ≤ δ)
    (hy : |y - Y| ≤ δ)
    (hy1 : |y| ≤ 1)
    (hX1 : |X| ≤ 1) :
    |x * y - X * Y| ≤ 2 * δ := by
  have hxy : |(x - X) * y| ≤ δ := by
    rw [abs_mul]
    simpa using mul_le_mul hx hy1 (abs_nonneg y) hδ
  have hXY : |X * (y - Y)| ≤ δ := by
    rw [abs_mul]
    simpa using mul_le_mul hX1 hy (abs_nonneg (y - Y)) (by norm_num : (0 : ℝ) ≤ 1)
  have hxy' := abs_le.mp hxy
  have hXY' := abs_le.mp hXY
  rw [show x * y - X * Y = (x - X) * y + X * (y - Y) by ring]
  rw [abs_le]
  constructor <;> nlinarith

lemma tailMatrix_entry_diff_le_two_delta
    {δ a b c d e f A B C D E F : ℝ}
    (hδ : 0 ≤ δ)
    (hclose : close6 δ a b c d e f A B C D E F) :
    ∀ i j : Fin 4,
      |tailMatrix a b c d e f i j -
        tailMatrix A B C D E F i j| ≤ 2 * δ := by
  rcases hclose with ⟨ha, hb, hc, hd, he, hf⟩
  have ha2 : |a - A| ≤ 2 * δ := by linarith
  have hb2 : |b - B| ≤ 2 * δ := by linarith
  have hc2 : |c - C| ≤ 2 * δ := by linarith
  have hd2 : |d - D| ≤ 2 * δ := by linarith
  have he2 : |e - E| ≤ 2 * δ := by linarith
  have hf2 : |f - F| ≤ 2 * δ := by linarith
  have he2neg : |-e + E| ≤ 2 * δ := by
    rw [show -e + E = -(e - E) by ring, abs_neg]
    exact he2
  have hf2neg : |-f + F| ≤ 2 * δ := by
    rw [show -f + F = -(f - F) by ring, abs_neg]
    exact hf2
  have hec := abs_pair_diff_le_two_delta hδ he hc
  have hfd := abs_pair_diff_le_two_delta hδ hf hd
  have hce := abs_pair_sum_le_two_delta hδ hc he
  have hdf := abs_pair_sum_le_two_delta hδ hd hf
  have hac := abs_pair_sum_le_two_delta hδ ha hc
  have hbd := abs_pair_sum_le_two_delta hδ hb hd
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [tailMatrix] using hec
  · simpa [tailMatrix] using hfd
  · simpa [tailMatrix] using he2neg
  · simpa [tailMatrix] using hf2neg
  · simpa [tailMatrix] using ha2
  · simpa [tailMatrix] using hb2
  · simpa [tailMatrix] using hce
  · simpa [tailMatrix] using hdf
  · simpa [tailMatrix] using he2
  · simpa [tailMatrix] using hf2
  · simpa [tailMatrix] using hac
  · simpa [tailMatrix] using hbd
  · simpa [tailMatrix] using hac
  · simpa [tailMatrix] using hbd
  · simpa [tailMatrix] using ha2
  · simpa [tailMatrix] using hb2

lemma tailRhs_diff_le_fourteen_delta
    {δ a b c d e f A B C D E F : ℝ}
    (hδ : 0 ≤ δ)
    (hclose : close6 δ a b c d e f A B C D E F)
    (hu : unit6 a b c d e f)
    (hU : unit6 A B C D E F) :
    ∀ i : Fin 4,
      |tailRhs a b c d e f i -
        tailRhs A B C D E F i| ≤ 14 * δ := by
  rcases hclose with ⟨ha, hb, hc, hd, he, hf⟩
  rcases hu with ⟨hua, hub, huc, hud, hue, huf⟩
  rcases hU with ⟨hUA, hUB, hUC, hUD, hUE, hUF⟩
  have hac := abs_mul_sub_mul_le_two_delta hδ ha hc huc hUA
  have hbd := abs_mul_sub_mul_le_two_delta hδ hb hd hud hUB
  have hce := abs_mul_sub_mul_le_two_delta hδ hc he hue hUC
  have hdf := abs_mul_sub_mul_le_two_delta hδ hd hf huf hUD
  have hae := abs_mul_sub_mul_le_two_delta hδ ha he hue hUA
  have hbf := abs_mul_sub_mul_le_two_delta hδ hb hf huf hUB
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hd' := abs_le.mp hd
  have he' := abs_le.mp he
  have hf' := abs_le.mp hf
  have hac' := abs_le.mp hac
  have hbd' := abs_le.mp hbd
  have hce' := abs_le.mp hce
  have hdf' := abs_le.mp hdf
  have hae' := abs_le.mp hae
  have hbf' := abs_le.mp hbf
  intro i
  fin_cases i <;>
    simp [tailRhs] <;>
    rw [abs_le] <;>
    constructor <;>
    nlinarith

lemma tailMatrix_mulVec_diff_le_eight_delta
    {δ a b c d e f A B C D E F g h j k : ℝ}
    (hδ : 0 ≤ δ)
    (hclose : close6 δ a b c d e f A B C D E F)
    (hg : |g| ≤ 1)
    (hh : |h| ≤ 1)
    (hj : |j| ≤ 1)
    (hk : |k| ≤ 1) :
    ∀ i : Fin 4,
      |((tailMatrix a b c d e f -
          tailMatrix A B C D E F).mulVec
          (tailVec g h j k)) i| ≤ 8 * δ := by
  have hentry := tailMatrix_entry_diff_le_two_delta hδ hclose
  intro i
  have h0 := hentry i 0
  have h1 := hentry i 1
  have h2 := hentry i 2
  have h3 := hentry i 3
  have h2δ : 0 ≤ 2 * δ := by positivity
  have t0 :
      |(tailMatrix a b c d e f i 0 -
          tailMatrix A B C D E F i 0) * g| ≤ 2 * δ := by
    rw [abs_mul]
    simpa using mul_le_mul h0 hg (abs_nonneg g) h2δ
  have t1 :
      |(tailMatrix a b c d e f i 1 -
          tailMatrix A B C D E F i 1) * h| ≤ 2 * δ := by
    rw [abs_mul]
    simpa using mul_le_mul h1 hh (abs_nonneg h) h2δ
  have t2 :
      |(tailMatrix a b c d e f i 2 -
          tailMatrix A B C D E F i 2) * j| ≤ 2 * δ := by
    rw [abs_mul]
    simpa using mul_le_mul h2 hj (abs_nonneg j) h2δ
  have t3 :
      |(tailMatrix a b c d e f i 3 -
          tailMatrix A B C D E F i 3) * k| ≤ 2 * δ := by
    rw [abs_mul]
    simpa using mul_le_mul h3 hk (abs_nonneg k) h2δ
  have t0' := abs_le.mp t0
  have t1' := abs_le.mp t1
  have t2' := abs_le.mp t2
  have t3' := abs_le.mp t3
  simp only [Matrix.mulVec, dotProduct, tailVec, Fin.sum_univ_four]
  change |(tailMatrix a b c d e f i 0 - tailMatrix A B C D E F i 0) * g +
      (tailMatrix a b c d e f i 1 - tailMatrix A B C D E F i 1) * h +
      (tailMatrix a b c d e f i 2 - tailMatrix A B C D E F i 2) * j +
      (tailMatrix a b c d e f i 3 - tailMatrix A B C D E F i 3) * k| ≤ 8 * δ
  rw [abs_le]
  constructor <;> linarith [t0'.1, t0'.2, t1'.1, t1'.2, t2'.1, t2'.2, t3'.1, t3'.2]

end Biunimodular.F11
