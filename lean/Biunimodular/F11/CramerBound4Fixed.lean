/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-- Explicit 3×3 determinant, used only for the elementary 4×4 Cramer bound. -/
def det3r (a b c d e f g h i : ℝ) : ℝ :=
  a * (e*i - f*h) - b * (d*i - f*g) + c * (d*h - e*g)

/-- Explicit 4×4 determinant expanded along the first row. -/
def det4r
    (a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 : ℝ) : ℝ :=
  a00 * det3r a11 a12 a13 a21 a22 a23 a31 a32 a33
  - a01 * det3r a10 a12 a13 a20 a22 a23 a30 a32 a33
  + a02 * det3r a10 a11 a13 a20 a21 a23 a30 a31 a33
  - a03 * det3r a10 a11 a12 a20 a21 a22 a30 a31 a32

/-- Cramer numerator for coordinate 0. -/
def cramer0r (y0 y1 y2 y3 : ℝ)
    (a01 a02 a03 a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℝ) : ℝ :=
  y0 * det3r a11 a12 a13 a21 a22 a23 a31 a32 a33
  - y1 * det3r a01 a02 a03 a21 a22 a23 a31 a32 a33
  + y2 * det3r a01 a02 a03 a11 a12 a13 a31 a32 a33
  - y3 * det3r a01 a02 a03 a11 a12 a13 a21 a22 a23

/-- Cramer numerator for coordinate 1. -/
def cramer1r (y0 y1 y2 y3 : ℝ)
    (a00 a02 a03 a10 a12 a13 a20 a22 a23 a30 a32 a33 : ℝ) : ℝ :=
  -y0 * det3r a10 a12 a13 a20 a22 a23 a30 a32 a33
  + y1 * det3r a00 a02 a03 a20 a22 a23 a30 a32 a33
  - y2 * det3r a00 a02 a03 a10 a12 a13 a30 a32 a33
  + y3 * det3r a00 a02 a03 a10 a12 a13 a20 a22 a23

/-- Cramer numerator for coordinate 2. -/
def cramer2r (y0 y1 y2 y3 : ℝ)
    (a00 a01 a03 a10 a11 a13 a20 a21 a23 a30 a31 a33 : ℝ) : ℝ :=
  y0 * det3r a10 a11 a13 a20 a21 a23 a30 a31 a33
  - y1 * det3r a00 a01 a03 a20 a21 a23 a30 a31 a33
  + y2 * det3r a00 a01 a03 a10 a11 a13 a30 a31 a33
  - y3 * det3r a00 a01 a03 a10 a11 a13 a20 a21 a23

/-- Cramer numerator for coordinate 3. -/
def cramer3r (y0 y1 y2 y3 : ℝ)
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 a30 a31 a32 : ℝ) : ℝ :=
  -y0 * det3r a10 a11 a12 a20 a21 a22 a30 a31 a32
  + y1 * det3r a00 a01 a02 a20 a21 a22 a30 a31 a32
  - y2 * det3r a00 a01 a02 a10 a11 a12 a30 a31 a32
  + y3 * det3r a00 a01 a02 a10 a11 a12 a20 a21 a22

private lemma abs_add_le_via_sub (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  have h := abs_sub x (-y)
  simpa [abs_neg] using h

private lemma mul_abs_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y)
    (hX : 0 ≤ X) (_hY : 0 ≤ Y) : |x*y| ≤ X*Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hX

lemma abs_det3r_le_48 {a b c d e f g h i : ℝ}
    (ha : |a| ≤ 2) (hb : |b| ≤ 2) (hc : |c| ≤ 2)
    (hd : |d| ≤ 2) (he : |e| ≤ 2) (hf : |f| ≤ 2)
    (hg : |g| ≤ 2) (hh : |h| ≤ 2) (hi : |i| ≤ 2) :
    |det3r a b c d e f g h i| ≤ 48 := by
  have hei : |e*i| ≤ 4 := by
    calc
      |e*i| = |e| * |i| := abs_mul e i
      _ ≤ (2:ℝ)*2 := mul_le_mul he hi (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hfh : |f*h| ≤ 4 := by
    calc
      |f*h| = |f| * |h| := abs_mul f h
      _ ≤ (2:ℝ)*2 := mul_le_mul hf hh (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hdi : |d*i| ≤ 4 := by
    calc
      |d*i| = |d| * |i| := abs_mul d i
      _ ≤ (2:ℝ)*2 := mul_le_mul hd hi (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hfg : |f*g| ≤ 4 := by
    calc
      |f*g| = |f| * |g| := abs_mul f g
      _ ≤ (2:ℝ)*2 := mul_le_mul hf hg (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hdh : |d*h| ≤ 4 := by
    calc
      |d*h| = |d| * |h| := abs_mul d h
      _ ≤ (2:ℝ)*2 := mul_le_mul hd hh (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have heg : |e*g| ≤ 4 := by
    calc
      |e*g| = |e| * |g| := abs_mul e g
      _ ≤ (2:ℝ)*2 := mul_le_mul he hg (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have h1 : |e*i-f*h| ≤ 8 := by
    calc
      |e*i-f*h| ≤ |e*i| + |f*h| := abs_sub _ _
      _ ≤ 4 + 4 := add_le_add hei hfh
      _ = 8 := by norm_num
  have h2 : |d*i-f*g| ≤ 8 := by
    calc
      |d*i-f*g| ≤ |d*i| + |f*g| := abs_sub _ _
      _ ≤ 4 + 4 := add_le_add hdi hfg
      _ = 8 := by norm_num
  have h3 : |d*h-e*g| ≤ 8 := by
    calc
      |d*h-e*g| ≤ |d*h| + |e*g| := abs_sub _ _
      _ ≤ 4 + 4 := add_le_add hdh heg
      _ = 8 := by norm_num
  have ha1 : |a*(e*i-f*h)| ≤ 16 := by
    calc
      |a*(e*i-f*h)| = |a| * |e*i-f*h| := abs_mul a _
      _ ≤ (2:ℝ)*8 := mul_le_mul ha h1 (abs_nonneg _) (by norm_num)
      _ = 16 := by norm_num
  have hb2 : |b*(d*i-f*g)| ≤ 16 := by
    calc
      |b*(d*i-f*g)| = |b| * |d*i-f*g| := abs_mul b _
      _ ≤ (2:ℝ)*8 := mul_le_mul hb h2 (abs_nonneg _) (by norm_num)
      _ = 16 := by norm_num
  have hc3 : |c*(d*h-e*g)| ≤ 16 := by
    calc
      |c*(d*h-e*g)| = |c| * |d*h-e*g| := abs_mul c _
      _ ≤ (2:ℝ)*8 := mul_le_mul hc h3 (abs_nonneg _) (by norm_num)
      _ = 16 := by norm_num
  rw [det3r]
  calc
    |a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)|
        ≤ |a*(e*i-f*h) - b*(d*i-f*g)| + |c*(d*h-e*g)| := abs_add_le_via_sub _ _
    _ ≤ (|a*(e*i-f*h)| + |b*(d*i-f*g)|) + |c*(d*h-e*g)| := by
      gcongr
      exact abs_sub _ _
    _ ≤ (16 + 16) + 16 := add_le_add (add_le_add ha1 hb2) hc3
    _ = 48 := by norm_num

private lemma four_term_le {y0 y1 y2 y3 c0 c1 c2 c3 ε : ℝ}
    (hε : 0 ≤ ε)
    (hy0 : |y0| ≤ ε) (hy1 : |y1| ≤ ε) (hy2 : |y2| ≤ ε) (hy3 : |y3| ≤ ε)
    (hc0 : |c0| ≤ 48) (hc1 : |c1| ≤ 48) (hc2 : |c2| ≤ 48) (hc3 : |c3| ≤ 48) :
    |y0 * c0 - y1 * c1 + y2 * c2 - y3 * c3| ≤ 192 * ε := by
  have h0 : |y0 * c0| ≤ ε * 48 := mul_abs_le hy0 hc0 hε (by norm_num)
  have h1 : |y1 * c1| ≤ ε * 48 := mul_abs_le hy1 hc1 hε (by norm_num)
  have h2 : |y2 * c2| ≤ ε * 48 := mul_abs_le hy2 hc2 hε (by norm_num)
  have h3 : |y3 * c3| ≤ ε * 48 := mul_abs_le hy3 hc3 hε (by norm_num)
  calc
    |y0 * c0 - y1 * c1 + y2 * c2 - y3 * c3|
      ≤ |y0 * c0 - y1 * c1 + y2 * c2| + |y3 * c3| := abs_sub _ _
    _ ≤ (|y0 * c0 - y1 * c1| + |y2 * c2|) + |y3 * c3| := by
      gcongr
      exact abs_add_le_via_sub _ _
    _ ≤ ((|y0 * c0| + |y1 * c1|) + |y2 * c2|) + |y3 * c3| := by
      gcongr
      exact abs_sub _ _
    _ ≤ ((ε * 48 + ε * 48) + ε * 48) + ε * 48 :=
      add_le_add (add_le_add (add_le_add h0 h1) h2) h3
    _ = 192 * ε := by ring

lemma cramer0_identity
    {a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 z0 z1 z2 z3 y0 y1 y2 y3 : ℝ}
    (h0 : a00 * z0 + a01 * z1 + a02 * z2 + a03 * z3 = y0)
    (h1 : a10 * z0 + a11 * z1 + a12 * z2 + a13 * z3 = y1)
    (h2 : a20 * z0 + a21 * z1 + a22 * z2 + a23 * z3 = y2)
    (h3 : a30 * z0 + a31 * z1 + a32 * z2 + a33 * z3 = y3) :
    det4r a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 * z0 =
      cramer0r y0 y1 y2 y3 a01 a02 a03 a11 a12 a13 a21 a22 a23 a31 a32 a33 := by
  rw [← h0, ← h1, ← h2, ← h3]
  simp only [det4r, cramer0r, det3r]
  ring

lemma cramer1_identity
    {a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 z0 z1 z2 z3 y0 y1 y2 y3 : ℝ}
    (h0 : a00 * z0 + a01 * z1 + a02 * z2 + a03 * z3 = y0)
    (h1 : a10 * z0 + a11 * z1 + a12 * z2 + a13 * z3 = y1)
    (h2 : a20 * z0 + a21 * z1 + a22 * z2 + a23 * z3 = y2)
    (h3 : a30 * z0 + a31 * z1 + a32 * z2 + a33 * z3 = y3) :
    det4r a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 * z1 =
      cramer1r y0 y1 y2 y3 a00 a02 a03 a10 a12 a13 a20 a22 a23 a30 a32 a33 := by
  rw [← h0, ← h1, ← h2, ← h3]
  simp only [det4r, cramer1r, det3r]
  ring

lemma cramer2_identity
    {a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 z0 z1 z2 z3 y0 y1 y2 y3 : ℝ}
    (h0 : a00 * z0 + a01 * z1 + a02 * z2 + a03 * z3 = y0)
    (h1 : a10 * z0 + a11 * z1 + a12 * z2 + a13 * z3 = y1)
    (h2 : a20 * z0 + a21 * z1 + a22 * z2 + a23 * z3 = y2)
    (h3 : a30 * z0 + a31 * z1 + a32 * z2 + a33 * z3 = y3) :
    det4r a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 * z2 =
      cramer2r y0 y1 y2 y3 a00 a01 a03 a10 a11 a13 a20 a21 a23 a30 a31 a33 := by
  rw [← h0, ← h1, ← h2, ← h3]
  simp only [det4r, cramer2r, det3r]
  ring

lemma cramer3_identity
    {a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 z0 z1 z2 z3 y0 y1 y2 y3 : ℝ}
    (h0 : a00 * z0 + a01 * z1 + a02 * z2 + a03 * z3 = y0)
    (h1 : a10 * z0 + a11 * z1 + a12 * z2 + a13 * z3 = y1)
    (h2 : a20 * z0 + a21 * z1 + a22 * z2 + a23 * z3 = y2)
    (h3 : a30 * z0 + a31 * z1 + a32 * z2 + a33 * z3 = y3) :
    det4r a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 * z3 =
      cramer3r y0 y1 y2 y3 a00 a01 a02 a10 a11 a12 a20 a21 a22 a30 a31 a32 := by
  rw [← h0, ← h1, ← h2, ← h3]
  simp only [det4r, cramer3r, det3r]
  ring

lemma abs_cramer0r_le_192 {y0 y1 y2 y3 ε : ℝ}
    {a01 a02 a03 a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℝ}
    (hε : 0 ≤ ε) (hy0 : |y0| ≤ ε) (hy1 : |y1| ≤ ε) (hy2 : |y2| ≤ ε) (hy3 : |y3| ≤ ε)
    (h01 : |a01| ≤ 2) (h02 : |a02| ≤ 2) (h03 : |a03| ≤ 2)
    (h11 : |a11| ≤ 2) (h12 : |a12| ≤ 2) (h13 : |a13| ≤ 2)
    (h21 : |a21| ≤ 2) (h22 : |a22| ≤ 2) (h23 : |a23| ≤ 2)
    (h31 : |a31| ≤ 2) (h32 : |a32| ≤ 2) (h33 : |a33| ≤ 2) :
    |cramer0r y0 y1 y2 y3 a01 a02 a03 a11 a12 a13 a21 a22 a23 a31 a32 a33| ≤ 192 * ε := by
  apply four_term_le hε hy0 hy1 hy2 hy3
  · exact abs_det3r_le_48 h11 h12 h13 h21 h22 h23 h31 h32 h33
  · exact abs_det3r_le_48 h01 h02 h03 h21 h22 h23 h31 h32 h33
  · exact abs_det3r_le_48 h01 h02 h03 h11 h12 h13 h31 h32 h33
  · exact abs_det3r_le_48 h01 h02 h03 h11 h12 h13 h21 h22 h23

lemma abs_cramer1r_le_192 {y0 y1 y2 y3 ε : ℝ}
    {a00 a02 a03 a10 a12 a13 a20 a22 a23 a30 a32 a33 : ℝ}
    (hε : 0 ≤ ε) (hy0 : |y0| ≤ ε) (hy1 : |y1| ≤ ε) (hy2 : |y2| ≤ ε) (hy3 : |y3| ≤ ε)
    (h00 : |a00| ≤ 2) (h02 : |a02| ≤ 2) (h03 : |a03| ≤ 2)
    (h10 : |a10| ≤ 2) (h12 : |a12| ≤ 2) (h13 : |a13| ≤ 2)
    (h20 : |a20| ≤ 2) (h22 : |a22| ≤ 2) (h23 : |a23| ≤ 2)
    (h30 : |a30| ≤ 2) (h32 : |a32| ≤ 2) (h33 : |a33| ≤ 2) :
    |cramer1r y0 y1 y2 y3 a00 a02 a03 a10 a12 a13 a20 a22 a23 a30 a32 a33| ≤ 192 * ε := by
  let d0 := det3r a10 a12 a13 a20 a22 a23 a30 a32 a33
  let d1 := det3r a00 a02 a03 a20 a22 a23 a30 a32 a33
  let d2 := det3r a00 a02 a03 a10 a12 a13 a30 a32 a33
  let d3 := det3r a00 a02 a03 a10 a12 a13 a20 a22 a23
  have hd0 : |d0| ≤ 48 := abs_det3r_le_48 h10 h12 h13 h20 h22 h23 h30 h32 h33
  have hd1 : |d1| ≤ 48 := abs_det3r_le_48 h00 h02 h03 h20 h22 h23 h30 h32 h33
  have hd2 : |d2| ≤ 48 := abs_det3r_le_48 h00 h02 h03 h10 h12 h13 h30 h32 h33
  have hd3 : |d3| ≤ 48 := abs_det3r_le_48 h00 h02 h03 h10 h12 h13 h20 h22 h23
  have h := four_term_le hε hy0 hy1 hy2 hy3 hd0 hd1 hd2 hd3
  have heq : cramer1r y0 y1 y2 y3 a00 a02 a03 a10 a12 a13 a20 a22 a23 a30 a32 a33 =
      -(y0 * d0 - y1 * d1 + y2 * d2 - y3 * d3) := by
    simp [cramer1r, d0, d1, d2, d3]
    ring
  rw [heq, abs_neg]
  exact h

lemma abs_cramer2r_le_192 {y0 y1 y2 y3 ε : ℝ}
    {a00 a01 a03 a10 a11 a13 a20 a21 a23 a30 a31 a33 : ℝ}
    (hε : 0 ≤ ε) (hy0 : |y0| ≤ ε) (hy1 : |y1| ≤ ε) (hy2 : |y2| ≤ ε) (hy3 : |y3| ≤ ε)
    (h00 : |a00| ≤ 2) (h01 : |a01| ≤ 2) (h03 : |a03| ≤ 2)
    (h10 : |a10| ≤ 2) (h11 : |a11| ≤ 2) (h13 : |a13| ≤ 2)
    (h20 : |a20| ≤ 2) (h21 : |a21| ≤ 2) (h23 : |a23| ≤ 2)
    (h30 : |a30| ≤ 2) (h31 : |a31| ≤ 2) (h33 : |a33| ≤ 2) :
    |cramer2r y0 y1 y2 y3 a00 a01 a03 a10 a11 a13 a20 a21 a23 a30 a31 a33| ≤ 192 * ε := by
  apply four_term_le hε hy0 hy1 hy2 hy3
  · exact abs_det3r_le_48 h10 h11 h13 h20 h21 h23 h30 h31 h33
  · exact abs_det3r_le_48 h00 h01 h03 h20 h21 h23 h30 h31 h33
  · exact abs_det3r_le_48 h00 h01 h03 h10 h11 h13 h30 h31 h33
  · exact abs_det3r_le_48 h00 h01 h03 h10 h11 h13 h20 h21 h23

lemma abs_cramer3r_le_192 {y0 y1 y2 y3 ε : ℝ}
    {a00 a01 a02 a10 a11 a12 a20 a21 a22 a30 a31 a32 : ℝ}
    (hε : 0 ≤ ε) (hy0 : |y0| ≤ ε) (hy1 : |y1| ≤ ε) (hy2 : |y2| ≤ ε) (hy3 : |y3| ≤ ε)
    (h00 : |a00| ≤ 2) (h01 : |a01| ≤ 2) (h02 : |a02| ≤ 2)
    (h10 : |a10| ≤ 2) (h11 : |a11| ≤ 2) (h12 : |a12| ≤ 2)
    (h20 : |a20| ≤ 2) (h21 : |a21| ≤ 2) (h22 : |a22| ≤ 2)
    (h30 : |a30| ≤ 2) (h31 : |a31| ≤ 2) (h32 : |a32| ≤ 2) :
    |cramer3r y0 y1 y2 y3 a00 a01 a02 a10 a11 a12 a20 a21 a22 a30 a31 a32| ≤ 192 * ε := by
  let d0 := det3r a10 a11 a12 a20 a21 a22 a30 a31 a32
  let d1 := det3r a00 a01 a02 a20 a21 a22 a30 a31 a32
  let d2 := det3r a00 a01 a02 a10 a11 a12 a30 a31 a32
  let d3 := det3r a00 a01 a02 a10 a11 a12 a20 a21 a22
  have hd0 : |d0| ≤ 48 := abs_det3r_le_48 h10 h11 h12 h20 h21 h22 h30 h31 h32
  have hd1 : |d1| ≤ 48 := abs_det3r_le_48 h00 h01 h02 h20 h21 h22 h30 h31 h32
  have hd2 : |d2| ≤ 48 := abs_det3r_le_48 h00 h01 h02 h10 h11 h12 h30 h31 h32
  have hd3 : |d3| ≤ 48 := abs_det3r_le_48 h00 h01 h02 h10 h11 h12 h20 h21 h22
  have h := four_term_le hε hy0 hy1 hy2 hy3 hd0 hd1 hd2 hd3
  have heq : cramer3r y0 y1 y2 y3 a00 a01 a02 a10 a11 a12 a20 a21 a22 a30 a31 a32 =
      -(y0 * d0 - y1 * d1 + y2 * d2 - y3 * d3) := by
    simp [cramer3r, d0, d1, d2, d3]
    ring
  rw [heq, abs_neg]
  exact h

end Biunimodular.F11
