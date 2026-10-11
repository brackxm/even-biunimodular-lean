/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.P150CofactorPositive11
public import Biunimodular.F11.P150PhaseExhaustionBridge11
public import Biunimodular.F11.SquaredKRootCover40Data
public meta import Biunimodular.F11.P150CofactorPositive11
public meta import Biunimodular.F11.P150PhaseExhaustionBridge11
public meta import Biunimodular.F11.SquaredKRootCover40Data

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Assembly of the P150 coordinate root cover

This file organizes the exact coordinate-cover certificates into their
natural layers:

* elimination of a phase solution to the polynomial `H252`;
* isolation of real `P150` roots into the forty squared-coordinate intervals;
* interval and circle geometry locating one of the 160 signed phase centers.

The `R102` branch is not an input: it is discharged by the exact Bernstein
positivity certificate in `P150CofactorPositive11`.
-/

def p150KQ11 : ℚ[X] := p150K11.map (Int.castRingHom ℚ)
def p150KR11 : ℝ[X] := p150KQ11.map (algebraMap ℚ ℝ)

/-- Rational form of the full eliminant. -/
def h252KQ11 : ℚ[X] := p150KQ11 * r102KQ11
def h252KR11 : ℝ[X] := h252KQ11.map (algebraMap ℚ ℝ)

theorem r102KQ11_eq_map_integer :
    r102KQ11 = r102K11.map (Int.castRingHom ℚ) := by
  rw [r102KQ11, r102K11, r102SquaredYQ11_eq_map_integer,
    Polynomial.map_comp]
  simp

theorem h252KQ11_eq_map_integer :
    h252KQ11 = h252K11.map (Int.castRingHom ℚ) := by
  rw [h252KQ11, h252K11, Polynomial.map_mul, p150KQ11,
    r102KQ11_eq_map_integer]

/-- Kernel-facing statement supplied by a replay of the localized `H252`
shape/elimination calculation. -/
structure H252PhaseEliminationCertificate11 where
  phase_k_isRoot : ∀ (x : PhaseCoords11), x.IsPhaseSolution →
    h252KR11.IsRoot x.k

def squaredKInInterval11 (k : ℝ) (I : TaggedRootInterval) : Prop :=
  (I.box.lo : ℝ) ≤ k ^ 2 ∧ k ^ 2 ≤ (I.box.hi : ℝ)

/-- Exact real-root isolation statement for the forty positive roots of the
three factors of `P150(y)`. -/
structure P150SquaredRootIsolationCertificate11 where
  cover : ∀ k : ℝ, |k| ≤ 1 → p150KR11.IsRoot k →
    ∃ q : Fin 40,
      squaredKInInterval11 k (squaredKRootIntervals40[q.1]!)

/-- Pure ordered-ring geometry turning a squared-root interval and
`j²+k²=1` into one of the 160 signed coordinate boxes. -/
structure SquaredKIntervalPhaseCenterCertificate11 where
  cover : ∀ (j k : ℝ) (q : Fin 40),
    squaredKInInterval11 k (squaredKRootIntervals40[q.1]!) →
    j ^ 2 + k ^ 2 = 1 →
    ∃ i : Fin 160,
      closePhaseCandidate11 p150PhaseRootRadius11 j k i

/-- The four sign choices belonging to squared-root interval `q`. -/
def phaseCenterBlockIndex11 (q : Fin 40) (o : Fin 4) : Fin 160 :=
  ⟨4 * q.1 + o.1, by omega⟩

def centerCoordQ11 (x : Int) : ℚ :=
  (x : ℚ) / (phaseCenterScale : ℚ)

def p150PhaseRootRadiusQ11 : ℚ := 1 / 200000000000000

/-- Every rational isolating interval fits inside the squared image of the
`5·10⁻¹⁵` box around its positive-positive phase center.  The complementary
real coordinate has the same property after `j² = 1-k²` is used. -/
theorem squaredK_interval_positive_center_bounds11 :
    ∀ q : Fin 40,
      let I := squaredKRootIntervals40[q.1]!
      let z := phaseCenters160[(phaseCenterBlockIndex11 q ⟨3, by omega⟩).1]!
      let re := centerCoordQ11 z.re
      let im := centerCoordQ11 z.im
      0 < re - p150PhaseRootRadiusQ11 ∧
      0 < im - p150PhaseRootRadiusQ11 ∧
      (im - p150PhaseRootRadiusQ11) ^ 2 ≤ I.box.lo ∧
      I.box.hi ≤ (im + p150PhaseRootRadiusQ11) ^ 2 ∧
      (re - p150PhaseRootRadiusQ11) ^ 2 ≤ 1 - I.box.hi ∧
      1 - I.box.lo ≤ (re + p150PhaseRootRadiusQ11) ^ 2 := by
  native_decide

/-- Exact sign layout of each four-center block. -/
theorem phaseCenterBlock_signs11 :
    ∀ q : Fin 40,
      let z0 := phaseCenters160[(phaseCenterBlockIndex11 q ⟨0, by omega⟩).1]!
      let z1 := phaseCenters160[(phaseCenterBlockIndex11 q ⟨1, by omega⟩).1]!
      let z2 := phaseCenters160[(phaseCenterBlockIndex11 q ⟨2, by omega⟩).1]!
      let z3 := phaseCenters160[(phaseCenterBlockIndex11 q ⟨3, by omega⟩).1]!
      z0.re = -z3.re ∧ z0.im = -z3.im ∧
      z1.re = -z3.re ∧ z1.im = z3.im ∧
      z2.re = z3.re ∧ z2.im = -z3.im := by
  native_decide

private theorem abs_sub_center_le_of_sq_bounds
    (x c δ lo hi : ℝ)
    (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hc : 0 < c - δ)
    (hclo : (c - δ) ^ 2 ≤ lo) (hlox : lo ≤ x ^ 2)
    (hxhi : x ^ 2 ≤ hi) (hhic : hi ≤ (c + δ) ^ 2) :
    |x - c| ≤ δ := by
  have hleft : c - δ ≤ x := by
    by_contra h
    have hlt : x < c - δ := lt_of_not_ge h
    have hprod : 0 < (c - δ - x) * (c - δ + x) :=
      mul_pos (sub_pos.mpr hlt) (by linarith)
    nlinarith
  have hright : x ≤ c + δ := by
    by_contra h
    have hlt : c + δ < x := lt_of_not_ge h
    have hcplus : 0 < c + δ := by linarith
    have hprod : 0 < (x - (c + δ)) * (x + (c + δ)) :=
      mul_pos (sub_pos.mpr hlt) (by linarith)
    nlinarith
  rw [abs_le]
  constructor <;> linarith

private theorem abs_sub_neg_center_le_of_sq_bounds
    (x c δ lo hi : ℝ)
    (hδ : 0 ≤ δ) (hx : x < 0) (hc : 0 < c - δ)
    (hclo : (c - δ) ^ 2 ≤ lo) (hlox : lo ≤ x ^ 2)
    (hxhi : x ^ 2 ≤ hi) (hhic : hi ≤ (c + δ) ^ 2) :
    |x - (-c)| ≤ δ := by
  have h := abs_sub_center_le_of_sq_bounds (-x) c δ lo hi hδ
    (by linarith) hc hclo (by nlinarith) (by nlinarith) hhic
  calc
    |x - (-c)| = |-x - c| := by
      rw [show -x - c = -(x - -c) by ring, abs_neg]
    _ ≤ δ := h

theorem centerCoordR_neg11 (x : Int) :
    centerCoordR (-x) = -centerCoordR x := by
  simp [centerCoordR]
  ring

/-- Strong form of the interval-to-center geometry: the returned center is
one of the four sign choices in the same squared-root block. -/
theorem squaredK_interval_phase_center_block11
    (j k : ℝ) (q : Fin 40)
    (hkI : squaredKInInterval11 k (squaredKRootIntervals40[q.1]!))
    (hjk : j ^ 2 + k ^ 2 = 1) :
    ∃ o : Fin 4,
      closePhaseCandidate11 p150PhaseRootRadius11 j k
        (phaseCenterBlockIndex11 q o) := by
    let I := squaredKRootIntervals40[q.1]!
    let z0 := phaseCenters160[(phaseCenterBlockIndex11 q ⟨0, by omega⟩).1]!
    let z1 := phaseCenters160[(phaseCenterBlockIndex11 q ⟨1, by omega⟩).1]!
    let z2 := phaseCenters160[(phaseCenterBlockIndex11 q ⟨2, by omega⟩).1]!
    let z3 := phaseCenters160[(phaseCenterBlockIndex11 q ⟨3, by omega⟩).1]!
    let re : ℝ := centerCoordR z3.re
    let im : ℝ := centerCoordR z3.im
    let δ : ℝ := p150PhaseRootRadius11
    have hbQ := squaredK_interval_positive_center_bounds11 q
    change
      0 < centerCoordQ11 z3.re - p150PhaseRootRadiusQ11 ∧
      0 < centerCoordQ11 z3.im - p150PhaseRootRadiusQ11 ∧
      (centerCoordQ11 z3.im - p150PhaseRootRadiusQ11) ^ 2 ≤ I.box.lo ∧
      I.box.hi ≤
        (centerCoordQ11 z3.im + p150PhaseRootRadiusQ11) ^ 2 ∧
      (centerCoordQ11 z3.re - p150PhaseRootRadiusQ11) ^ 2 ≤
        1 - I.box.hi ∧
      1 - I.box.lo ≤
        (centerCoordQ11 z3.re + p150PhaseRootRadiusQ11) ^ 2 at hbQ
    have hbR :
      0 < re - δ ∧ 0 < im - δ ∧
      (im - δ) ^ 2 ≤ (I.box.lo : ℝ) ∧
      (I.box.hi : ℝ) ≤ (im + δ) ^ 2 ∧
      (re - δ) ^ 2 ≤ 1 - (I.box.hi : ℝ) ∧
      1 - (I.box.lo : ℝ) ≤ (re + δ) ^ 2 := by
      dsimp [re, im, δ, centerCoordR, centerCoordQ11,
        p150PhaseRootRadius11, p150PhaseRootRadiusQ11] at hbQ ⊢
      rcases hbQ with ⟨h1, h2, h3, h4, h5, h6⟩
      constructor
      · have h := (Rat.cast_pos (K := ℝ)).mpr h1
        push_cast at h
        exact h
      constructor
      · have h := (Rat.cast_pos (K := ℝ)).mpr h2
        push_cast at h
        exact h
      constructor
      · have h := (Rat.cast_le (K := ℝ)).mpr h3
        push_cast at h
        exact h
      constructor
      · have h := (Rat.cast_le (K := ℝ)).mpr h4
        push_cast at h
        exact h
      constructor
      · have h := (Rat.cast_le (K := ℝ)).mpr h5
        push_cast at h
        exact h
      · have h := (Rat.cast_le (K := ℝ)).mpr h6
        push_cast at h
        exact h
    have hδ : 0 ≤ δ := by norm_num [δ, p150PhaseRootRadius11]
    have hklo : (I.box.lo : ℝ) ≤ k ^ 2 := hkI.1
    have hkhi : k ^ 2 ≤ (I.box.hi : ℝ) := hkI.2
    have hjlo : 1 - (I.box.hi : ℝ) ≤ j ^ 2 := by nlinarith
    have hjhi : j ^ 2 ≤ 1 - (I.box.lo : ℝ) := by nlinarith
    have hs := phaseCenterBlock_signs11 q
    change
      z0.re = -z3.re ∧ z0.im = -z3.im ∧
      z1.re = -z3.re ∧ z1.im = z3.im ∧
      z2.re = z3.re ∧ z2.im = -z3.im at hs
    by_cases hj : 0 ≤ j
    · have hjclose : |j - re| ≤ δ :=
        abs_sub_center_le_of_sq_bounds j re δ
          (1 - (I.box.hi : ℝ)) (1 - (I.box.lo : ℝ))
          hδ hj hbR.1 hbR.2.2.2.2.1 hjlo hjhi hbR.2.2.2.2.2
      by_cases hk : 0 ≤ k
      · have hkclose : |k - im| ≤ δ :=
          abs_sub_center_le_of_sq_bounds k im δ
            (I.box.lo : ℝ) (I.box.hi : ℝ)
            hδ hk hbR.2.1 hbR.2.2.1 hklo hkhi hbR.2.2.2.1
        refine ⟨⟨3, by omega⟩, ?_⟩
        exact ⟨hjclose, hkclose⟩
      · have hkneg : k < 0 := lt_of_not_ge hk
        have hkclose : |k - (-im)| ≤ δ :=
          abs_sub_neg_center_le_of_sq_bounds k im δ
            (I.box.lo : ℝ) (I.box.hi : ℝ)
            hδ hkneg hbR.2.1 hbR.2.2.1 hklo hkhi hbR.2.2.2.1
        refine ⟨⟨2, by omega⟩, ?_⟩
        change |j - centerCoordR z2.re| ≤ δ ∧
          |k - centerCoordR z2.im| ≤ δ
        have hzre : centerCoordR z2.re = re := by
          rw [hs.2.2.2.2.1]
        have hzim : centerCoordR z2.im = -im := by
          rw [hs.2.2.2.2.2, centerCoordR_neg11]
        simpa [hzre, hzim] using And.intro hjclose hkclose
    · have hjneg : j < 0 := lt_of_not_ge hj
      have hjclose : |j - (-re)| ≤ δ :=
        abs_sub_neg_center_le_of_sq_bounds j re δ
          (1 - (I.box.hi : ℝ)) (1 - (I.box.lo : ℝ))
          hδ hjneg hbR.1 hbR.2.2.2.2.1 hjlo hjhi hbR.2.2.2.2.2
      by_cases hk : 0 ≤ k
      · have hkclose : |k - im| ≤ δ :=
          abs_sub_center_le_of_sq_bounds k im δ
            (I.box.lo : ℝ) (I.box.hi : ℝ)
            hδ hk hbR.2.1 hbR.2.2.1 hklo hkhi hbR.2.2.2.1
        refine ⟨⟨1, by omega⟩, ?_⟩
        change |j - centerCoordR z1.re| ≤ δ ∧
          |k - centerCoordR z1.im| ≤ δ
        have hzre : centerCoordR z1.re = -re := by
          rw [hs.2.2.1, centerCoordR_neg11]
        have hzim : centerCoordR z1.im = im := by
          rw [hs.2.2.2.1]
        simpa [hzre, hzim] using And.intro hjclose hkclose
      · have hkneg : k < 0 := lt_of_not_ge hk
        have hkclose : |k - (-im)| ≤ δ :=
          abs_sub_neg_center_le_of_sq_bounds k im δ
            (I.box.lo : ℝ) (I.box.hi : ℝ)
            hδ hkneg hbR.2.1 hbR.2.2.1 hklo hkhi hbR.2.2.2.1
        refine ⟨⟨0, by omega⟩, ?_⟩
        change |j - centerCoordR z0.re| ≤ δ ∧
          |k - centerCoordR z0.im| ≤ δ
        have hzre : centerCoordR z0.re = -re := by
          rw [hs.1, centerCoordR_neg11]
        have hzim : centerCoordR z0.im = -im := by
          rw [hs.2.1, centerCoordR_neg11]
        simpa [hzre, hzim] using And.intro hjclose hkclose

/-- The interval-to-center layer is completely discharged by the rational
40-interval table and the exact sign layout of the 160 centers. -/
theorem squaredKIntervalPhaseCenterCertificate11 :
    SquaredKIntervalPhaseCenterCertificate11 where
  cover j k q hkI hjk := by
    obtain ⟨o, ho⟩ :=
      squaredK_interval_phase_center_block11 j k q hkI hjk
    exact ⟨phaseCenterBlockIndex11 q o, ho⟩

private theorem phase_last_abs_le_one
    (x : PhaseCoords11) (hx : x.IsPhaseSolution) : |x.k| ≤ 1 := by
  have hjk : x.j ^ 2 + x.k ^ 2 = 1 := hx.1.2.2.2.2
  have hk2 : x.k ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.j]
  exact (sq_le_one_iff_abs_le_one x.k).mp hk2

/-- `H252 = P150 * R102`, and the `R102` factor is strictly positive on all
real circle coordinates.  Hence elimination to `H252` already gives a
`P150` root for every phase solution. -/
theorem H252PhaseEliminationCertificate11.phase_k_is_p150_root
    (E : H252PhaseEliminationCertificate11)
    (x : PhaseCoords11) (hx : x.IsPhaseSolution) :
    p150KR11.IsRoot x.k := by
  have hH := E.phase_k_isRoot x hx
  rw [Polynomial.IsRoot] at hH ⊢
  have hprod : p150KR11.eval x.k * r102KR11.eval x.k = 0 := by
    simpa [h252KR11, h252KQ11, p150KR11, r102KR11] using hH
  rcases mul_eq_zero.mp hprod with hp | hr
  · exact hp
  · exact False.elim <| (ne_of_gt
      (r102KR11_pos_of_abs_le_one x.k (phase_last_abs_le_one x hx))) hr

/-- Assemble the exact single-coordinate root cover consumed by the finite
scanner.  All downstream dilation and 80-box arguments are already proved in
`P150PhaseExhaustionBridge11`. -/
theorem p150KRootCoverCertificate11_of_exact_layers
    (E : H252PhaseEliminationCertificate11)
    (R : P150SquaredRootIsolationCertificate11)
    (G : SquaredKIntervalPhaseCenterCertificate11) :
    P150KRootCoverCertificate11 where
  cover_last x hx := by
    have hp := E.phase_k_is_p150_root x hx
    obtain ⟨q, hkI⟩ := R.cover x.k (phase_last_abs_le_one x hx) hp
    exact G.cover x.j x.k q hkI hx.1.2.2.2.2

/-- The reusable coordinate-cover assembly takes the elimination and
root-isolation certificates as its hypotheses. -/
structure P150CoordinateCertificateInputs11 where
  elimination : H252PhaseEliminationCertificate11
  rootIsolation : P150SquaredRootIsolationCertificate11

theorem P150CoordinateCertificateInputs11.toKRootCoverCertificate
    (C : P150CoordinateCertificateInputs11) :
    P150KRootCoverCertificate11 :=
  p150KRootCoverCertificate11_of_exact_layers C.elimination C.rootIsolation
    squaredKIntervalPhaseCenterCertificate11

end

end Biunimodular.F11
