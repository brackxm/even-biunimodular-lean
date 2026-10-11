/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.FinitePhaseNativeScan
public import Biunimodular.F11.TailCramerPerturbation
public meta import Biunimodular.F11.ProofTactics
public meta import Biunimodular.F11.FinitePhaseNativeScan
public meta import Biunimodular.F11.TailCramerPerturbation

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Exact scaling bridge between the integer scanner and the real Cramer system

The scanner stores phase centers as integers at scale `S = 10^14`.
Its matrix entries therefore have scale `S`, its right-hand side has scale
`S^2`, the determinant has scale `S^4`, and every Cramer numerator has scale
`S^5`.  These identities connect the `native_decide` determinant/lookup
certificates to the real perturbation estimates without any floating-point
argument.
-/

/-- Every stored phase center lies in the closed square of radius the fixed
point scale. -/
theorem phaseCenters_abs_le_scale (i : Fin 160) :
    iabs (phaseCenters160[i.1]!).re ≤ phaseCenterScale ∧
      iabs (phaseCenters160[i.1]!).im ≤ phaseCenterScale := by
  native_decide +revert

/-- A `10⁻¹⁰` version of `nearScaled`, used to certify the returned scan
centers with ample room inside the wider search window. -/
def nearScaledTight (n d center : Int) : Bool :=
  decide ((10000000000 : Int) * iabs (n - center*d) < phaseCenterScale*d)

noncomputable def centerCoordR (x : Int) : ℝ :=
  (x : ℝ) / (phaseCenterScale : ℝ)

/-- Integer tail system written directly in the six center coordinates. -/
def centerTailSystemRaw (A B C D E F : Int) : CenterTailSystem :=
  let S := phaseCenterScale
  let m00 := E-C; let m01 := F-D; let m02 := -E; let m03 := -F
  let m10 := A; let m11 := B; let m12 := C+E; let m13 := D+F
  let m20 := S+E; let m21 := F; let m22 := A+C; let m23 := B+D
  let m30 := A+C; let m31 := B+D; let m32 := S+A; let m33 := B
  let r0 := -((A-C)*S + A*C+B*D+C*E+D*F-A*E-B*F)
  let r1 := -(E*S + A*C+B*D + S*S/2)
  let r2 := -(A*E+B*F + S*S/2)
  let r3 := -(C*E+D*F + S*S/2)
  let Δ := det4i m00 m01 m02 m03 m10 m11 m12 m13
    m20 m21 m22 m23 m30 m31 m32 m33
  let ng := det4i r0 m01 m02 m03 r1 m11 m12 m13
    r2 m21 m22 m23 r3 m31 m32 m33
  let nh := det4i m00 r0 m02 m03 m10 r1 m12 m13
    m20 r2 m22 m23 m30 r3 m32 m33
  let nj := det4i m00 m01 r0 m03 m10 m11 r1 m13
    m20 m21 r2 m23 m30 m31 r3 m33
  let nk := det4i m00 m01 m02 r0 m10 m11 m12 r1
    m20 m21 m22 r2 m30 m31 m32 r3
  ⟨Δ,ng,nh,nj,nk⟩

/-- The optimized scan system is literally the raw scaled system. -/
theorem centerTailSystem_eq_raw (ia ic ie : Nat) :
    centerTailSystem ia ic ie =
      centerTailSystemRaw
        (phaseCenters160[ia]!).re (phaseCenters160[ia]!).im
        (phaseCenters160[ic]!).re (phaseCenters160[ic]!).im
        (phaseCenters160[ie]!).re (phaseCenters160[ie]!).im := by
  rfl

lemma phaseCenterScale_real_ne : (phaseCenterScale : ℝ) ≠ 0 := by
  norm_num [phaseCenterScale]

lemma det3i_cast
    (a b c d e f g h i : Int) :
    ((det3i a b c d e f g h i : Int) : ℝ) =
      det3r a b c d e f g h i := by
  simp [det3i, det3r]

lemma det4i_cast
    (a00 a01 a02 a03 a10 a11 a12 a13
     a20 a21 a22 a23 a30 a31 a32 a33 : Int) :
    ((det4i a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33 : Int) : ℝ) =
      det4r a00 a01 a02 a03 a10 a11 a12 a13
      a20 a21 a22 a23 a30 a31 a32 a33 := by
  simp [det4i, det4r, det3i, det3r]

/-- Determinant homogeneity for a common scalar on all matrix entries. -/
lemma det4r_scale (S : ℝ)
    (a00 a01 a02 a03 a10 a11 a12 a13
     a20 a21 a22 a23 a30 a31 a32 a33 : ℝ) :
    det4r (S*a00) (S*a01) (S*a02) (S*a03)
      (S*a10) (S*a11) (S*a12) (S*a13)
      (S*a20) (S*a21) (S*a22) (S*a23)
      (S*a30) (S*a31) (S*a32) (S*a33) =
      S^4 * det4r a00 a01 a02 a03 a10 a11 a12 a13
        a20 a21 a22 a23 a30 a31 a32 a33 := by
  simp [det4r, det3r]
  ring

/-- Each Cramer numerator has one RHS column at scale `S^2` and three
ordinary matrix columns at scale `S`, hence total scale `S^5`. -/
lemma cramer0r_scale_rhs (S : ℝ)
    (y0 y1 y2 y3 a01 a02 a03 a11 a12 a13
      a21 a22 a23 a31 a32 a33 : ℝ) :
    cramer0r (S^2*y0) (S^2*y1) (S^2*y2) (S^2*y3)
      (S*a01) (S*a02) (S*a03) (S*a11) (S*a12) (S*a13)
      (S*a21) (S*a22) (S*a23) (S*a31) (S*a32) (S*a33) =
      S^5 * cramer0r y0 y1 y2 y3 a01 a02 a03 a11 a12 a13
        a21 a22 a23 a31 a32 a33 := by
  simp [cramer0r, det3r]
  ring

lemma cramer1r_scale_rhs (S : ℝ)
    (y0 y1 y2 y3 a00 a02 a03 a10 a12 a13
      a20 a22 a23 a30 a32 a33 : ℝ) :
    cramer1r (S^2*y0) (S^2*y1) (S^2*y2) (S^2*y3)
      (S*a00) (S*a02) (S*a03) (S*a10) (S*a12) (S*a13)
      (S*a20) (S*a22) (S*a23) (S*a30) (S*a32) (S*a33) =
      S^5 * cramer1r y0 y1 y2 y3 a00 a02 a03 a10 a12 a13
        a20 a22 a23 a30 a32 a33 := by
  simp [cramer1r, det3r]
  ring

lemma cramer2r_scale_rhs (S : ℝ)
    (y0 y1 y2 y3 a00 a01 a03 a10 a11 a13
      a20 a21 a23 a30 a31 a33 : ℝ) :
    cramer2r (S^2*y0) (S^2*y1) (S^2*y2) (S^2*y3)
      (S*a00) (S*a01) (S*a03) (S*a10) (S*a11) (S*a13)
      (S*a20) (S*a21) (S*a23) (S*a30) (S*a31) (S*a33) =
      S^5 * cramer2r y0 y1 y2 y3 a00 a01 a03 a10 a11 a13
        a20 a21 a23 a30 a31 a33 := by
  simp [cramer2r, det3r]
  ring

lemma cramer3r_scale_rhs (S : ℝ)
    (y0 y1 y2 y3 a00 a01 a02 a10 a11 a12
      a20 a21 a22 a30 a31 a32 : ℝ) :
    cramer3r (S^2*y0) (S^2*y1) (S^2*y2) (S^2*y3)
      (S*a00) (S*a01) (S*a02) (S*a10) (S*a11) (S*a12)
      (S*a20) (S*a21) (S*a22) (S*a30) (S*a31) (S*a32) =
      S^5 * cramer3r y0 y1 y2 y3 a00 a01 a02 a10 a11 a12
        a20 a21 a22 a30 a31 a32 := by
  simp [cramer3r, det3r]
  ring

/-- Raw scanner determinant = `S^4` times the physical real determinant. -/
theorem centerTailSystemRaw_det_scale (A B C D E F : Int) :
    let a := centerCoordR A; let b := centerCoordR B
    let c := centerCoordR C; let d := centerCoordR D
    let e := centerCoordR E; let f := centerCoordR F
    (((centerTailSystemRaw A B C D E F).det : Int) : ℝ) =
      (phaseCenterScale : ℝ)^4 * tailDetR a b c d e f := by
  dsimp [centerTailSystemRaw, centerCoordR, tailDetR]
  rw [det4i_cast]
  field_simp [phaseCenterScale_real_ne]
  simp [tailMatrix, det4r, det3r, phaseCenterScale]
  ring

/-- The four raw scanner Cramer numerators = `S^5` times their physical
real counterparts. -/
theorem centerTailSystemRaw_cramer_scale (A B C D E F : Int) :
    let a := centerCoordR A; let b := centerCoordR B
    let c := centerCoordR C; let d := centerCoordR D
    let e := centerCoordR E; let f := centerCoordR F
    let s := centerTailSystemRaw A B C D E F
    (((s.ng : Int) : ℝ) = (phaseCenterScale : ℝ)^5 * tailCramerG a b c d e f) ∧
    (((s.nh : Int) : ℝ) = (phaseCenterScale : ℝ)^5 * tailCramerH a b c d e f) ∧
    (((s.nj : Int) : ℝ) = (phaseCenterScale : ℝ)^5 * tailCramerJ a b c d e f) ∧
    (((s.nk : Int) : ℝ) = (phaseCenterScale : ℝ)^5 * tailCramerK a b c d e f) := by
  dsimp [centerTailSystemRaw, centerCoordR, tailCramerG, tailCramerH,
    tailCramerJ, tailCramerK]
  field_simp [phaseCenterScale_real_ne]
  simp [det4i, det3i, cramer0r, cramer1r, cramer2r, cramer3r,
    det3r, tailMatrix, tailRhs, phaseCenterScale]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

end Biunimodular.F11

namespace Biunimodular.F11

lemma iabs_cast_real (x : Int) : ((iabs x : Int) : ℝ) = |(x : ℝ)| := by
  by_cases hx : x < 0
  · have hxR : (x : ℝ) < 0 := by exact_mod_cast hx
    simp only [iabs, ite_eq_left hx, Int.cast_neg]
    exact (abs_of_neg hxR).symm
  · have hx' : (0 : Int) ≤ x := le_of_not_gt hx
    have hxR : (0 : ℝ) ≤ x := by exact_mod_cast hx'
    simp only [iabs, ite_eq_right hx]
    exact (abs_of_nonneg hxR).symm

/-- The exact integer determinant margin used by the scan implies the physical
real determinant margin `10^-6`. -/
theorem center_real_det_margin
    (ia ic ie : Fin 160)
    (hreg : exceptionalTriple ia.1 ic.1 ie.1 = false) :
    (1/1000000 : ℝ) ≤
      |tailDetR
        (centerCoordR (phaseCenters160[ia.1]!).re)
        (centerCoordR (phaseCenters160[ia.1]!).im)
        (centerCoordR (phaseCenters160[ic.1]!).re)
        (centerCoordR (phaseCenters160[ic.1]!).im)
        (centerCoordR (phaseCenters160[ie.1]!).re)
        (centerCoordR (phaseCenters160[ie.1]!).im)| := by
  have hi := center_det_margin_all ia ic ie hreg
  have heq := centerTailSystem_eq_raw ia.1 ic.1 ie.1
  let A := (phaseCenters160[ia.1]!).re
  let B := (phaseCenters160[ia.1]!).im
  let C := (phaseCenters160[ic.1]!).re
  let D := (phaseCenters160[ic.1]!).im
  let E := (phaseCenters160[ie.1]!).re
  let F := (phaseCenters160[ie.1]!).im
  have hs := centerTailSystemRaw_det_scale A B C D E F
  have hicast : (centerDetThreshold : ℝ) ≤
      |(((centerTailSystem ia.1 ic.1 ie.1).det : Int) : ℝ)| := by
    rw [← iabs_cast_real]
    exact_mod_cast hi
  rw [heq] at hicast
  dsimp [A,B,C,D,E,F] at hs ⊢
  rw [hs] at hicast
  simp [abs_mul, phaseCenterScale, centerDetThreshold] at hicast
  norm_num [phaseCenterScale, centerDetThreshold] at hicast ⊢
  nlinarith

/-- Physical meaning of the scanner's `nearScaled` test.  A strict `10^-4`
physical error implies the exact cross-multiplied integer predicate. -/
theorem nearScaled_of_physical_ratio_close
    (n d center : Int)
    (hd : 0 < d)
    (hclose :
      |((n : ℝ) / (d : ℝ)) / (phaseCenterScale : ℝ) -
        (center : ℝ) / (phaseCenterScale : ℝ)| < (1 / 10000 : ℝ)) :
    nearScaled n d center = true := by
  unfold nearScaled
  apply decide_eq_true
  rw [show n - center*d = n - center*d by rfl]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hSR : (0 : ℝ) < (phaseCenterScale : ℝ) := by
    norm_num [phaseCenterScale]
  have hratio :
      ((n : ℝ) / (d : ℝ)) / (phaseCenterScale : ℝ) -
          (center : ℝ) / (phaseCenterScale : ℝ) =
        ((n - center*d : Int) : ℝ) /
          ((d : ℝ) * (phaseCenterScale : ℝ)) := by
    push_cast
    field_simp [ne_of_gt hdR, ne_of_gt hSR]
  rw [hratio, abs_div, abs_of_pos (mul_pos hdR hSR)] at hclose
  have hreal : (10000 : ℝ) * |((n - center*d : Int) : ℝ)| <
      (phaseCenterScale : ℝ) * (d : ℝ) := by
    have hcross := (div_lt_iff₀ (mul_pos hdR hSR)).mp hclose
    nlinarith
  rw [← iabs_cast_real] at hreal
  exact_mod_cast hreal

end Biunimodular.F11

namespace Biunimodular.F11

lemma normalized_int_ratio_eq (n det : Int) (_hdet : det ≠ 0) :
    (((if det < 0 then -n else n : Int) : ℝ) / ((iabs det : Int) : ℝ)) =
      (n : ℝ) / (det : ℝ) := by
  by_cases hneg : det < 0
  · simp [hneg, iabs]
  · simp [hneg, iabs]

/-- Exact physical interpretation of all four sign-normalized integer Cramer
ratios used by `phaseNear`. -/
theorem centerTailSystemRaw_normalized_ratios
    (A B C D E F : Int)
    (hdet : (centerTailSystemRaw A B C D E F).det ≠ 0) :
    let a := centerCoordR A; let b := centerCoordR B
    let c := centerCoordR C; let d := centerCoordR D
    let e := centerCoordR E; let f := centerCoordR F
    let s := centerTailSystemRaw A B C D E F
    let Δ := s.det
    let den := iabs Δ
    let ng := if Δ < 0 then -s.ng else s.ng
    let nh := if Δ < 0 then -s.nh else s.nh
    let nj := if Δ < 0 then -s.nj else s.nj
    let nk := if Δ < 0 then -s.nk else s.nk
    (((ng : ℝ)/(den : ℝ))/(phaseCenterScale : ℝ) = tailCramerG a b c d e f / tailDetR a b c d e f) ∧
    (((nh : ℝ)/(den : ℝ))/(phaseCenterScale : ℝ) = tailCramerH a b c d e f / tailDetR a b c d e f) ∧
    (((nj : ℝ)/(den : ℝ))/(phaseCenterScale : ℝ) = tailCramerJ a b c d e f / tailDetR a b c d e f) ∧
    (((nk : ℝ)/(den : ℝ))/(phaseCenterScale : ℝ) = tailCramerK a b c d e f / tailDetR a b c d e f) := by
  dsimp
  have hdscale := centerTailSystemRaw_det_scale A B C D E F
  have hnscale := centerTailSystemRaw_cramer_scale A B C D E F
  dsimp at hdscale
  rcases hnscale with ⟨hg,hh,hj,hk⟩
  have hΔR : tailDetR (centerCoordR A) (centerCoordR B) (centerCoordR C)
      (centerCoordR D) (centerCoordR E) (centerCoordR F) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdscale
    exact hdet (by exact_mod_cast hdscale)
  have hnormg := normalized_int_ratio_eq (centerTailSystemRaw A B C D E F).ng
    (centerTailSystemRaw A B C D E F).det hdet
  have hnormh := normalized_int_ratio_eq (centerTailSystemRaw A B C D E F).nh
    (centerTailSystemRaw A B C D E F).det hdet
  have hnormj := normalized_int_ratio_eq (centerTailSystemRaw A B C D E F).nj
    (centerTailSystemRaw A B C D E F).det hdet
  have hnormk := normalized_int_ratio_eq (centerTailSystemRaw A B C D E F).nk
    (centerTailSystemRaw A B C D E F).det hdet
  rw [hg, hdscale] at hnormg
  rw [hh, hdscale] at hnormh
  rw [hj, hdscale] at hnormj
  rw [hk, hdscale] at hnormk
  have hS : (phaseCenterScale : ℝ) ≠ 0 := phaseCenterScale_real_ne
  constructor
  · rw [hnormg]
    field_simp [hS,hΔR]
  · constructor
    · rw [hnormh]
      field_simp [hS,hΔR]
    · constructor
      · rw [hnormj]
        field_simp [hS,hΔR]
      · rw [hnormk]
        field_simp [hS,hΔR]

end Biunimodular.F11

namespace Biunimodular.F11

/-- Reverse direction of `nearScaled_of_physical_ratio_close`. -/
theorem physical_ratio_close_of_nearScaled
    (n d center : Int) (hd : 0 < d)
    (hnear : nearScaled n d center = true) :
    |((n : ℝ) / (d : ℝ)) / (phaseCenterScale : ℝ) -
      (center : ℝ) / (phaseCenterScale : ℝ)| < (1/10000 : ℝ) := by
  unfold nearScaled at hnear
  have hi := of_decide_eq_true hnear
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hiR : (10000 : ℝ) * |((n - center*d : Int) : ℝ)| <
      (phaseCenterScale : ℝ) * (d : ℝ) := by
    rw [← iabs_cast_real]
    exact_mod_cast hi
  have hSR : (0 : ℝ) < (phaseCenterScale : ℝ) := by
    norm_num [phaseCenterScale]
  have hratio :
      ((n : ℝ) / (d : ℝ)) / (phaseCenterScale : ℝ) -
          (center : ℝ) / (phaseCenterScale : ℝ) =
        ((n - center*d : Int) : ℝ) /
          ((d : ℝ) * (phaseCenterScale : ℝ)) := by
    push_cast
    field_simp [ne_of_gt hdR, ne_of_gt hSR]
  rw [hratio, abs_div, abs_of_pos (mul_pos hdR hSR)]
  apply (div_lt_iff₀ (mul_pos hdR hSR)).2
  nlinarith

/-- Reverse direction for the tighter `10^-10` predicate used on the 80
accepted scanner outputs. -/
theorem physical_ratio_close_of_nearScaledTight
    (n d center : Int) (hd : 0 < d)
    (hnear : nearScaledTight n d center = true) :
    |((n : ℝ) / (d : ℝ)) / (phaseCenterScale : ℝ) -
      (center : ℝ) / (phaseCenterScale : ℝ)| < (1/10000000000 : ℝ) := by
  unfold nearScaledTight at hnear
  have hi := of_decide_eq_true hnear
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hiR : (10000000000 : ℝ) * |((n - center*d : Int) : ℝ)| <
      (phaseCenterScale : ℝ) * (d : ℝ) := by
    rw [← iabs_cast_real]
    exact_mod_cast hi
  have hSR : (0 : ℝ) < (phaseCenterScale : ℝ) := by
    norm_num [phaseCenterScale]
  have hratio :
      ((n : ℝ) / (d : ℝ)) / (phaseCenterScale : ℝ) -
          (center : ℝ) / (phaseCenterScale : ℝ) =
        ((n - center*d : Int) : ℝ) /
          ((d : ℝ) * (phaseCenterScale : ℝ)) := by
    push_cast
    field_simp [ne_of_gt hdR, ne_of_gt hSR]
  rw [hratio, abs_div, abs_of_pos (mul_pos hdR hSR)]
  apply (div_lt_iff₀ (mul_pos hdR hSR)).2
  nlinarith

end Biunimodular.F11

namespace Biunimodular.F11

/-- Specialized ratio bridge for one scanner center triple. -/
theorem centerTailSystem_normalized_ratios
    (ia ic ie : Fin 160)
    (hdet : (centerTailSystem ia.1 ic.1 ie.1).det ≠ 0) :
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
    (((ng : ℝ)/(den : ℝ))/(phaseCenterScale : ℝ) = tailCramerG A B C D E F / tailDetR A B C D E F) ∧
    (((nh : ℝ)/(den : ℝ))/(phaseCenterScale : ℝ) = tailCramerH A B C D E F / tailDetR A B C D E F) ∧
    (((nj : ℝ)/(den : ℝ))/(phaseCenterScale : ℝ) = tailCramerJ A B C D E F / tailDetR A B C D E F) ∧
    (((nk : ℝ)/(den : ℝ))/(phaseCenterScale : ℝ) = tailCramerK A B C D E F / tailDetR A B C D E F) := by
  rw [centerTailSystem_eq_raw ia.1 ic.1 ie.1] at hdet ⊢
  exact centerTailSystemRaw_normalized_ratios _ _ _ _ _ _ hdet

/-- All stored first-three-phase center coordinates satisfy the unit bound
needed by the perturbation lemmas. -/
theorem center_unit6 (ia ic ie : Fin 160) :
    unit6
      (centerCoordR (phaseCenters160[ia.1]!).re)
      (centerCoordR (phaseCenters160[ia.1]!).im)
      (centerCoordR (phaseCenters160[ic.1]!).re)
      (centerCoordR (phaseCenters160[ic.1]!).im)
      (centerCoordR (phaseCenters160[ie.1]!).re)
      (centerCoordR (phaseCenters160[ie.1]!).im) := by
  have ha := phaseCenters_abs_le_scale ia
  have hc := phaseCenters_abs_le_scale ic
  have he := phaseCenters_abs_le_scale ie
  rcases ha with ⟨ha0,ha1⟩
  rcases hc with ⟨hc0,hc1⟩
  rcases he with ⟨he0,he1⟩
  have hSpos : (0 : ℝ) < (phaseCenterScale : ℝ) := by
    norm_num [phaseCenterScale]
  have hbound (x : Int) (hx : iabs x ≤ phaseCenterScale) :
      |centerCoordR x| ≤ 1 := by
    have hxR : |(x : ℝ)| ≤ (phaseCenterScale : ℝ) := by
      rw [← iabs_cast_real]
      exact_mod_cast hx
    rw [centerCoordR, abs_div, abs_of_pos hSpos]
    exact (div_le_iff₀ hSpos).2 (by simpa using hxR)
  exact ⟨hbound _ ha0, hbound _ ha1, hbound _ hc0, hbound _ hc1,
    hbound _ he0, hbound _ he1⟩

end Biunimodular.F11
