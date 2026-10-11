/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceFourierQuotient
import Biunimodular.F11.FixedSliceQuotientInvariant
import Biunimodular.F11.FixedSliceQuotientPolynomial
import Biunimodular.F11.FixedSliceRootIntervalCertificate
import Biunimodular.F11.FixedSliceGeometryAssembly

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial
open ZMod
open scoped ComplexConjugate LinearAlgebra.Projectivization

noncomputable section

/-!
# The concrete F11 quotient map and real locus

This file defines the geometric certificate used by the
fixed-slice cardinality assembly:

* the quotient-to-root map is the actual projective invariant `u=q^2`;
* the real locus is the fixed locus of the Fourier-conjugate real structure.

Consequently the geometric certificate cannot choose an arbitrary
equivalence with a sixteen-element type or an arbitrary sixteen-point
predicate.  It only asserts that the concrete `u` map is a bijection onto the
roots of the certified degree-sixteen polynomial.  The real/split theorem is
then derived from conjugation, Fourier freeness, and elementary inequalities.
-/

/-- The homogeneous quotient invariant descended to projective five-space. -/
def even11ProjectiveU : Even11ProjectiveSpace → ℂ :=
  Projectivization.lift
    (fun h : {h : Even6 ℂ // h ≠ 0} ↦
      fixedSliceUValue even11FourierNormalized h.1)
    (by
      intro a b c hab
      have hc : c ≠ 0 := by
        intro hc
        apply a.2
        rw [hab, hc, zero_smul]
      rw [hab]
      exact fixedSliceUValue_smul even11FourierNormalized hc b.1)

@[simp] theorem even11ProjectiveU_mk
    (h : Even6 ℂ) (hnz : h ≠ 0) :
    even11ProjectiveU (Projectivization.mk ℂ h hnz) =
      fixedSliceUValue even11FourierNormalized h := by
  rfl

/-- The projective invariant is unchanged by the normalized Fourier
involution. -/
@[simp] theorem even11ProjectiveU_fourier
    (p : Even11ProjectiveSpace) :
    even11ProjectiveU (even11ProjectiveFourier p) = even11ProjectiveU p := by
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveFourier_mk, even11ProjectiveU_mk,
        even11ProjectiveU_mk]
      exact fixedSliceUValue_fourier even11FourierNormalized_sq h

/-- The concrete invariant on the projective fixed slice. -/
def even11FixedSliceU (p : Even11FixedSlicePoint) : ℂ :=
  even11ProjectiveU p.1

@[simp] theorem even11FixedSliceU_fourier (p : Even11FixedSlicePoint) :
    even11FixedSliceU (even11FixedSliceFourier p) = even11FixedSliceU p := by
  exact even11ProjectiveU_fourier p.1

@[simp] theorem even11FixedSliceU_vadd
    (b : Bool) (p : Even11FixedSlicePoint) :
    even11FixedSliceU (b +ᵥ p) = even11FixedSliceU p := by
  cases b <;> simp

/-- The actual `u=q^2` map on the free Fourier quotient. -/
def even11FixedSliceQuotientU : Even11FixedSliceFourierQuotient → ℂ :=
  Quotient.lift even11FixedSliceU (by
    intro a b hab
    change AddAction.orbitRel Bool Even11FixedSlicePoint a b at hab
    rw [AddAction.orbitRel_apply] at hab
    rcases hab with ⟨g, hg⟩
    rw [← hg]
    exact even11FixedSliceU_vadd g b)

@[simp] theorem even11FixedSliceQuotientU_mk
    (p : Even11FixedSlicePoint) :
    even11FixedSliceQuotientU (Quotient.mk'' p) = even11FixedSliceU p := by
  rfl

/-- Coordinatewise complex conjugation on the six-coordinate even model. -/
def even11Conj (h : Even6 ℂ) : Even6 ℂ :=
  fun i ↦ conj (h i)

theorem even11_conj_stdAddChar (x : ZMod 11) :
    conj (stdAddChar x) = stdAddChar (-x) := by
  simp only [stdAddChar_apply, ← Circle.coe_inv_eq_conj]
  rw [AddChar.map_neg_eq_inv]

/-- Complex conjugation reverses frequency in the full DFT. -/
theorem even11_conj_dft (f : ZMod 11 → ℂ) (k : ZMod 11) :
    conj (ZMod.dft f k) =
      ZMod.dft (fun j ↦ conj (f j)) (-k) := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [map_sum, smul_eq_mul, map_mul, even11_conj_stdAddChar]
  congr 1
  funext j
  congr 1
  ring_nf

/-- On the even subspace, the unnormalised Fourier matrix is real. -/
theorem even11Fourier_conj (h : Even6 ℂ) :
    even11Conj (even11Fourier h) = even11Fourier (even11Conj h) := by
  funext i
  change conj (ZMod.dft (even11Lift h) (i.1 : ZMod 11)) =
    ZMod.dft (even11Lift (even11Conj h)) (i.1 : ZMod 11)
  rw [even11_conj_dft]
  have hlift : (fun j ↦ conj (even11Lift h j)) =
      even11Lift (even11Conj h) := by
    funext j
    rfl
  rw [hlift]
  exact (ZMod.dft_even_iff.mpr (even11Lift_even (even11Conj h))) i.1

/-- The normalized even Fourier matrix is real as well. -/
theorem even11FourierNormalized_conj (h : Even6 ℂ) :
    even11Conj (even11FourierNormalized h) =
      even11FourierNormalized (even11Conj h) := by
  funext i
  simp only [even11Conj, even11FourierNormalized, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show conj ((Real.sqrt 11 : ℂ)⁻¹) = (Real.sqrt 11 : ℂ)⁻¹ by simp]
  exact congrArg (fun z : ℂ ↦ (Real.sqrt 11 : ℂ)⁻¹ * z)
    (congrFun (even11Fourier_conj h) i)

theorem even11Conj_ne_zero {h : Even6 ℂ} (hnz : h ≠ 0) :
    even11Conj h ≠ 0 := by
  intro hzero
  apply hnz
  funext i
  have hi := congrFun hzero i
  change conj (h i) = 0 at hi
  exact (map_eq_zero (starRingEnd ℂ)).mp hi

@[simp] theorem even11Conj_conj (h : Even6 ℂ) :
    even11Conj (even11Conj h) = h := by
  funext i
  simp [even11Conj]

/-- The real Fourier matrix makes the complex fixed-slice equations stable
under coordinatewise conjugation. -/
theorem even11_fixedSliceEq_conj {h : Even6 ℂ}
    (hh : FixedSliceEq even11FourierNormalized h) :
    FixedSliceEq even11FourierNormalized (even11Conj h) := by
  intro j
  have hj := congrArg conj (hh j)
  simp only [fourierCoordProduct, map_mul] at hj ⊢
  rw [← congrFun (even11FourierNormalized_conj h) j,
    ← congrFun (even11FourierNormalized_conj h) 0]
  exact hj

/-- Coordinatewise conjugation descended to complex projective five-space. -/
def even11ProjectiveConj :
    Even11ProjectiveSpace → Even11ProjectiveSpace :=
  Projectivization.lift
    (fun h : {h : Even6 ℂ // h ≠ 0} ↦
      Projectivization.mk ℂ (even11Conj h.1) (even11Conj_ne_zero h.2))
    (by
      intro a b c hab
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨conj c, ?_⟩
      rw [hab]
      funext i
      simp [even11Conj])

@[simp] theorem even11ProjectiveConj_mk
    (h : Even6 ℂ) (hnz : h ≠ 0) :
    even11ProjectiveConj (Projectivization.mk ℂ h hnz) =
      Projectivization.mk ℂ (even11Conj h) (even11Conj_ne_zero hnz) := by
  rfl

@[simp] theorem even11ProjectiveConj_sq (p : Even11ProjectiveSpace) :
    even11ProjectiveConj (even11ProjectiveConj p) = p := by
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveConj_mk, even11ProjectiveConj_mk]
      simp only [even11Conj_conj]

/-- Projective conjugation preserves the concrete fixed slice. -/
theorem even11ProjectiveFixedSlice_conj
    {p : Even11ProjectiveSpace} (hp : even11ProjectiveFixedSlice p) :
    even11ProjectiveFixedSlice (even11ProjectiveConj p) := by
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveConj_mk,
        even11ProjectiveFixedSlice_mk] at ⊢
      exact even11_fixedSliceEq_conj hp

/-- Projective conjugation commutes with the real Fourier involution. -/
@[simp] theorem even11ProjectiveConj_fourier
    (p : Even11ProjectiveSpace) :
    even11ProjectiveConj (even11ProjectiveFourier p) =
      even11ProjectiveFourier (even11ProjectiveConj p) := by
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveFourier_mk, even11ProjectiveConj_mk,
        even11ProjectiveConj_mk, even11ProjectiveFourier_mk]
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨1, ?_⟩
      simp [even11FourierNormalized_conj]

/-- Coordinatewise conjugation restricted to the concrete fixed slice. -/
def even11FixedSliceConj :
    Even11FixedSlicePoint ≃ Even11FixedSlicePoint where
  toFun p := ⟨even11ProjectiveConj p.1,
    even11ProjectiveFixedSlice_conj p.2⟩
  invFun p := ⟨even11ProjectiveConj p.1,
    even11ProjectiveFixedSlice_conj p.2⟩
  left_inv p := by
    apply Subtype.ext
    exact even11ProjectiveConj_sq p.1
  right_inv p := by
    apply Subtype.ext
    exact even11ProjectiveConj_sq p.1

@[simp] theorem even11FixedSliceConj_apply_coe
    (p : Even11FixedSlicePoint) :
    (even11FixedSliceConj p).1 = even11ProjectiveConj p.1 := rfl

@[simp] theorem even11FixedSliceConj_sq (p : Even11FixedSlicePoint) :
    even11FixedSliceConj (even11FixedSliceConj p) = p := by
  exact even11FixedSliceConj.left_inv p

@[simp] theorem even11FixedSliceConj_fourier
    (p : Even11FixedSlicePoint) :
    even11FixedSliceConj (even11FixedSliceFourier p) =
      even11FixedSliceFourier (even11FixedSliceConj p) := by
  apply Subtype.ext
  exact even11ProjectiveConj_fourier p.1

/-- The numerator of `q` is conjugation-equivariant. -/
theorem even11_fixedSliceQNum_conj (h : Even6 ℂ) :
    fixedSliceQNum even11FourierNormalized (even11Conj h) =
      conj (fixedSliceQNum even11FourierNormalized h) := by
  simp only [fixedSliceQNum, even11Conj, map_add, map_pow]
  rw [show even11FourierNormalized (even11Conj h) 0 =
    conj (even11FourierNormalized h 0) by
      exact congrFun (even11FourierNormalized_conj h).symm 0]

/-- The denominator of `q` is conjugation-equivariant. -/
theorem even11_fixedSliceQDen_conj (h : Even6 ℂ) :
    fixedSliceQDen even11FourierNormalized (even11Conj h) =
      conj (fixedSliceQDen even11FourierNormalized h) := by
  simp only [fixedSliceQDen, even11Conj, map_mul, map_ofNat]
  rw [show even11FourierNormalized (even11Conj h) 0 =
    conj (even11FourierNormalized h 0) by
      exact congrFun (even11FourierNormalized_conj h).symm 0]

/-- The homogeneous invariant `u=q²` is conjugation-equivariant. -/
theorem even11_fixedSliceUValue_conj (h : Even6 ℂ) :
    fixedSliceUValue even11FourierNormalized (even11Conj h) =
      conj (fixedSliceUValue even11FourierNormalized h) := by
  simp only [fixedSliceUValue, map_pow, map_div₀,
    even11_fixedSliceQNum_conj, even11_fixedSliceQDen_conj]

@[simp] theorem even11ProjectiveU_conj
    (p : Even11ProjectiveSpace) :
    even11ProjectiveU (even11ProjectiveConj p) =
      conj (even11ProjectiveU p) := by
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveConj_mk, even11ProjectiveU_mk,
        even11ProjectiveU_mk, even11_fixedSliceUValue_conj]

/-- The scalar two-coordinate expression for `q`. -/
def fixedSliceQPair (z w : ℂ) : ℂ :=
  (z ^ 2 + w ^ 2) / (2 * z * w)

theorem fixedSliceQPair_ratio {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    fixedSliceQPair z w = ((z / w) + (z / w)⁻¹) / 2 := by
  simp only [fixedSliceQPair]
  field_simp

private theorem conj_ratio_eq_inv_of_swap
    {z w a : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (hzconj : conj z = a * w) (hwconj : conj w = a * z) :
    conj (z / w) = (z / w)⁻¹ := by
  rw [map_div₀, hzconj, hwconj]
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at hzconj
    exact hz ((map_eq_zero (starRingEnd ℂ)).mp hzconj)
  field_simp [hz, hw, ha]

private theorem norm_ratio_eq_one_of_conj_swap
    {z w a : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (hzconj : conj z = a * w) (hwconj : conj w = a * z) :
    ‖z / w‖ = 1 := by
  let r := z / w
  have hr : r ≠ 0 := div_ne_zero hz hw
  have hconj : conj r = r⁻¹ :=
    conj_ratio_eq_inv_of_swap hz hw hzconj hwconj
  have hsq : Complex.normSq r = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self, hconj, inv_mul_cancel₀ hr]
    norm_num
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg r]

/-- If conjugation exchanges `z` and `w` up to a common scalar, then the
square of their quotient coordinate is real and belongs to `[0,1]`. -/
theorem fixedSliceQPair_sq_mem_unitInterval_of_conj_swap
    {z w a : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (hzconj : conj z = a * w) (hwconj : conj w = a * z) :
    (fixedSliceQPair z w ^ 2).im = 0 ∧
      0 ≤ (fixedSliceQPair z w ^ 2).re ∧
      (fixedSliceQPair z w ^ 2).re ≤ 1 := by
  let r := z / w
  let q := (r + r⁻¹) / 2
  have hconj : conj r = r⁻¹ :=
    conj_ratio_eq_inv_of_swap hz hw hzconj hwconj
  have hnorm : ‖r‖ = 1 :=
    norm_ratio_eq_one_of_conj_swap hz hw hzconj hwconj
  have hr : r ≠ 0 := div_ne_zero hz hw
  have hqconj : conj q = q := by
    simp only [q, map_div₀, map_add, map_inv₀, map_ofNat, hconj, inv_inv]
    rw [add_comm]
  have hqim : q.im = 0 := Complex.conj_eq_iff_im.mp hqconj
  have hnormInv : ‖r⁻¹‖ = 1 := by simp [hnorm]
  have hqnorm : ‖q‖ ≤ 1 := by
    calc
      ‖q‖ = ‖r + r⁻¹‖ / 2 := by simp [q]
      _ ≤ (‖r‖ + ‖r⁻¹‖) / 2 := by
        gcongr
        exact norm_add_le r r⁻¹
      _ = 1 := by rw [hnorm, hnormInv]; norm_num
  have hqnorm_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
  have hqnormsq : Complex.normSq q = ‖q‖ ^ 2 :=
    Complex.normSq_eq_norm_sq q
  have hqreSq : q.re ^ 2 = ‖q‖ ^ 2 := by
    rw [← hqnormsq]
    simp [Complex.normSq_apply, hqim, pow_two]
  have hqle : q.re ^ 2 ≤ 1 := by nlinarith
  have hqleMul : q.re * q.re ≤ 1 := by simpa [pow_two] using hqle
  rw [fixedSliceQPair_ratio hz hw]
  change (q ^ 2).im = 0 ∧ 0 ≤ (q ^ 2).re ∧ (q ^ 2).re ≤ 1
  simp only [pow_two, Complex.mul_im, Complex.mul_re, hqim,
    mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, mul_self_nonneg q.re, hqleMul⟩

private theorem conj_ratio_eq_self_of_common_scale
    {z w a : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (hzconj : conj z = a * z) (hwconj : conj w = a * w) :
    conj (z / w) = z / w := by
  rw [map_div₀, hzconj, hwconj]
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at hzconj
    exact hz ((map_eq_zero (starRingEnd ℂ)).mp hzconj)
  field_simp [hz, hw, ha]

/-- If conjugation fixes both `z` and `w` up to a common scalar, then the
square of their quotient coordinate is real and at least one. -/
theorem fixedSliceQPair_sq_ge_one_of_conj_common_scale
    {z w a : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (hzconj : conj z = a * z) (hwconj : conj w = a * w) :
    (fixedSliceQPair z w ^ 2).im = 0 ∧
      1 ≤ (fixedSliceQPair z w ^ 2).re := by
  let r := z / w
  let q := (r + r⁻¹) / 2
  let d := (r - r⁻¹) / 2
  have hr : r ≠ 0 := div_ne_zero hz hw
  have hconj : conj r = r :=
    conj_ratio_eq_self_of_common_scale hz hw hzconj hwconj
  have hqconj : conj q = q := by simp [q, hconj, map_ofNat]
  have hdconj : conj d = d := by simp [d, hconj, map_ofNat]
  have hqim : q.im = 0 := Complex.conj_eq_iff_im.mp hqconj
  have hdim : d.im = 0 := Complex.conj_eq_iff_im.mp hdconj
  have halg : q ^ 2 - 1 = d ^ 2 := by
    simp only [q, d]
    field_simp [hr]
    ring
  have hre := congrArg Complex.re halg
  simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re,
    hqim, hdim, mul_zero, sub_zero] at hre
  rw [fixedSliceQPair_ratio hz hw]
  change (q ^ 2).im = 0 ∧ 1 ≤ (q ^ 2).re
  simp only [pow_two, Complex.mul_im, Complex.mul_re, hqim,
    mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, by nlinarith [sq_nonneg d.re]⟩

/-- A homogeneous equation for the Fourier-conjugate real form used by the
fixed-slice construction.  On an affine representative it says that
`conj h` and `F h` span the same complex line. -/
def even11VectorIsFixedSliceReal (h : Even6 ℂ) : Prop :=
  ∀ i j,
    conj (h i) * even11FourierNormalized h j =
      conj (h j) * even11FourierNormalized h i

/-- The cross-product definition is exactly equality of the conjugate and
Fourier projective lines. -/
theorem even11VectorIsFixedSliceReal_iff_conj_fourier_line
    (h : Even6 ℂ) (hnz : h ≠ 0) :
    even11VectorIsFixedSliceReal h ↔
      Projectivization.mk ℂ (even11Conj h) (even11Conj_ne_zero hnz) =
        Projectivization.mk ℂ (even11FourierNormalized h)
          (by simpa using even11FourierNormalized_injective.ne hnz) := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · intro hr
    have hFourier : even11FourierNormalized h ≠ 0 :=
      by simpa using even11FourierNormalized_injective.ne hnz
    have hex : ∃ k, even11FourierNormalized h k ≠ 0 := by
      by_contra hnone
      simp only [not_exists, not_not] at hnone
      apply hFourier
      funext k
      exact hnone k
    rcases hex with ⟨k, hk⟩
    refine ⟨conj (h k) / even11FourierNormalized h k, ?_⟩
    funext i
    change (conj (h k) / even11FourierNormalized h k) *
      even11FourierNormalized h i = conj (h i)
    rw [div_mul_eq_mul_div, div_eq_iff hk]
    exact (hr i k).symm
  · rintro ⟨a, ha⟩ i j
    have hai := congrFun ha i
    have haj := congrFun ha j
    simp only [Pi.smul_apply, smul_eq_mul, even11Conj] at hai haj
    rw [← hai, ← haj]
    ring

/-- Fourier-conjugate reality is unchanged by nonzero complex rescaling. -/
theorem even11VectorIsFixedSliceReal_smul_iff
    {c : ℂ} (hc : c ≠ 0) (h : Even6 ℂ) :
    even11VectorIsFixedSliceReal (c • h) ↔
      even11VectorIsFixedSliceReal h := by
  have hconj : conj c ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hc
  constructor
  · intro hr i j
    have hij := hr i j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul,
      LinearMap.map_smul] at hij
    apply mul_left_cancel₀ (mul_ne_zero hconj hc)
    convert hij using 1 <;> ring
  · intro hr i j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul,
      LinearMap.map_smul]
    convert congrArg (fun z : ℂ ↦ conj c * c * z) (hr i j) using 1 <;> ring

/-- The genuine real locus of the complexified fixed-slice model.  Its real
structure is the anti-linear involution `h ↦ F (conj h)`, so a projective
point is real exactly when `[conj h] = [F h]`. -/
def even11ProjectiveIsReal : Even11ProjectiveSpace → Prop :=
  Projectivization.lift
    (fun h : {h : Even6 ℂ // h ≠ 0} ↦
      even11VectorIsFixedSliceReal h.1)
    (by
      intro a b c hab
      have hc : c ≠ 0 := by
        intro hc
        apply a.2
        rw [hab, hc, zero_smul]
      apply propext
      rw [hab]
      exact even11VectorIsFixedSliceReal_smul_iff hc b.1)

@[simp] theorem even11ProjectiveIsReal_mk
    (h : Even6 ℂ) (hnz : h ≠ 0) :
    even11ProjectiveIsReal (Projectivization.mk ℂ h hnz) ↔
      even11VectorIsFixedSliceReal h := by
  rfl

/-- On a representative, membership in the projective real locus is
literally equality of its conjugate and Fourier projective lines. -/
theorem even11ProjectiveIsReal_mk_iff_conj_fourier_line
    (h : Even6 ℂ) (hnz : h ≠ 0) :
    even11ProjectiveIsReal (Projectivization.mk ℂ h hnz) ↔
      Projectivization.mk ℂ (even11Conj h) (even11Conj_ne_zero hnz) =
        even11ProjectiveFourier (Projectivization.mk ℂ h hnz) := by
  have hmap := even11ProjectiveFourier_mk h hnz
  rw [hmap]
  exact even11VectorIsFixedSliceReal_iff_conj_fourier_line h hnz

/-- Intrinsic projective form of the Fourier-conjugate real-locus
condition. -/
theorem even11ProjectiveIsReal_iff_conj_eq_fourier
    (p : Even11ProjectiveSpace) :
    even11ProjectiveIsReal p ↔
      even11ProjectiveConj p = even11ProjectiveFourier p := by
  induction p using Projectivization.ind with
  | h h hnz =>
      exact even11ProjectiveIsReal_mk_iff_conj_fourier_line h hnz

/-- The concrete real-locus predicate on the projective fixed slice. -/
def even11FixedSliceIsReal (p : Even11FixedSlicePoint) : Prop :=
  even11ProjectiveIsReal p.1

/-- The real-locus predicate is equality of conjugation and Fourier on the
concrete fixed slice. -/
theorem even11FixedSliceIsReal_iff_conj_eq_fourier
    (p : Even11FixedSlicePoint) :
    even11FixedSliceIsReal p ↔
      even11FixedSliceConj p = even11FixedSliceFourier p := by
  constructor
  · intro hp
    apply Subtype.ext
    exact (even11ProjectiveIsReal_iff_conj_eq_fourier p.1).mp hp
  · intro hp
    apply (even11ProjectiveIsReal_iff_conj_eq_fourier p.1).mpr
    exact congrArg Subtype.val hp

/-- The other possible real form of a conjugation-stable Fourier orbit: the
projective line itself is defined over the standard real coordinates. -/
def even11FixedSliceIsOrdinaryReal (p : Even11FixedSlicePoint) : Prop :=
  even11FixedSliceConj p = p

@[simp] theorem even11FixedSliceConj_vadd
    (b : Bool) (p : Even11FixedSlicePoint) :
    even11FixedSliceConj (b +ᵥ p) = b +ᵥ even11FixedSliceConj p := by
  cases b <;> simp

/-- Complex conjugation descended through the Fourier orbit quotient. -/
def even11FixedSliceQuotientConj :
    Even11FixedSliceFourierQuotient → Even11FixedSliceFourierQuotient :=
  Quotient.lift
    (fun p : Even11FixedSlicePoint ↦ Quotient.mk'' (even11FixedSliceConj p))
    (by
      intro a b hab
      change AddAction.orbitRel Bool Even11FixedSlicePoint a b at hab
      rw [AddAction.orbitRel_apply] at hab
      rcases hab with ⟨g, hg⟩
      rw [← hg, even11FixedSliceConj_vadd]
      exact AddAction.orbitRel.Quotient.quotient_vadd_eq)

@[simp] theorem even11FixedSliceQuotientConj_mk
    (p : Even11FixedSlicePoint) :
    even11FixedSliceQuotientConj (Quotient.mk'' p) =
      Quotient.mk'' (even11FixedSliceConj p) := by
  rfl

@[simp] theorem even11FixedSliceQuotientConj_sq
    (y : Even11FixedSliceFourierQuotient) :
    even11FixedSliceQuotientConj (even11FixedSliceQuotientConj y) = y := by
  induction y using Quotient.inductionOn' with
  | _ p => simp

/-- Conjugation on the geometric quotient induces ordinary complex
conjugation on the invariant value. -/
@[simp] theorem even11FixedSliceQuotientU_conj
    (y : Even11FixedSliceFourierQuotient) :
    even11FixedSliceQuotientU (even11FixedSliceQuotientConj y) =
      conj (even11FixedSliceQuotientU y) := by
  induction y using Quotient.inductionOn' with
  | _ p => exact even11ProjectiveU_conj p.1

/-- A Fourier-conjugate real lift has `u` real and in the closed unit
interval.  Strictness will follow from the quotient polynomial's exclusion
of `u=1`. -/
theorem even11FixedSliceU_mem_unitInterval_of_real
    (p : Even11FixedSlicePoint) (hreal : even11FixedSliceIsReal p) :
    (even11FixedSliceU p).im = 0 ∧
      0 ≤ (even11FixedSliceU p).re ∧
      (even11FixedSliceU p).re ≤ 1 := by
  let h : Even6 ℂ := p.1.rep
  have hnz : h ≠ 0 := p.1.rep_nonzero
  have hmk : Projectivization.mk ℂ h hnz = p.1 := p.1.mk_rep
  have hh : FixedSliceEq even11FourierNormalized h := by
    apply (even11ProjectiveFixedSlice_mk h hnz).mp
    rw [hmk]
    exact p.2
  have hvreal : even11VectorIsFixedSliceReal h := by
    apply (even11ProjectiveIsReal_mk h hnz).mp
    rw [hmk]
    exact hreal
  have hline :=
    (even11VectorIsFixedSliceReal_iff_conj_fourier_line h hnz).mp hvreal
  rw [Projectivization.mk_eq_mk_iff'] at hline
  rcases hline with ⟨a, ha⟩
  have hcommon :=
    even11_normalized_fixedSlice_common_ne_zero_certified hnz hh
  have hprod : h 0 * even11FourierNormalized h 0 ≠ 0 := by
    simpa [fourierCoordProduct] using hcommon
  have hz : h 0 ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hw : even11FourierNormalized h 0 ≠ 0 :=
    (mul_ne_zero_iff.mp hprod).2
  have hzconj : conj (h 0) = a * even11FourierNormalized h 0 := by
    have hcoord := congrFun ha 0
    simpa [even11Conj] using hcoord.symm
  have hwconj : conj (even11FourierNormalized h 0) = a * h 0 := by
    calc
      conj (even11FourierNormalized h 0) =
          even11Conj (even11FourierNormalized h) 0 := rfl
      _ = even11FourierNormalized (even11Conj h) 0 := by
        rw [even11FourierNormalized_conj]
      _ = even11FourierNormalized (a • even11FourierNormalized h) 0 := by
        rw [ha]
      _ = a * h 0 := by simp [even11FourierNormalized_sq]
  have hpair := fixedSliceQPair_sq_mem_unitInterval_of_conj_swap
    hz hw hzconj hwconj
  have hu : even11FixedSliceU p =
      fixedSliceQPair (h 0) (even11FourierNormalized h 0) ^ 2 := by
    change even11ProjectiveU p.1 = _
    rw [← hmk, even11ProjectiveU_mk]
    rfl
  rwa [hu]

/-- A lift whose projective line is fixed by ordinary conjugation has real
`u` on the complementary side `u ≥ 1`. -/
theorem even11FixedSliceU_ge_one_of_ordinaryReal
    (p : Even11FixedSlicePoint)
    (hreal : even11FixedSliceIsOrdinaryReal p) :
    (even11FixedSliceU p).im = 0 ∧
      1 ≤ (even11FixedSliceU p).re := by
  let h : Even6 ℂ := p.1.rep
  have hnz : h ≠ 0 := p.1.rep_nonzero
  have hmk : Projectivization.mk ℂ h hnz = p.1 := p.1.mk_rep
  have hh : FixedSliceEq even11FourierNormalized h := by
    apply (even11ProjectiveFixedSlice_mk h hnz).mp
    rw [hmk]
    exact p.2
  have hline :
      Projectivization.mk ℂ (even11Conj h) (even11Conj_ne_zero hnz) =
        Projectivization.mk ℂ h hnz := by
    have hp : even11ProjectiveConj p.1 = p.1 :=
      congrArg Subtype.val hreal
    rw [← hmk] at hp
    simpa using hp
  rw [Projectivization.mk_eq_mk_iff'] at hline
  rcases hline with ⟨a, ha⟩
  have hcommon :=
    even11_normalized_fixedSlice_common_ne_zero_certified hnz hh
  have hprod : h 0 * even11FourierNormalized h 0 ≠ 0 := by
    simpa [fourierCoordProduct] using hcommon
  have hz : h 0 ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hw : even11FourierNormalized h 0 ≠ 0 :=
    (mul_ne_zero_iff.mp hprod).2
  have hzconj : conj (h 0) = a * h 0 := by
    have hcoord := congrFun ha 0
    simpa [even11Conj] using hcoord.symm
  have hwconj : conj (even11FourierNormalized h 0) =
      a * even11FourierNormalized h 0 := by
    calc
      conj (even11FourierNormalized h 0) =
          even11Conj (even11FourierNormalized h) 0 := rfl
      _ = even11FourierNormalized (even11Conj h) 0 := by
        rw [even11FourierNormalized_conj]
      _ = even11FourierNormalized (a • h) 0 := by rw [ha]
      _ = a * even11FourierNormalized h 0 := by simp
  have hpair := fixedSliceQPair_sq_ge_one_of_conj_common_scale
    hz hw hzconj hwconj
  have hu : even11FixedSliceU p =
      fixedSliceQPair (h 0) (even11FourierNormalized h 0) ^ 2 := by
    change even11ProjectiveU p.1 = _
    rw [← hmk, even11ProjectiveU_mk]
    rfl
  rwa [hu]

/-- Turn a proof that every concrete quotient value is a polynomial root into
the corresponding value-preserving root map. -/
def even11FixedSliceQuotientRootMap
    (hroot : ∀ y : Even11FixedSliceFourierQuotient,
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (even11FixedSliceQuotientU y)) :
    Even11FixedSliceFourierQuotient → FixedSliceQuotientRoot :=
  fun y ↦ ⟨even11FixedSliceQuotientU y, by
    rw [mem_rootSet]
    refine ⟨fixedSliceQuotientP16Q_separable.ne_zero, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map]
    exact hroot y⟩

@[simp] theorem even11FixedSliceQuotientRootMap_value
    (hroot : ∀ y : Even11FixedSliceFourierQuotient,
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (even11FixedSliceQuotientU y))
    (y : Even11FixedSliceFourierQuotient) :
    (even11FixedSliceQuotientRootMap hroot y : ℂ) =
      even11FixedSliceQuotientU y := by
  rfl

/-- The exact geometric certificate for the invariant spectrum.  Both fields refer
to the concrete quotient and its actual invariant `u`; no arbitrary
sixteen-element relabeling is accepted.  The real-locus criterion is derived below from this
separation theorem and the Fourier-conjugate real structure. -/
structure Even11FixedSliceGeometryCertificate where
  quotient_u_isRoot : ∀ y : Even11FixedSliceFourierQuotient,
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
      (even11FixedSliceQuotientU y)
  quotient_u_bijective :
    Function.Bijective
      (even11FixedSliceQuotientRootMap quotient_u_isRoot)

/-- Since `u` separates quotient points, a quotient point with real `u` is
fixed by quotient conjugation. -/
theorem Even11FixedSliceGeometryCertificate.quotientConj_eq_of_u_im_eq_zero
    (C : Even11FixedSliceGeometryCertificate)
    (y : Even11FixedSliceFourierQuotient)
    (him : (even11FixedSliceQuotientU y).im = 0) :
    even11FixedSliceQuotientConj y = y := by
  apply C.quotient_u_bijective.1
  apply Subtype.ext
  change even11FixedSliceQuotientU (even11FixedSliceQuotientConj y) =
    even11FixedSliceQuotientU y
  rw [even11FixedSliceQuotientU_conj]
  exact Complex.conj_eq_iff_im.mpr him

/-- Above a real quotient value, conjugation either fixes a lift or exchanges
it with its Fourier mate. -/
theorem Even11FixedSliceGeometryCertificate.conj_eq_self_or_fourier_of_u_im_eq_zero
    (C : Even11FixedSliceGeometryCertificate)
    (p : Even11FixedSlicePoint)
    (him : (even11FixedSliceQuotientU (Quotient.mk'' p)).im = 0) :
    even11FixedSliceConj p = p ∨
      even11FixedSliceConj p = even11FixedSliceFourier p := by
  have hq :
      (Quotient.mk'' (even11FixedSliceConj p) :
        Even11FixedSliceFourierQuotient) = Quotient.mk'' p := by
    exact C.quotientConj_eq_of_u_im_eq_zero (Quotient.mk'' p) him
  have hrel := Quotient.exact hq
  change AddAction.orbitRel Bool Even11FixedSlicePoint
    (even11FixedSliceConj p) p at hrel
  rw [AddAction.orbitRel_apply] at hrel
  rcases hrel with ⟨b, hb⟩
  cases b
  · left
    simpa using hb.symm
  · right
    simpa using hb.symm

/-- The two alternatives above are mutually exclusive because Fourier acts
freely on the fixed slice. -/
theorem even11FixedSlice_not_real_and_ordinaryReal
    (p : Even11FixedSlicePoint) :
    ¬(even11FixedSliceIsReal p ∧ even11FixedSliceIsOrdinaryReal p) := by
  rintro ⟨hreal, hord⟩
  rw [even11FixedSliceIsReal_iff_conj_eq_fourier] at hreal
  apply even11FixedSliceFourier_ne p
  rw [← hreal, hord]

/-- The closed upper bound for a real lift is strict because `u=1` is not a
root of the quotient polynomial. -/
theorem Even11FixedSliceGeometryCertificate.real_u_mem_interval
    (C : Even11FixedSliceGeometryCertificate)
    (p : Even11FixedSlicePoint) (hreal : even11FixedSliceIsReal p) :
    (even11FixedSliceU p).im = 0 ∧
      0 ≤ (even11FixedSliceU p).re ∧
      (even11FixedSliceU p).re < 1 := by
  have hle := even11FixedSliceU_mem_unitInterval_of_real p hreal
  refine ⟨hle.1, hle.2.1, lt_of_le_of_ne hle.2.2 ?_⟩
  intro hre
  have huone : even11FixedSliceU p = 1 := by
    apply Complex.ext
    · simpa using hre
    · simpa using hle.1
  apply fixedSliceQuotientP16Q_one_not_isRoot
  have hroot := C.quotient_u_isRoot
    (Quotient.mk'' p : Even11FixedSliceFourierQuotient)
  rwa [even11FixedSliceQuotientU_mk, huone] at hroot

/-- The complementary ordinary-real lift has `u>1`. -/
theorem Even11FixedSliceGeometryCertificate.ordinaryReal_u_gt_one
    (C : Even11FixedSliceGeometryCertificate)
    (p : Even11FixedSlicePoint)
    (hreal : even11FixedSliceIsOrdinaryReal p) :
    (even11FixedSliceU p).im = 0 ∧ 1 < (even11FixedSliceU p).re := by
  have hge := even11FixedSliceU_ge_one_of_ordinaryReal p hreal
  refine ⟨hge.1, lt_of_le_of_ne hge.2 ?_⟩
  intro hre
  have huone : even11FixedSliceU p = 1 := by
    apply Complex.ext
    · simpa using hre.symm
    · simpa using hge.1
  apply fixedSliceQuotientP16Q_one_not_isRoot
  have hroot := C.quotient_u_isRoot
    (Quotient.mk'' p : Even11FixedSliceFourierQuotient)
  rwa [even11FixedSliceQuotientU_mk, huone] at hroot

/-- The concrete quotient is identified with the sixteen certified
roots by its actual `u` value. -/
noncomputable def Even11FixedSliceGeometryCertificate.quotientRootEquiv
    (C : Even11FixedSliceGeometryCertificate) :
    Even11FixedSliceFourierQuotient ≃ FixedSliceQuotientRoot :=
  Equiv.ofBijective
    (even11FixedSliceQuotientRootMap C.quotient_u_isRoot)
    C.quotient_u_bijective

@[simp] theorem Even11FixedSliceGeometryCertificate.quotientRootEquiv_value
    (C : Even11FixedSliceGeometryCertificate)
    (y : Even11FixedSliceFourierQuotient) :
    (C.quotientRootEquiv y : ℂ) = even11FixedSliceQuotientU y := by
  rfl

/-- A concrete fixed-slice point is
real exactly when its quotient invariant is real and lies in `0 ≤ u < 1`. -/
theorem Even11FixedSliceGeometryCertificate.real_iff_u_interval
    (C : Even11FixedSliceGeometryCertificate)
    (p : Even11FixedSlicePoint) :
    even11FixedSliceIsReal p ↔
      (even11FixedSliceQuotientU (Quotient.mk'' p)).im = 0 ∧
      0 ≤ (even11FixedSliceQuotientU (Quotient.mk'' p)).re ∧
      (even11FixedSliceQuotientU (Quotient.mk'' p)).re < 1 := by
  simp only [even11FixedSliceQuotientU_mk]
  constructor
  · exact C.real_u_mem_interval p
  · intro hu
    have hdich := C.conj_eq_self_or_fourier_of_u_im_eq_zero p (by
      simpa using hu.1)
    rcases hdich with hord | hreal
    · have hgt := C.ordinaryReal_u_gt_one p hord
      linarith [hu.2.2, hgt.2]
    · exact (even11FixedSliceIsReal_iff_conj_eq_fourier p).mpr hreal

/-- The Fourier-conjugate real locus is exactly the two-sheeted
preimage of the split roots.  This is now a theorem, not certificate data. -/
theorem Even11FixedSliceGeometryCertificate.real_iff_split
    (C : Even11FixedSliceGeometryCertificate)
    (p : Even11FixedSlicePoint) :
    even11FixedSliceIsReal p ↔
      fixedSliceQuotientRootSplit
        (C.quotientRootEquiv (Quotient.mk'' p)) := by
  rw [fixedSliceQuotientRootSplit_iff,
    C.quotientRootEquiv_value]
  exact C.real_iff_u_interval p

/-- The class component of the canonical two-sheet equivalence is the actual
orbit quotient map. -/
@[simp] theorem even11FixedSliceTwoSheeted_fst
    (p : Even11FixedSlicePoint) :
    (even11FixedSliceTwoSheeted p).1 = Quotient.mk'' p := by
  rfl

/-- Steps 4 and 5 feed the generic finite assembly with no arbitrary choices:
the equivalence is induced by `u`, and `IsReal` is projective reality. -/
noncomputable def Even11FixedSliceGeometryCertificate.toFixedSliceGeometryCertificate
    (C : Even11FixedSliceGeometryCertificate) :
    FixedSliceGeometryCertificate
      Even11FixedSlicePoint Even11FixedSliceFourierQuotient where
  IsReal := even11FixedSliceIsReal
  decReal := Classical.decPred even11FixedSliceIsReal
  twoSheeted := even11FixedSliceTwoSheeted
  quotientRoots := C.quotientRootEquiv
  real_iff_split p := by
    rw [even11FixedSliceTwoSheeted_fst]
    exact C.real_iff_split p

/-- Concrete `32/16/8/7` conclusion obtained from the exact geometric
certificate. -/
theorem Even11FixedSliceGeometryCertificate.cardinality_core
    (C : Even11FixedSliceGeometryCertificate) :
    Nat.card Even11FixedSlicePoint = 32 ∧
    Nat.card {p : Even11FixedSlicePoint // even11FixedSliceIsReal p} = 16 ∧
    Fintype.card SplitQuotientRoot = 8 ∧
    Fintype.card NonGaussianSplitQuotientRoot = 7 := by
  exact fixedSlice_cardinality_core C.toFixedSliceGeometryCertificate

end

end Biunimodular.F11
