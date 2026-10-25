/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceGeometryCertificate
import Biunimodular.F11.P150PhaseBoxUniqueness11
import Biunimodular.F11.PhaseGramFixedSliceBridge11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace Biunimodular.F11

open scoped ComplexConjugate LinearAlgebra.Projectivization
open ZMod Polynomial

noncomputable section

/-!
# Physical fixed-slice points produce phase solutions

The Fourier-conjugate real locus of the already-certified fixed slice has a
canonical unimodular representative.  Its normalized even coordinates are a
phase solution.  This supplies existence and realization independently of
the degree-252 RUR computation.
-/

def cyclicAutocorrelation11 (f : ZMod 11 → ℂ) (r : ZMod 11) : ℂ :=
  ∑ t, f (t + r) * star (f t)

/-- Finite Wiener--Khinchin identity for the DFT convention used by
`Mathlib.Analysis.Fourier.ZMod`. -/
theorem dft_cyclicAutocorrelation11 (f : ZMod 11 → ℂ) (k : ZMod 11) :
    ZMod.dft (cyclicAutocorrelation11 f) k =
      (Complex.normSq (ZMod.dft f k) : ℂ) := by
  rw [ZMod.dft_apply, Complex.normSq_eq_conj_mul_self]
  simp only [cyclicAutocorrelation11, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [map_sum]
  simp_rw [map_mul, even11_conj_stdAddChar]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  have hreindex :
      (∑ r : ZMod 11,
          stdAddChar (-(r * k)) * (f (t + r) * star (f t))) =
        ∑ u : ZMod 11,
          stdAddChar (-((u - t) * k)) * (f u * star (f t)) := by
    exact Fintype.sum_equiv (Equiv.addLeft t) _ _ fun r ↦ by
      change
        stdAddChar (-(r * k)) * (f (t + r) * star (f t)) =
          stdAddChar (-(((t + r) - t) * k)) * (f (t + r) * star (f t))
      congr 2
      · congr 1
        ring
  rw [hreindex]
  apply Finset.sum_congr rfl
  intro u _
  rw [show -((u - t) * k) = t * k + -(u * k) by ring]
  rw [AddChar.map_add_eq_mul]
  simp only [starRingEnd_apply]
  ring_nf

/-- A flat Fourier spectrum has delta autocorrelation. -/
theorem cyclicAutocorrelation11_eq_zero_of_dft_normSq
    (f : ZMod 11 → ℂ)
    (hflat : ∀ k, Complex.normSq (ZMod.dft f k) = 11) :
    ∀ r, r ≠ 0 → cyclicAutocorrelation11 f r = 0 := by
  let delta : ZMod 11 → ℂ := fun r ↦ if r = 0 then 11 else 0
  have hdft : ZMod.dft (cyclicAutocorrelation11 f) = ZMod.dft delta := by
    funext k
    rw [dft_cyclicAutocorrelation11, hflat]
    rw [ZMod.dft_apply]
    simp [delta]
  have heq : cyclicAutocorrelation11 f = delta := ZMod.dft.injective hdft
  intro r hr
  rw [heq]
  simp [delta, hr]

/-- The hand-written `Fin 11` autocorrelation used by the phase equations is
the same cyclic sum as the `ZMod 11` Fourier formulation. -/
theorem autocorr11_eq_cyclicAutocorrelation11
    (z : Fin 11 → ℂ) (r : Fin 11) :
    autocorr11 z r =
      cyclicAutocorrelation11 (fun t : ZMod 11 ↦ z t) r := by
  unfold autocorr11 cyclicAutocorrelation11
  apply Finset.sum_congr rfl
  intro t _
  congr 2

private theorem fixedSliceLag1raw (x : PhaseCoords11) :
    autocorr11 (phaseSignal11 x) 1 =
      phaseC (2*x.a*x.c+2*x.a+2*x.b*x.d+2*x.c*x.e+2*x.d*x.f+
        2*x.e*x.g+2*x.f*x.h+2*x.g*x.j+2*x.h*x.k+x.j^2+x.k^2) 0 := by
  apply Complex.ext <;>
    norm_num [autocorr11, phaseSignal11, phaseC, add11,
      Fin.sum_univ_succ] <;> ring

private theorem fixedSliceLag2raw (x : PhaseCoords11) :
    autocorr11 (phaseSignal11 x) 2 =
      phaseC (x.a^2+x.b^2+2*x.a*x.e+2*x.b*x.f+2*x.c*x.g+2*x.c+
        2*x.d*x.h+2*x.e*x.j+2*x.f*x.k+2*x.g*x.j+2*x.h*x.k) 0 := by
  apply Complex.ext <;>
    norm_num [autocorr11, phaseSignal11, phaseC, add11,
      Fin.sum_univ_succ] <;> ring

private theorem fixedSliceLag3raw (x : PhaseCoords11) :
    autocorr11 (phaseSignal11 x) 3 =
      phaseC (2*x.a*x.c+2*x.a*x.g+2*x.b*x.d+2*x.b*x.h+2*x.c*x.j+
        2*x.d*x.k+2*x.e*x.j+2*x.e+2*x.f*x.k+x.g^2+x.h^2) 0 := by
  apply Complex.ext <;>
    norm_num [autocorr11, phaseSignal11, phaseC, add11,
      Fin.sum_univ_succ] <;> ring

private theorem fixedSliceLag4raw (x : PhaseCoords11) :
    autocorr11 (phaseSignal11 x) 4 =
      phaseC (2*x.a*x.e+2*x.a*x.j+2*x.b*x.f+2*x.b*x.k+x.c^2+
        2*x.c*x.j+x.d^2+2*x.d*x.k+2*x.e*x.g+2*x.f*x.h+2*x.g) 0 := by
  apply Complex.ext <;>
    norm_num [autocorr11, phaseSignal11, phaseC, add11,
      Fin.sum_univ_succ] <;> ring

private theorem fixedSliceLag5raw (x : PhaseCoords11) :
    autocorr11 (phaseSignal11 x) 5 =
      phaseC (2*x.a*x.g+2*x.a*x.j+2*x.b*x.h+2*x.b*x.k+2*x.c*x.e+
        2*x.c*x.g+2*x.d*x.f+2*x.d*x.h+x.e^2+x.f^2+2*x.j) 0 := by
  apply Complex.ext <;>
    norm_num [autocorr11, phaseSignal11, phaseC, add11,
      Fin.sum_univ_succ] <;> ring

/-- The unit-circle equations and five nontrivial autocorrelations recover
the original polynomial phase system. -/
theorem isPhaseSolution_of_normSq_autocorr11
    (x : PhaseCoords11)
    (hnorm : ∀ t, Complex.normSq (phaseSignal11 x t) = 1)
    (hzero : ∀ r, r ≠ 0 → autocorr11 (phaseSignal11 x) r = 0) :
    x.IsPhaseSolution := by
  have hab : x.a ^ 2 + x.b ^ 2 = 1 := by
    simpa [phaseSignal11, phaseC, Complex.normSq, pow_two] using hnorm 1
  have hcd : x.c ^ 2 + x.d ^ 2 = 1 := by
    simpa [phaseSignal11, phaseC, Complex.normSq, pow_two] using hnorm 2
  have hef : x.e ^ 2 + x.f ^ 2 = 1 := by
    simpa [phaseSignal11, phaseC, Complex.normSq, pow_two] using hnorm 3
  have hgh : x.g ^ 2 + x.h ^ 2 = 1 := by
    simpa [phaseSignal11, phaseC, Complex.normSq, pow_two] using hnorm 4
  have hjk : x.j ^ 2 + x.k ^ 2 = 1 := by
    simpa [phaseSignal11, phaseC, Complex.normSq, pow_two] using hnorm 5
  have hz1 := hzero 1 (by decide)
  have hz2 := hzero 2 (by decide)
  have hz3 := hzero 3 (by decide)
  have hz4 := hzero 4 (by decide)
  have hz5 := hzero 5 (by decide)
  rw [fixedSliceLag1raw] at hz1
  rw [fixedSliceLag2raw] at hz2
  rw [fixedSliceLag3raw] at hz3
  rw [fixedSliceLag4raw] at hz4
  rw [fixedSliceLag5raw] at hz5
  have hr1 := congrArg Complex.re hz1
  have hr2 := congrArg Complex.re hz2
  have hr3 := congrArg Complex.re hz3
  have hr4 := congrArg Complex.re hz4
  have hr5 := congrArg Complex.re hz5
  simp only [phaseC_re, Complex.zero_re] at hr1 hr2 hr3 hr4 hr5
  refine ⟨⟨hab, hcd, hef, hgh, hjk⟩, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [PhaseCoords11.E1]
    rw [← hjk]
    convert hr1 using 1
    all_goals ring
  · dsimp [PhaseCoords11.E2]
    rw [← hab]
    convert hr2 using 1
    all_goals ring
  · dsimp [PhaseCoords11.E3]
    rw [← hgh]
    convert hr3 using 1
    all_goals ring
  · dsimp [PhaseCoords11.E4]
    rw [← hcd]
    convert hr4 using 1
    all_goals ring
  · dsimp [PhaseCoords11.E5]
    rw [← hef]
    convert hr5 using 1
    all_goals ring

/-- On the Fourier-conjugate real locus, the fixed-slice equation forces
every coordinate and every normalized Fourier coordinate to have the same
squared norm as the zeroth coordinate. -/
theorem even11FixedSlice_real_rep_normSq
    (p : Even11FixedSlicePoint) (hreal : even11FixedSliceIsReal p) :
    let h : Even6 ℂ := p.1.rep
    ∀ i,
      Complex.normSq (h i) = Complex.normSq (h 0) ∧
      Complex.normSq (even11FourierNormalized h i) =
        Complex.normSq (h 0) := by
  let h : Even6 ℂ := p.1.rep
  have hnz : h ≠ 0 := p.1.rep_nonzero
  have hmk : Projectivization.mk ℂ h hnz = p.1 := p.1.mk_rep
  have hfixed : FixedSliceEq even11FourierNormalized h := by
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
  have hconjh (i : Fin 6) :
      conj (h i) = a * even11FourierNormalized h i := by
    have hi := congrFun ha i
    simpa [even11Conj] using hi.symm
  have hconjF (i : Fin 6) :
      conj (even11FourierNormalized h i) = a * h i := by
    calc
      conj (even11FourierNormalized h i) =
          even11Conj (even11FourierNormalized h) i := rfl
      _ = even11FourierNormalized (even11Conj h) i := by
        rw [even11FourierNormalized_conj]
      _ = even11FourierNormalized
          (a • even11FourierNormalized h) i := by rw [ha]
      _ = a * h i := by simp [even11FourierNormalized_sq]
  dsimp only
  intro i
  have hprod : h i * even11FourierNormalized h i =
      h 0 * even11FourierNormalized h 0 := by
    simpa [fourierCoordProduct] using hfixed i
  constructor
  · change Complex.normSq (h i) = Complex.normSq (h 0)
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_conj_mul_self, hconjh i, hconjh 0]
    calc
      (a * even11FourierNormalized h i) * h i =
          a * (h i * even11FourierNormalized h i) := by ring
      _ = a * (h 0 * even11FourierNormalized h 0) := by rw [hprod]
      _ = (a * even11FourierNormalized h 0) * h 0 := by ring
  · change Complex.normSq (even11FourierNormalized h i) =
      Complex.normSq (h 0)
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_conj_mul_self, hconjF i, hconjh 0]
    calc
      (a * h i) * even11FourierNormalized h i =
          a * (h i * even11FourierNormalized h i) := by ring
      _ = a * (h 0 * even11FourierNormalized h 0) := by rw [hprod]
      _ = (a * even11FourierNormalized h 0) * h 0 := by ring

/-- Real coordinates of the normalized even representative. -/
def phaseCoordsOfEven11 (h : Even6 ℂ) : PhaseCoords11 where
  a := (h 1 / h 0).re
  b := (h 1 / h 0).im
  c := (h 2 / h 0).re
  d := (h 2 / h 0).im
  e := (h 3 / h 0).re
  f := (h 3 / h 0).im
  g := (h 4 / h 0).re
  h := (h 4 / h 0).im
  j := (h 5 / h 0).re
  k := (h 5 / h 0).im

theorem phaseC_re_im (z : ℂ) : phaseC z.re z.im = z := by
  apply Complex.ext <;> rfl

/-- The phase signal attached to the five even coordinates is precisely the
full even lift divided by its zeroth coordinate. -/
theorem phaseSignal11_phaseCoordsOfEven11
    (h : Even6 ℂ) (hh0 : h 0 ≠ 0) (t : Fin 11) :
    phaseSignal11 (phaseCoordsOfEven11 h) t =
      even11Lift ((h 0)⁻¹ • h) (t.1 : ZMod 11) := by
  have hcoord0 : even11Coordinate (0 : ZMod 11) = 0 := by native_decide
  have hcoord1 : even11Coordinate (1 : ZMod 11) = 1 := by native_decide
  have hcoord2 : even11Coordinate (2 : ZMod 11) = 2 := by native_decide
  have hcoord3 : even11Coordinate (3 : ZMod 11) = 3 := by native_decide
  have hcoord4 : even11Coordinate (4 : ZMod 11) = 4 := by native_decide
  have hcoord5 : even11Coordinate (5 : ZMod 11) = 5 := by native_decide
  have hcoord6 : even11Coordinate (6 : ZMod 11) = 5 := by native_decide
  have hcoord7 : even11Coordinate (7 : ZMod 11) = 4 := by native_decide
  have hcoord8 : even11Coordinate (8 : ZMod 11) = 3 := by native_decide
  have hcoord9 : even11Coordinate (9 : ZMod 11) = 2 := by native_decide
  have hcoord10 : even11Coordinate (10 : ZMod 11) = 1 := by native_decide
  fin_cases t <;>
    simp [phaseSignal11, phaseCoordsOfEven11,
      even11Lift_apply, hcoord0, hcoord1, hcoord2, hcoord3, hcoord4,
      hcoord5, hcoord6, hcoord7, hcoord8, hcoord9, hcoord10,
      smul_eq_mul, hh0, div_eq_mul_inv,
      mul_comm] <;>
    apply Complex.ext <;>
      simp [phaseC, div_eq_mul_inv, mul_comm]

/-- The normalized representative of a real fixed-slice point is flat in
both the time and Fourier domains. -/
theorem even11FixedSlice_real_rep_flat
    (p : Even11FixedSlicePoint) (hreal : even11FixedSliceIsReal p) :
    let h : Even6 ℂ := p.1.rep
    h 0 ≠ 0 ∧
      (∀ t, Complex.normSq (even11Lift ((h 0)⁻¹ • h) t) = 1) ∧
      (∀ k, Complex.normSq
        (ZMod.dft (even11Lift ((h 0)⁻¹ • h)) k) = 11) := by
  let h : Even6 ℂ := p.1.rep
  have hnz : h ≠ 0 := p.1.rep_nonzero
  have hmk : Projectivization.mk ℂ h hnz = p.1 := p.1.mk_rep
  have hfixed : FixedSliceEq even11FourierNormalized h := by
    apply (even11ProjectiveFixedSlice_mk h hnz).mp
    rw [hmk]
    exact p.2
  have hcommon :=
    even11_normalized_fixedSlice_common_ne_zero_certified hnz hfixed
  have hh0 : h 0 ≠ 0 := fixedSlice_all_h_nonzero hfixed hcommon 0
  have hnorm := even11FixedSlice_real_rep_normSq p hreal
  change ∀ i,
    Complex.normSq (h i) = Complex.normSq (h 0) ∧
    Complex.normSq (even11FourierNormalized h i) =
      Complex.normSq (h 0) at hnorm
  dsimp only
  refine ⟨hh0, ?_, ?_⟩
  · intro t
    rw [even11Lift_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_inv]
    rw [(hnorm (even11Coordinate t)).1]
    exact inv_mul_cancel₀ ((not_congr Complex.normSq_eq_zero).mpr hh0)
  · intro k
    have hsR : Real.sqrt 11 ≠ 0 :=
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 11)).ne'
    have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by exact_mod_cast hsR
    have hs2R : Real.sqrt 11 * Real.sqrt 11 = 11 :=
      Real.mul_self_sqrt (by norm_num)
    have hsNorm : Complex.normSq (Real.sqrt 11 : ℂ) = 11 := by
      simp [Complex.normSq, hs2R]
    have hraw : ZMod.dft (even11Lift h) k =
        (Real.sqrt 11 : ℂ) * even11Lift (even11FourierNormalized h) k := by
      have hi := congrFun (even11Lift_fourierNormalized h) k
      change even11Lift (even11FourierNormalized h) k =
        (Real.sqrt 11 : ℂ)⁻¹ * ZMod.dft (even11Lift h) k at hi
      field_simp [hs] at hi ⊢
      exact hi.symm
    have hdft : ZMod.dft (even11Lift ((h 0)⁻¹ • h)) k =
        (h 0)⁻¹ * ZMod.dft (even11Lift h) k := by
      have hlift : even11Lift ((h 0)⁻¹ • h) =
          (h 0)⁻¹ • even11Lift h := rfl
      rw [hlift, ZMod.dft_const_smul]
      rfl
    rw [hdft, hraw, Complex.normSq_mul, Complex.normSq_inv,
      Complex.normSq_mul, hsNorm]
    rw [even11Lift_apply]
    rw [(hnorm (even11Coordinate k)).2]
    have hh0norm : Complex.normSq (h 0) ≠ 0 :=
      (not_congr Complex.normSq_eq_zero).mpr hh0
    field_simp

/-- Normalizing any Fourier-conjugate real fixed-slice point gives a
solution of the original ten real phase equations. -/
theorem phaseCoordsOfEven11_isPhaseSolution
    (p : Even11FixedSlicePoint) (hreal : even11FixedSliceIsReal p) :
    let h : Even6 ℂ := p.1.rep
    (phaseCoordsOfEven11 h).IsPhaseSolution := by
  let h : Even6 ℂ := p.1.rep
  have hflat := even11FixedSlice_real_rep_flat p hreal
  change h 0 ≠ 0 ∧
      (∀ t, Complex.normSq (even11Lift ((h 0)⁻¹ • h) t) = 1) ∧
      (∀ k, Complex.normSq
        (ZMod.dft (even11Lift ((h 0)⁻¹ • h)) k) = 11) at hflat
  rcases hflat with ⟨hh0, htime, hfourier⟩
  dsimp only
  apply isPhaseSolution_of_normSq_autocorr11
  · intro t
    rw [phaseSignal11_phaseCoordsOfEven11 h hh0 t]
    exact htime (t.1 : ZMod 11)
  · intro r hr
    rw [autocorr11_eq_cyclicAutocorrelation11]
    have hrz : (r : ZMod 11) ≠ 0 := by
      intro hz
      exact hr hz
    have hz := cyclicAutocorrelation11_eq_zero_of_dft_normSq
      (even11Lift ((h 0)⁻¹ • h)) hfourier r hrz
    convert hz using 1
    congr 1
    funext t
    have ht := phaseSignal11_phaseCoordsOfEven11 h hh0 (t : Fin 11)
    change phaseSignal11 (phaseCoordsOfEven11 h) t =
      even11Lift ((h 0)⁻¹ • h) (t.val : ZMod 11) at ht
    rw [ZMod.natCast_zmod_val] at ht
    change phaseSignal11 (phaseCoordsOfEven11 h) t =
      even11Lift ((h 0)⁻¹ • h) t
    exact ht

/-- The phase invariant of the normalized representative is the homogeneous
fixed-slice invariant of the original projective point. -/
theorem phaseInvariantU11_phaseCoordsOfEven11
    (p : Even11FixedSlicePoint) (hreal : even11FixedSliceIsReal p) :
    let h : Even6 ℂ := p.1.rep
    (phaseInvariantU11 (phaseCoordsOfEven11 h) : ℂ) =
      even11FixedSliceU p := by
  let h : Even6 ℂ := p.1.rep
  let w : ℂ := even11FourierNormalized h 0
  let r : ℂ := w / h 0
  have hnz : h ≠ 0 := p.1.rep_nonzero
  have hmk : Projectivization.mk ℂ h hnz = p.1 := p.1.mk_rep
  have hfixed : FixedSliceEq even11FourierNormalized h := by
    apply (even11ProjectiveFixedSlice_mk h hnz).mp
    rw [hmk]
    exact p.2
  have hcommon :=
    even11_normalized_fixedSlice_common_ne_zero_certified hnz hfixed
  have hh0 : h 0 ≠ 0 := fixedSlice_all_h_nonzero hfixed hcommon 0
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact fixedSlice_all_Fh_nonzero hfixed hcommon 0
  have hnorm := even11FixedSlice_real_rep_normSq p hreal
  change ∀ i,
    Complex.normSq (h i) = Complex.normSq (h 0) ∧
    Complex.normSq (even11FourierNormalized h i) =
      Complex.normSq (h 0) at hnorm
  have hsR : Real.sqrt 11 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 11)).ne'
  have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by exact_mod_cast hsR
  have hr_formula :
      r = (Real.sqrt 11 : ℂ)⁻¹ *
        (1 + 2 * (h 1 / h 0 + h 2 / h 0 + h 3 / h 0 +
          h 4 / h 0 + h 5 / h 0)) := by
    dsimp only [r, w]
    change ((Real.sqrt 11 : ℂ)⁻¹ * even11Fourier h 0) / h 0 = _
    rw [even11Fourier_zero]
    field_simp [hh0, hs]
  have hsInv : (Real.sqrt 11 : ℂ)⁻¹ =
      ((Real.sqrt 11)⁻¹ : ℝ) := by
    exact_mod_cast rfl
  have hq : phaseInvariantQ11 (phaseCoordsOfEven11 h) = r.re := by
    have hrre := congrArg Complex.re hr_formula
    rw [hsInv] at hrre
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_re, Complex.one_re] at hrre
    norm_num at hrre
    rw [hrre]
    simp only [phaseInvariantQ11, phaseCoordsOfEven11]
    rw [div_eq_mul_inv]
    ring
  have hrnorm : Complex.normSq r = 1 := by
    dsimp only [r, w]
    simp only [div_eq_mul_inv, Complex.normSq_mul, Complex.normSq_inv]
    rw [(hnorm 0).2]
    exact mul_inv_cancel₀ ((not_congr Complex.normSq_eq_zero).mpr hh0)
  have hrconj : conj r = r⁻¹ := by
    rw [Complex.inv_def, hrnorm]
    norm_num
  have hpair : fixedSliceQPair (h 0) w = (r.re : ℂ) := by
    rw [show fixedSliceQPair (h 0) w = fixedSliceQPair w (h 0) by
      simp only [fixedSliceQPair]
      congr 1 <;> ring]
    rw [fixedSliceQPair_ratio hw0 hh0]
    change (r + r⁻¹) / 2 = (r.re : ℂ)
    rw [← hrconj]
    apply Complex.ext
    · simp [div_eq_mul_inv]
      ring
    · simp [div_eq_mul_inv]
  have hu : even11FixedSliceU p = fixedSliceQPair (h 0) w ^ 2 := by
    change even11ProjectiveU p.1 = _
    rw [← hmk, even11ProjectiveU_mk]
    rfl
  dsimp only
  calc
    (phaseInvariantU11 (phaseCoordsOfEven11 h) : ℂ) =
        (phaseInvariantQ11 (phaseCoordsOfEven11 h) : ℂ) ^ 2 := by
          simp [phaseInvariantU11]
    _ = (r.re : ℂ) ^ 2 := by rw [hq]
    _ = fixedSliceQPair (h 0) w ^ 2 := by rw [hpair]
    _ = even11FixedSliceU p := hu.symm

/-- Each of the eight certified split quotient roots is realized by a
physical phase solution, directly from the fixed-slice geometry. -/
theorem splitQuotientRoot_phase_realized11
    (r : SplitQuotientRoot) :
    ∃ s : PhaseSolution11,
      (phaseInvariantU11 s.1 : ℂ) = (r : ℂ) := by
  let F : Even11FixedSliceGeometryCertificate :=
    even11FixedSliceGeometryCertificate
  let y : Even11FixedSliceFourierQuotient :=
    F.quotientRootEquiv.symm r.1
  obtain ⟨p, hp⟩ := Quotient.exists_rep y
  have hreal : even11FixedSliceIsReal p := by
    apply (F.real_iff_split p).2
    have hvalue := congrArg F.quotientRootEquiv hp
    rw [hvalue]
    simpa [y] using r.2
  let h : Even6 ℂ := p.1.rep
  have hphase : (phaseCoordsOfEven11 h).IsPhaseSolution := by
    exact phaseCoordsOfEven11_isPhaseSolution p hreal
  let s : PhaseSolution11 := ⟨phaseCoordsOfEven11 h, hphase⟩
  refine ⟨s, ?_⟩
  change (phaseInvariantU11 (phaseCoordsOfEven11 h) : ℂ) = (r : ℂ)
  rw [phaseInvariantU11_phaseCoordsOfEven11 p hreal]
  calc
    even11FixedSliceU p =
        even11FixedSliceQuotientU (Quotient.mk'' p) := rfl
    _ = even11FixedSliceQuotientU y :=
      congrArg even11FixedSliceQuotientU hp
    _ = (F.quotientRootEquiv y : ℂ) :=
      (F.quotientRootEquiv_value y).symm
    _ = (r : ℂ) := by simp [y]

noncomputable def splitRootPhaseSolution11
    (r : SplitQuotientRoot) : PhaseSolution11 :=
  Classical.choose (splitQuotientRoot_phase_realized11 r)

@[simp] theorem splitRootPhaseSolution11_value
    (r : SplitQuotientRoot) :
    (phaseInvariantU11 (splitRootPhaseSolution11 r).1 : ℂ) = (r : ℂ) :=
  Classical.choose_spec (splitQuotientRoot_phase_realized11 r)

noncomputable def splitRootPhaseOrbit11
    (r : SplitQuotientRoot) : PhaseSolution11Orbit :=
  Quotient.mk'' (splitRootPhaseSolution11 r)

theorem splitRootPhaseOrbit11_injective :
    Function.Injective splitRootPhaseOrbit11 := by
  intro r s hrs
  have hv := congrArg phaseSolution11OrbitInvariantU hrs
  change phaseInvariantU11 (splitRootPhaseSolution11 r).1 =
    phaseInvariantU11 (splitRootPhaseSolution11 s).1 at hv
  have hvc := congrArg ((↑) : ℝ → ℂ) hv
  rw [splitRootPhaseSolution11_value, splitRootPhaseSolution11_value] at hvc
  apply Subtype.ext
  apply Subtype.ext
  exact hvc

/-- The eight geometric realizations exhaust the phase orbit space because
the independent P150 box argument gives the matching upper bound. -/
theorem splitRootPhaseOrbit11_bijective :
    Function.Bijective splitRootPhaseOrbit11 := by
  let _ := p150KRootCoverCertificate11.phaseSolutionFinite
    phaseAcceptedBoxUniquenessCertificate11
  let _ : Finite PhaseSolution11Orbit := inferInstance
  apply splitRootPhaseOrbit11_injective.bijective_of_nat_card_le
  calc
    Nat.card PhaseSolution11Orbit ≤ 8 :=
      p150KRootCoverCertificate11.phaseSolutionOrbit_card_le_8
        phaseAcceptedBoxUniquenessCertificate11
    _ = Nat.card SplitQuotientRoot := by
      simpa only [Nat.card_eq_fintype_card] using
        splitQuotientRoot_card.symm

/-- Hence every phase invariant is a root of the fixed-slice quotient
polynomial; no degree-252 RUR reconstruction is needed for this step. -/
theorem phaseInvariantU11_is_fixedSliceQuotientRoot
    (s : PhaseSolution11) :
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
      (phaseInvariantU11 s.1 : ℂ) := by
  obtain ⟨r, hr⟩ := splitRootPhaseOrbit11_bijective.2
    (Quotient.mk'' s)
  have hv := congrArg phaseSolution11OrbitInvariantU hr
  change phaseInvariantU11 (splitRootPhaseSolution11 r).1 =
    phaseInvariantU11 s.1 at hv
  have hvc := congrArg ((↑) : ℝ → ℂ) hv
  rw [splitRootPhaseSolution11_value] at hvc
  rw [← hvc]
  have hroot := (Polynomial.mem_rootSet.mp r.1.2).2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hroot
  exact hroot

/-- The completed exact fixed-slice realization, P150 cover, and local box
uniqueness assemble the Gram spectrum certificate. -/
theorem phaseGramSpectrumCertificate11 : PhaseGramSpectrumCertificate :=
  p150_phaseGramSpectrumCertificate
    p150KRootCoverCertificate11
    phaseAcceptedBoxUniquenessCertificate11
    phaseInvariantU11_is_fixedSliceQuotientRoot
    splitQuotientRoot_phase_realized11

/-- Concrete closed form of the F11 classification: both the fixed-slice
counts and the physical `80 = 10 + 70` phase counts, without certificate
hypotheses. -/
theorem phaseSolution11_classification_complete :
    (Nat.card Even11FixedSlicePoint = 32 ∧
      Nat.card {p : Even11FixedSlicePoint // even11FixedSliceIsReal p} = 16 ∧
      Fintype.card SplitQuotientRoot = 8 ∧
      Fintype.card NonGaussianSplitQuotientRoot = 7) ∧
    (Nat.card PhaseSolution11 = 80 ∧
      Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 = 0} = 10 ∧
      Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 ≠ 0} = 70) :=
  classification11_phaseSolution_from_gram
    even11FixedSliceGeometryCertificate
    phaseGramSpectrumCertificate11

end

end Biunimodular.F11
