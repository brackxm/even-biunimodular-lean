/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceTrace

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar

noncomputable section

/-!
# Exact elementary points on the F11 fixed slice

The nonphysical rational quotient component `u = 176` is represented by a
vector which is constant away from zero.  This file constructs that point
directly and proves its invariant value.  The proof uses only the finite
Fourier sum and the quadratic equation `s² + 9s + 1 = 0`; it does not use an
eliminant or numerical root enumeration.

The Gaussian quotient component `u = 0` is represented by the quadratic
phase `x ↦ exp(2πi 5x²/11)`.  Its Gauss-sum identity is proved from the
Fourier involution and a finite multiplicity check in `ZMod 11`, again without
root enumeration.
-/

/-- The six even coordinates of a vector constant on the ten nonzero
elements of `ZMod 11`. -/
def even11ConstantVector (s : ℂ) : Even6 ℂ :=
  fun i ↦ if i = 0 then 1 else s

theorem even11Coordinate_eq_zero_iff (x : ZMod 11) :
    even11Coordinate x = 0 ↔ x = 0 := by
  native_decide +revert

@[simp] theorem even11Lift_constantVector (s : ℂ) (x : ZMod 11) :
    even11Lift (even11ConstantVector s) x = if x = 0 then 1 else s := by
  simp only [even11Lift_apply, even11ConstantVector]
  rw [if_congr (even11Coordinate_eq_zero_iff x) rfl rfl]

/-- The Fourier transform of a vector constant away from zero. -/
theorem even11Fourier_constantVector (s : ℂ) (k : Fin 6) :
    even11Fourier (even11ConstantVector s) k =
      if k = 0 then 1 + 10 * s else 1 - s := by
  rw [even11Fourier_apply, ZMod.dft_apply]
  simp only [even11Lift_constantVector, smul_eq_mul]
  have hsum :
      (∑ j : ZMod 11, stdAddChar (-(j * (k.1 : ZMod 11)))) =
        if k = 0 then 11 else 0 := by
    by_cases hk : k = 0
    · subst k
      simp
    · rw [ite_eq_right hk]
      have hkz : (k.1 : ZMod 11) ≠ 0 := by
        revert hk
        native_decide +revert
      have hneg : -(k.1 : ZMod 11) ≠ 0 := neg_ne_zero.mpr hkz
      simpa only [AddChar.mulShift_apply, mul_neg, mul_comm] using
        sum_eq_zero_of_ne_one (isPrimitive_stdAddChar 11 hneg)
  classical
  have hterm (j : ZMod 11) :
      stdAddChar (-(j * (k.1 : ZMod 11))) * (if j = 0 then 1 else s) =
        stdAddChar (-(j * (k.1 : ZMod 11))) * s +
          if j = 0 then 1 - s else 0 := by
    by_cases hj : j = 0 <;> simp [hj]
  rw [Finset.sum_congr rfl (fun j _ ↦ hterm j), Finset.sum_add_distrib,
    ← Finset.sum_mul, hsum]
  by_cases hk : k = 0
  all_goals simp [hk] <;> ring

/-- The quadratic constant branch satisfies all five projective fixed-slice
equations. -/
theorem even11ConstantVector_fixedSlice
    {s : ℂ} (hs : s ^ 2 + 9 * s + 1 = 0) :
    FixedSliceEq even11FourierNormalized (even11ConstantVector s) := by
  apply (even11_fixedSliceEq_normalized_iff _).2
  intro j
  simp only [fourierCoordProduct, even11Fourier_constantVector]
  fin_cases j <;> simp [even11ConstantVector] <;>
    linear_combination -hs

/-- The projective fixed-slice point belonging to a root of
`s² + 9s + 1`. -/
def even11ConstantBranchPoint (s : ℂ)
    (hs : s ^ 2 + 9 * s + 1 = 0) : Even11FixedSlicePoint :=
  ⟨Projectivization.mk ℂ (even11ConstantVector s) (by
      intro hzero
      have hz := congrFun hzero 0
      norm_num [even11ConstantVector] at hz),
    (even11ProjectiveFixedSlice_mk _ _).2
      (even11ConstantVector_fixedSlice hs)⟩

/-- Both roots of the constant-branch quadratic have quotient invariant
`u = 176`. -/
theorem even11ConstantBranchPoint_u
    {s : ℂ} (hs : s ^ 2 + 9 * s + 1 = 0) :
    even11FixedSliceU (even11ConstantBranchPoint s hs) = 176 := by
  rw [even11FixedSliceU_eq_trace]
  simp only [even11FixedSliceTrace, even11ConstantBranchPoint,
    even11ProjectiveTrace_mk, even11Fourier_constantVector]
  norm_num [even11ConstantVector]
  have ht : 1 + 10 * s ≠ 0 := by
    intro ht
    have hsval : s = -(1 / 10 : ℂ) := by
      linear_combination (1 / 10 : ℂ) * ht
    rw [hsval] at hs
    norm_num at hs
  apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))).2
  linear_combination (10000 * s ^ 2 - 86000 * s - 7600) * hs

/-- The exact `u = 176` quotient root is realized by the concrete fixed
slice. -/
theorem even11_constant_quotient_realized :
    ∃ y : Even11FixedSliceFourierQuotient,
      even11FixedSliceQuotientU y = 176 := by
  let s : ℂ := (-9 + (Real.sqrt 77 : ℂ)) / 2
  have hsqrt : (Real.sqrt 77 : ℂ) ^ 2 = 77 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 77)
  have hs : s ^ 2 + 9 * s + 1 = 0 := by
    dsimp [s]
    rw [div_pow]
    field_simp
    linear_combination hsqrt
  refine ⟨Quotient.mk'' (even11ConstantBranchPoint s hs), ?_⟩
  rw [even11FixedSliceQuotientU_mk]
  exact even11ConstantBranchPoint_u hs

/-! ## The Gaussian branch -/

/-- The even quadratic phase with coefficient `5` modulo `11`. -/
def even11GaussianVector : Even6 ℂ :=
  fun i ↦ stdAddChar (5 * (i.1 : ZMod 11) ^ 2)

/-- Its unnormalized quadratic Gauss sum. -/
def even11GaussianSum : ℂ :=
  ∑ x : ZMod 11, stdAddChar (5 * x ^ 2)

@[simp] theorem even11Lift_gaussianVector (x : ZMod 11) :
    even11Lift even11GaussianVector x = stdAddChar (5 * x ^ 2) := by
  rw [even11Lift_apply]
  simp only [even11GaussianVector]
  rcases even11Coordinate_cast_eq_or_eq_neg x with hx | hx
  · rw [hx]
  · rw [hx]
    congr 1
    ring

theorem even11Gaussian_complete_square (j k : ZMod 11) :
    -(j * k) + 5 * j ^ 2 = -(5 * k ^ 2) + 5 * (j + k) ^ 2 := by
  native_decide +revert

/-- Exact Fourier transform of the quadratic phase. -/
theorem even11Fourier_gaussianVector (k : Fin 6) :
    even11Fourier even11GaussianVector k =
      starRingEnd ℂ (even11GaussianVector k) * even11GaussianSum := by
  rw [even11Fourier_apply, ZMod.dft_apply]
  simp only [even11Lift_gaussianVector, smul_eq_mul]
  have hterm (j : ZMod 11) :
      stdAddChar (-(j * (k.1 : ZMod 11))) *
          stdAddChar (5 * j ^ 2) =
        stdAddChar (-(5 * (k.1 : ZMod 11) ^ 2)) *
          stdAddChar (5 * (j + (k.1 : ZMod 11)) ^ 2) := by
    rw [← map_add_eq_mul, ← map_add_eq_mul,
      even11Gaussian_complete_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hshift :
      (∑ j : ZMod 11,
        stdAddChar (5 * (j + (k.1 : ZMod 11)) ^ 2)) =
      even11GaussianSum := by
    rw [even11GaussianSum]
    exact Fintype.sum_equiv (Equiv.addRight (k.1 : ZMod 11)) _ _
      (fun j ↦ rfl)
  rw [hshift]
  congr 1
  simp only [even11GaussianVector, even11_conj_stdAddChar]

/-- For `11 ≡ 3 (mod 4)`, the quadratic Gauss sum is purely imaginary.
The finite multiset identity says that the square and negative-square fibers
together contain every residue twice. -/
theorem even11GaussianSum_add_conj :
    even11GaussianSum + starRingEnd ℂ even11GaussianSum = 0 := by
  rw [even11GaussianSum, map_sum]
  simp only [even11_conj_stdAddChar]
  let xs : Multiset (ZMod 11) := (Finset.univ : Finset (ZMod 11)).1
  have hcounts :
      xs.map (fun x ↦ 5 * x ^ 2) + xs.map (fun x ↦ -(5 * x ^ 2)) =
        xs + xs := by
    native_decide
  have hsum := congrArg
    (fun m : Multiset (ZMod 11) ↦ (m.map stdAddChar).sum) hcounts
  simp only [Multiset.map_add, Multiset.map_map, Multiset.sum_add] at hsum
  have hsum' :
      (xs.map (fun x ↦ stdAddChar (5 * x ^ 2))).sum +
          (xs.map (fun x ↦ stdAddChar (-(5 * x ^ 2)))).sum =
        (xs.map stdAddChar).sum + (xs.map stdAddChar).sum := by
    simpa only [Function.comp_apply] using hsum
  change (xs.map (fun x ↦ stdAddChar (5 * x ^ 2))).sum +
      (xs.map (fun x ↦ stdAddChar (-(5 * x ^ 2)))).sum = 0
  rw [hsum']
  change (∑ x : ZMod 11, stdAddChar x) +
      ∑ x : ZMod 11, stdAddChar x = 0
  have hone : (1 : ZMod 11) ≠ 0 := by native_decide
  have hne : (stdAddChar : AddChar (ZMod 11) ℂ) ≠ 1 := by
    simpa using
      (ZMod.isPrimitive_stdAddChar 11) (a := (1 : ZMod 11)) hone
  rw [sum_eq_zero_of_ne_one hne]
  simp

/-- The Fourier involution supplies the absolute-square identity for the
quadratic Gauss sum. -/
theorem even11GaussianSum_mul_conj :
    even11GaussianSum * starRingEnd ℂ even11GaussianSum = 11 := by
  have hFg : even11Fourier even11GaussianVector =
      even11GaussianSum • even11Conj even11GaussianVector := by
    funext k
    rw [even11Fourier_gaussianVector]
    simp only [Pi.smul_apply, smul_eq_mul, even11Conj]
    ring
  have hFc0 : even11Fourier (even11Conj even11GaussianVector) 0 =
      starRingEnd ℂ even11GaussianSum := by
    rw [← even11Fourier_conj]
    simp only [even11Conj, even11Fourier_gaussianVector,
      even11GaussianVector]
    simp
  have hs := congrFun (even11Fourier_sq even11GaussianVector) 0
  rw [hFg] at hs
  simp only [LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, hFc0,
    even11GaussianVector] at hs
  simpa using hs

/-- The exact quadratic Gauss-sum identity needed by the invariant. -/
theorem even11GaussianSum_sq : even11GaussianSum ^ 2 = -11 := by
  have hadd := even11GaussianSum_add_conj
  have hmul := even11GaussianSum_mul_conj
  linear_combination even11GaussianSum * hadd - hmul

/-- The quadratic Gaussian satisfies all projective fixed-slice equations. -/
theorem even11GaussianVector_fixedSlice :
    FixedSliceEq even11FourierNormalized even11GaussianVector := by
  apply (even11_fixedSliceEq_normalized_iff _).2
  intro j
  have hunit (k : Fin 6) :
      stdAddChar (5 * (k.1 : ZMod 11) ^ 2) *
          starRingEnd ℂ (stdAddChar (5 * (k.1 : ZMod 11) ^ 2)) = 1 := by
    rw [even11_conj_stdAddChar, ← map_add_eq_mul]
    simp
  simp only [fourierCoordProduct, even11Fourier_gaussianVector,
    even11GaussianVector]
  rw [← mul_assoc, hunit, one_mul, ← mul_assoc, hunit, one_mul]

/-- The concrete projective Gaussian point. -/
def even11GaussianBranchPoint : Even11FixedSlicePoint :=
  ⟨Projectivization.mk ℂ even11GaussianVector (by
      intro hzero
      have hz := congrFun hzero 0
      norm_num [even11GaussianVector] at hz),
    (even11ProjectiveFixedSlice_mk _ _).2 even11GaussianVector_fixedSlice⟩

/-- The Gaussian point has quotient invariant `u = 0`. -/
theorem even11GaussianBranchPoint_u :
    even11FixedSliceU even11GaussianBranchPoint = 0 := by
  rw [even11FixedSliceU_eq_trace]
  have htrace : even11FixedSliceTrace even11GaussianBranchPoint =
      even11GaussianSum := by
    simp only [even11FixedSliceTrace, even11GaussianBranchPoint,
      even11ProjectiveTrace_mk, even11Fourier_gaussianVector,
      even11GaussianVector]
    simp
  rw [htrace, even11GaussianSum_sq]
  norm_num

/-- The exact Gaussian quotient root `u = 0` is realized by the concrete
fixed slice. -/
theorem even11_gaussian_quotient_realized :
    ∃ y : Even11FixedSliceFourierQuotient,
      even11FixedSliceQuotientU y = 0 := by
  refine ⟨Quotient.mk'' even11GaussianBranchPoint, ?_⟩
  rw [even11FixedSliceQuotientU_mk]
  exact even11GaussianBranchPoint_u

end

end Biunimodular.F11
