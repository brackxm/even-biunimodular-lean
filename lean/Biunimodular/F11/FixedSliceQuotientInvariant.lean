/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceCommonProduct
import Biunimodular.F11.FixedSliceInvolution
import Biunimodular.F11.FixedSliceBoundaryReduction

set_option autoImplicit false

namespace Biunimodular.F11

section Field

variable {K : Type*} [Field K]

/-- Numerator of the quotient invariant q in homogeneous coordinates. -/
def fixedSliceQNum (F : Even6 K →ₗ[K] Even6 K) (h : Even6 K) : K :=
  (h 0)^2 + (F h 0)^2

/-- Denominator of the quotient invariant q. -/
def fixedSliceQDen (F : Even6 K →ₗ[K] Even6 K) (h : Even6 K) : K :=
  2 * h 0 * F h 0

/-- Homogeneous polynomial identity expressing `u=q²` without division. -/
def fixedSliceUEquation (F : Even6 K →ₗ[K] Even6 K)
    (h : Even6 K) (u : K) : Prop :=
  (fixedSliceQNum F h)^2 = u * (fixedSliceQDen F h)^2

/-- The affine quotient value `u = q²`, defined whenever the homogeneous
denominator is nonzero. -/
def fixedSliceUValue (F : Even6 K →ₗ[K] Even6 K) (h : Even6 K) : K :=
  (fixedSliceQNum F h / fixedSliceQDen F h) ^ 2

/-- Multiplying the Fourier operator by a square-one scalar does not change
the squared quotient invariant. -/
theorem fixedSliceUValue_smul_operator_of_sq_eq_one
    {F : Even6 K →ₗ[K] Even6 K} {c : K} (hc : c ^ 2 = 1)
    (h : Even6 K) :
    fixedSliceUValue (c • F) h = fixedSliceUValue F h := by
  rcases sq_eq_one_iff.mp hc with rfl | rfl
  · simp
  · simp [fixedSliceUValue, fixedSliceQNum, fixedSliceQDen,
      LinearMap.smul_apply]
    rw [div_neg]
    ring

/-- The quotient numerator commutes with semilinear Fourier transport. -/
theorem fixedSliceQNum_ringEquiv
    {L : Type*} [Field L]
    (sigma : K ≃+* L)
    {F : Even6 K →ₗ[K] Even6 K}
    {F' : Even6 L →ₗ[L] Even6 L}
    (hintertwine : ∀ x, even6Map sigma (F x) = F' (even6Map sigma x))
    (h : Even6 K) :
    fixedSliceQNum F' (even6Map sigma h) = sigma (fixedSliceQNum F h) := by
  have hF := congrFun (hintertwine h) 0
  change sigma (F h 0) = F' (even6Map sigma h) 0 at hF
  simp [fixedSliceQNum, hF]

/-- The quotient denominator commutes with semilinear Fourier transport. -/
theorem fixedSliceQDen_ringEquiv
    {L : Type*} [Field L]
    (sigma : K ≃+* L)
    {F : Even6 K →ₗ[K] Even6 K}
    {F' : Even6 L →ₗ[L] Even6 L}
    (hintertwine : ∀ x, even6Map sigma (F x) = F' (even6Map sigma x))
    (h : Even6 K) :
    fixedSliceQDen F' (even6Map sigma h) = sigma (fixedSliceQDen F h) := by
  have hF := congrFun (hintertwine h) 0
  change sigma (F h 0) = F' (even6Map sigma h) 0 at hF
  have htwo : sigma (2 : K) = (2 : L) := map_ofNat sigma 2
  calc
    fixedSliceQDen F' (even6Map sigma h) =
        2 * sigma (h 0) * F' (even6Map sigma h) 0 := rfl
    _ = sigma 2 * sigma (h 0) * sigma (F h 0) := by rw [htwo, hF]
    _ = sigma (fixedSliceQDen F h) := by
      simp only [fixedSliceQDen, map_mul]

/-- The affine quotient value is carried to its field conjugate under
semilinear Fourier transport. -/
theorem fixedSliceUValue_ringEquiv
    {L : Type*} [Field L]
    (sigma : K ≃+* L)
    {F : Even6 K →ₗ[K] Even6 K}
    {F' : Even6 L →ₗ[L] Even6 L}
    (hintertwine : ∀ x, even6Map sigma (F x) = F' (even6Map sigma x))
    (h : Even6 K) :
    fixedSliceUValue F' (even6Map sigma h) =
      sigma (fixedSliceUValue F h) := by
  simp only [fixedSliceUValue, fixedSliceQNum_ringEquiv sigma hintertwine,
    fixedSliceQDen_ringEquiv sigma hintertwine, map_div₀, map_pow]

/-- The homogeneous quotient equation is preserved while its parameter is
carried through the field equivalence. -/
theorem fixedSliceUEquation_ringEquiv
    {L : Type*} [Field L]
    (sigma : K ≃+* L)
    {F : Even6 K →ₗ[K] Even6 K}
    {F' : Even6 L →ₗ[L] Even6 L}
    (hintertwine : ∀ x, even6Map sigma (F x) = F' (even6Map sigma x))
    {h : Even6 K} {u : K}
    (hu : fixedSliceUEquation F h u) :
    fixedSliceUEquation F' (even6Map sigma h) (sigma u) := by
  simp only [fixedSliceUEquation, fixedSliceQNum_ringEquiv sigma hintertwine,
    fixedSliceQDen_ringEquiv sigma hintertwine, ← map_pow, ← map_mul]
  exact congrArg sigma hu

/-- Nonvanishing of the common Fourier-coordinate product excludes the
denominator of the quotient invariant. -/
theorem fixedSliceQDen_ne_zero_of_common_ne_zero
    [CharZero K]
    {F : Even6 K →ₗ[K] Even6 K} {h : Even6 K}
    (hc : fourierCoordProduct F h 0 ≠ 0) :
    fixedSliceQDen F h ≠ 0 := by
  simpa [fixedSliceQDen, fourierCoordProduct] using
    mul_ne_zero (by norm_num : (2 : K) ≠ 0) hc

/-- Away from the homogeneous boundary, the quotient equation has the unique
affine solution given by `fixedSliceUValue`. -/
theorem fixedSliceUEquation_iff_eq_value
    {F : Even6 K →ₗ[K] Even6 K} {h : Even6 K} {u : K}
    (hden : fixedSliceQDen F h ≠ 0) :
    fixedSliceUEquation F h u ↔ u = fixedSliceUValue F h := by
  unfold fixedSliceUEquation fixedSliceUValue
  constructor
  · intro hu
    apply (mul_right_cancel₀ (pow_ne_zero 2 hden))
    field_simp [hden] at hu ⊢
    simpa [mul_comm] using hu.symm
  · intro hu
    rw [hu]
    field_simp [hden]

/-- The quotient numerator is homogeneous of degree two. -/
theorem fixedSliceQNum_smul (F : Even6 K →ₗ[K] Even6 K)
    (c : K) (h : Even6 K) :
    fixedSliceQNum F (c • h) = c ^ 2 * fixedSliceQNum F h := by
  simp [fixedSliceQNum, pow_two]
  ring

/-- The quotient denominator is homogeneous of degree two. -/
theorem fixedSliceQDen_smul (F : Even6 K →ₗ[K] Even6 K)
    (c : K) (h : Even6 K) :
    fixedSliceQDen F (c • h) = c ^ 2 * fixedSliceQDen F h := by
  simp [fixedSliceQDen, pow_two]
  ring

/-- Thus the affine quotient value is invariant under nonzero projective
rescaling. -/
theorem fixedSliceUValue_smul
    (F : Even6 K →ₗ[K] Even6 K) {c : K} (hc : c ≠ 0) (h : Even6 K) :
    fixedSliceUValue F (c • h) = fixedSliceUValue F h := by
  rw [fixedSliceUValue, fixedSliceQNum_smul, fixedSliceQDen_smul]
  simp only [fixedSliceUValue]
  field_simp [hc]

/-- q's numerator is Fourier-invariant. -/
theorem fixedSliceQNum_fourier
    {F : Even6 K →ₗ[K] Even6 K}
    (hF2 : ∀ h, F (F h) = h)
    (h : Even6 K) :
    fixedSliceQNum F (F h) = fixedSliceQNum F h := by
  simp [fixedSliceQNum, hF2, add_comm]

/-- q's denominator is Fourier-invariant. -/
theorem fixedSliceQDen_fourier
    {F : Even6 K →ₗ[K] Even6 K}
    (hF2 : ∀ h, F (F h) = h)
    (h : Even6 K) :
    fixedSliceQDen F (F h) = fixedSliceQDen F h := by
  simp [fixedSliceQDen, hF2, mul_comm, mul_left_comm, mul_assoc]

/-- The affine quotient value is invariant under the Fourier involution. -/
theorem fixedSliceUValue_fourier
    {F : Even6 K →ₗ[K] Even6 K}
    (hF2 : ∀ h, F (F h) = h) (h : Even6 K) :
    fixedSliceUValue F (F h) = fixedSliceUValue F h := by
  simp [fixedSliceUValue, fixedSliceQNum_fourier hF2,
    fixedSliceQDen_fourier hF2]

/-- Therefore the quotient u-equation descends through the free Fourier
involution without choosing affine coordinates. -/
theorem fixedSliceUEquation_fourier
    {F : Even6 K →ₗ[K] Even6 K}
    (hF2 : ∀ h, F (F h) = h)
    {h : Even6 K} {u : K}
    (hu : fixedSliceUEquation F h u) :
    fixedSliceUEquation F (F h) u := by
  simpa [fixedSliceUEquation, fixedSliceQNum_fourier hF2,
    fixedSliceQDen_fourier hF2] using hu

end Field

end Biunimodular.F11
