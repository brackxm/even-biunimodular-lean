/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Fourier.ZMod
import Biunimodular.F11.FixedSliceFourierAdapter
import Biunimodular.F11.FixedSliceInvolution
import Biunimodular.F11.FixedSliceQuotientInvariant

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod

noncomputable section

/-!
# The concrete even Fourier lift at p = 11

The intrinsic fixed-slice development uses six coordinates, indexed by the
orbits `{0}, {±1}, ..., {±5}` in `ZMod 11`.  This file constructs the
corresponding linear embedding into the full eleven-coordinate function space
and transports the full discrete Fourier transform back to six coordinates.
-/

/-- The representative in `0, ..., 5` of a class modulo 11, up to sign. -/
def even11Coordinate (x : ZMod 11) : Fin 6 :=
  if h : x.val ≤ 5 then
    ⟨x.val, by omega⟩
  else
    ⟨11 - x.val, by omega⟩

@[simp] theorem even11Coordinate_natCast (i : Fin 6) :
    even11Coordinate (i.1 : ZMod 11) = i := by
  native_decide +revert

@[simp] theorem even11Coordinate_neg (x : ZMod 11) :
    even11Coordinate (-x) = even11Coordinate x := by
  native_decide +revert

@[simp] theorem even11Coordinate_zero :
    even11Coordinate (0 : ZMod 11) = 0 := by
  native_decide

theorem even11Coordinate_cast_eq_or_eq_neg (x : ZMod 11) :
    ((even11Coordinate x).1 : ZMod 11) = x ∨
      ((even11Coordinate x).1 : ZMod 11) = -x := by
  native_decide +revert

/-- Expand six even coordinates to a function on `ZMod 11`. -/
def even11Lift : Even6 ℂ →ₗ[ℂ] (ZMod 11 → ℂ) where
  toFun h x := h (even11Coordinate x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem even11Lift_apply (h : Even6 ℂ) (x : ZMod 11) :
    even11Lift h x = h (even11Coordinate x) := rfl

theorem even11Lift_even (h : Even6 ℂ) : Function.Even (even11Lift h) := by
  intro x
  simp

/-- Coordinatewise field transport commutes with the even-coordinate lift. -/
@[simp] theorem even11Lift_ringEquiv
    (sigma : ℂ ≃+* ℂ) (h : Even6 ℂ) (x : ZMod 11) :
    even11Lift (even6Map sigma h) x = sigma (even11Lift h x) := rfl

/-- Restrict a full function to the representatives `0, ..., 5`. -/
def even11Restrict : (ZMod 11 → ℂ) →ₗ[ℂ] Even6 ℂ where
  toFun f i := f (i.1 : ZMod 11)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem even11Restrict_lift (h : Even6 ℂ) :
    even11Restrict (even11Lift h) = h := by
  funext i
  simp [even11Restrict]

theorem even11Lift_injective : Function.Injective even11Lift := by
  intro h g hfg
  rw [← even11Restrict_lift h, ← even11Restrict_lift g, hfg]

theorem even11Lift_restrict_of_even
    (f : ZMod 11 → ℂ) (hf : Function.Even f) :
    even11Lift (even11Restrict f) = f := by
  funext x
  rcases even11Coordinate_cast_eq_or_eq_neg x with hx | hx
  · simp [even11Lift, even11Restrict, hx]
  · simpa [even11Lift, even11Restrict, hx] using hf x

/-- Dilation of full order-eleven coordinates by a unit. -/
def even11FullDilate (u : (ZMod 11)ˣ) :
    (ZMod 11 → ℂ) →ₗ[ℂ] (ZMod 11 → ℂ) where
  toFun f x := f (u.val * x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem even11FullDilate_apply
    (u : (ZMod 11)ˣ) (f : ZMod 11 → ℂ) (x : ZMod 11) :
    even11FullDilate u f x = f (u.val * x) := rfl

/-- Dilation transported to the six even-coordinate representatives. -/
def even11Dilate (u : (ZMod 11)ˣ) : Even6 ℂ →ₗ[ℂ] Even6 ℂ :=
  even11Restrict.comp ((even11FullDilate u).comp even11Lift)

@[simp] theorem even11Dilate_apply
    (u : (ZMod 11)ˣ) (h : Even6 ℂ) (i : Fin 6) :
    even11Dilate u h i =
      h (even11Coordinate (u.val * (i.1 : ZMod 11))) := rfl

/-- Expanding an even-coordinate dilation agrees with dilating the expanded
full function. -/
theorem even11Lift_dilate (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    even11Lift (even11Dilate u h) = even11FullDilate u (even11Lift h) := by
  change even11Lift
      (even11Restrict (even11FullDilate u (even11Lift h))) =
    even11FullDilate u (even11Lift h)
  apply even11Lift_restrict_of_even
  intro x
  change even11Lift h (u.val * -x) = even11Lift h (u.val * x)
  rw [mul_neg]
  exact even11Lift_even h (u.val * x)

@[simp] theorem even11Dilate_apply_zero
    (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    even11Dilate u h 0 = h 0 := by
  simp only [even11Dilate_apply, Fin.isValue, Fin.val_zero, Nat.cast_zero,
    mul_zero, even11Coordinate_zero]

@[simp] theorem even11Dilate_one (h : Even6 ℂ) :
    even11Dilate 1 h = h := by
  apply even11Lift_injective
  rw [even11Lift_dilate]
  funext x
  simp

theorem even11Dilate_mul
    (u v : (ZMod 11)ˣ) (h : Even6 ℂ) :
    even11Dilate (u * v) h = even11Dilate u (even11Dilate v h) := by
  apply even11Lift_injective
  rw [even11Lift_dilate, even11Lift_dilate, even11Lift_dilate]
  funext x
  change even11Lift h ((u * v).val * x) =
    even11Lift h (v.val * (u.val * x))
  simp only [Units.val_mul]
  rw [← mul_assoc, mul_comm u.val v.val, mul_assoc]

@[simp] theorem even11Dilate_inv_dilate
    (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    even11Dilate u⁻¹ (even11Dilate u h) = h := by
  calc
    even11Dilate u⁻¹ (even11Dilate u h) =
        even11Dilate (u⁻¹ * u) h := (even11Dilate_mul u⁻¹ u h).symm
    _ = h := by simp

@[simp] theorem even11Dilate_dilate_inv
    (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    even11Dilate u (even11Dilate u⁻¹ h) = h := by
  calc
    even11Dilate u (even11Dilate u⁻¹ h) =
        even11Dilate (u * u⁻¹) h := (even11Dilate_mul u u⁻¹ h).symm
    _ = h := by simp

/-- Dilation is a linear equivalence of the six-coordinate even space. -/
noncomputable def even11DilationLinearEquiv (u : (ZMod 11)ˣ) :
    Even6 ℂ ≃ₗ[ℂ] Even6 ℂ where
  toLinearMap := even11Dilate u
  invFun := even11Dilate u⁻¹
  left_inv := even11Dilate_inv_dilate u
  right_inv := even11Dilate_dilate_inv u

@[simp] theorem even11DilationLinearEquiv_apply
    (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    even11DilationLinearEquiv u h = even11Dilate u h := rfl

@[simp] theorem even11DilationLinearEquiv_symm_apply
    (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    (even11DilationLinearEquiv u).symm h = even11Dilate u⁻¹ h := rfl

/-- Squaring is surjective on nonzero order-eleven coordinate dilations after
identifying `x` with `-x`, exactly as in
`(ZMod 11)ˣ / {±1} ≃ C₅`. -/
theorem even11Coordinate_exists_square_dilation
    (u : (ZMod 11)ˣ) :
    ∃ v : (ZMod 11)ˣ, ∀ x : ZMod 11,
      even11Coordinate ((v * v).val * x) =
        even11Coordinate (u.val * x) := by
  native_decide +revert

/-- Consequently every dilation of the even six-coordinate model is the
square of another dilation. -/
theorem even11Dilate_exists_square (u : (ZMod 11)ˣ) :
    ∃ v : (ZMod 11)ˣ, ∀ h : Even6 ℂ,
      even11Dilate v (even11Dilate v h) = even11Dilate u h := by
  obtain ⟨v, hv⟩ := even11Coordinate_exists_square_dilation u
  refine ⟨v, fun h ↦ ?_⟩
  rw [← even11Dilate_mul]
  apply even11Lift_injective
  rw [even11Lift_dilate, even11Lift_dilate]
  funext x
  change h (even11Coordinate ((v * v).val * x)) =
    h (even11Coordinate (u.val * x))
  rw [hv x]

/-- The unnormalised DFT transported to the six even coordinates. -/
def even11Fourier : Even6 ℂ →ₗ[ℂ] Even6 ℂ :=
  even11Restrict.comp
    ((ZMod.dft : (ZMod 11 → ℂ) ≃ₗ[ℂ] (ZMod 11 → ℂ)).toLinearMap.comp even11Lift)

@[simp] theorem even11Fourier_apply (h : Even6 ℂ) (i : Fin 6) :
    even11Fourier h i = ZMod.dft (even11Lift h) (i.1 : ZMod 11) := rfl

theorem even11Lift_fourier (h : Even6 ℂ) :
    even11Lift (even11Fourier h) = ZMod.dft (even11Lift h) := by
  change even11Lift (even11Restrict (ZMod.dft (even11Lift h))) =
    ZMod.dft (even11Lift h)
  apply even11Lift_restrict_of_even
  exact ZMod.dft_even_iff.mpr (even11Lift_even h)

/-- The restricted DFT intertwines dilation by a unit with inverse dilation
on the Fourier side. -/
theorem even11Fourier_dilate (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    even11Fourier (even11Dilate u h) =
      even11Dilate u⁻¹ (even11Fourier h) := by
  apply even11Lift_injective
  rw [even11Lift_fourier, even11Lift_dilate, even11Lift_dilate,
    even11Lift_fourier]
  funext k
  exact ZMod.dft_comp_unitMul (even11Lift h) u k

/-- A field automorphism carrying the standard additive character to its
`u`-dilate carries the full order-eleven DFT to the same output dilation. -/
theorem even11FullFourier_ringEquiv
    (sigma : ℂ ≃+* ℂ) (u : (ZMod 11)ˣ)
    (hchar : ∀ z : ZMod 11,
      sigma (ZMod.stdAddChar z) = ZMod.stdAddChar (u.val * z))
    (f : ZMod 11 → ℂ) (k : ZMod 11) :
    sigma (ZMod.dft f k) =
      ZMod.dft (fun j ↦ sigma (f j)) (u.val * k) := by
  simp only [ZMod.dft_apply, map_sum, map_mul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hchar]
  congr 2
  ring

/-- Restricting the preceding kernel identity to even coordinates gives the
semilinear intertwining law needed for the fixed-slice Galois action. -/
theorem even11Fourier_ringEquiv
    (sigma : ℂ ≃+* ℂ) (u : (ZMod 11)ˣ)
    (hchar : ∀ z : ZMod 11,
      sigma (ZMod.stdAddChar z) = ZMod.stdAddChar (u.val * z))
    (h : Even6 ℂ) :
    even6Map sigma (even11Fourier h) =
      even11Dilate u (even11Fourier (even6Map sigma h)) := by
  funext i
  change sigma (even11Fourier h i) =
    even11Dilate u (even11Fourier (even6Map sigma h)) i
  rw [even11Fourier_apply]
  have hdilate := congrFun
    (even11Lift_dilate u (even11Fourier (even6Map sigma h)))
    (i.1 : ZMod 11)
  rw [even11Lift_fourier] at hdilate
  simp only [even11Lift_apply, even11Coordinate_natCast,
    even11FullDilate_apply] at hdilate
  rw [hdilate]
  have hmap : (fun j ↦ sigma (even11Lift h j)) =
      even11Lift (even6Map sigma h) := by
    funext j
    rfl
  simpa only [hmap] using
    even11FullFourier_ringEquiv sigma u hchar (even11Lift h)
      (i.1 : ZMod 11)

/-- The unnormalised even DFT squares to multiplication by 11. -/
theorem even11Fourier_sq (h : Even6 ℂ) :
    even11Fourier (even11Fourier h) = (11 : ℂ) • h := by
  apply even11Lift_injective
  rw [even11Lift_fourier, even11Lift_fourier, ZMod.dft_dft]
  funext x
  simp

/-- The normalized six-coordinate Fourier operator. -/
def even11FourierNormalized : Even6 ℂ →ₗ[ℂ] Even6 ℂ :=
  ((Real.sqrt 11 : ℂ)⁻¹) • even11Fourier

/-- The scalar discrepancy produced when a field automorphism is applied to
the chosen square-root normalization. -/
def even11NormalizationTwist (sigma : ℂ ≃+* ℂ) : ℂ :=
  (sigma (Real.sqrt 11 : ℂ))⁻¹ * (Real.sqrt 11 : ℂ)

theorem even11NormalizationTwist_ne_zero (sigma : ℂ ≃+* ℂ) :
    even11NormalizationTwist sigma ≠ 0 := by
  have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 11)).ne'
  have hsigma : sigma (Real.sqrt 11 : ℂ) ≠ 0 := by
    intro hzero
    apply hs
    apply sigma.injective
    rw [map_zero]
    exact hzero
  exact mul_ne_zero (inv_ne_zero hsigma) hs

/-- Every field automorphism can only change the normalized order-eleven DFT
by a sign: the normalization discrepancy has square one. -/
theorem even11NormalizationTwist_sq (sigma : ℂ ≃+* ℂ) :
    even11NormalizationTwist sigma ^ 2 = 1 := by
  let s : ℂ := Real.sqrt 11
  have hs : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 11)).ne'
  have hs2 : s * s = 11 := by
    dsimp [s]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 11)
  have hsigma : sigma s ≠ 0 := by
    intro hzero
    apply hs
    apply sigma.injective
    rw [map_zero]
    exact hzero
  have hsigma2 : sigma s * sigma s = s * s := by
    calc
      sigma s * sigma s = sigma (s * s) := (map_mul sigma s s).symm
      _ = sigma 11 := by rw [hs2]
      _ = 11 := map_ofNat sigma 11
      _ = s * s := hs2.symm
  change ((sigma s)⁻¹ * s) ^ 2 = 1
  field_simp [hsigma]
  simpa [pow_two] using hsigma2.symm

/-- The normalized and unnormalised operators define the same projective
fixed slice. -/
theorem even11_fixedSliceEq_normalized_iff (h : Even6 ℂ) :
    FixedSliceEq even11FourierNormalized h ↔ FixedSliceEq even11Fourier h := by
  have hsR : Real.sqrt 11 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by exact_mod_cast hsR
  exact fixedSliceEq_smul_iff (inv_ne_zero hs) h

/-- The normalized even Fourier operator is an actual involution. -/
theorem even11FourierNormalized_sq (h : Even6 ℂ) :
    even11FourierNormalized (even11FourierNormalized h) = h := by
  have hsR : Real.sqrt 11 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by exact_mod_cast hsR
  have hs2R : Real.sqrt 11 * Real.sqrt 11 = 11 :=
    Real.mul_self_sqrt (by norm_num)
  have hs2 : (Real.sqrt 11 : ℂ) * (Real.sqrt 11 : ℂ) = 11 := by
    exact_mod_cast hs2R
  have hcoef :
      (Real.sqrt 11 : ℂ)⁻¹ * (Real.sqrt 11 : ℂ)⁻¹ * 11 = 1 := by
    field_simp
    simpa [pow_two] using hs2.symm
  change (Real.sqrt 11 : ℂ)⁻¹ •
      even11Fourier ((Real.sqrt 11 : ℂ)⁻¹ • even11Fourier h) = h
  rw [even11Fourier.map_smul, even11Fourier_sq]
  simp only [smul_smul]
  rw [← mul_assoc, hcoef, one_smul]

/-- The normalized restricted DFT has the same inverse-dilation
intertwining law. -/
theorem even11FourierNormalized_dilate
    (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    even11FourierNormalized (even11Dilate u h) =
      even11Dilate u⁻¹ (even11FourierNormalized h) := by
  change (Real.sqrt 11 : ℂ)⁻¹ •
      even11Fourier (even11Dilate u h) =
    even11Dilate u⁻¹ ((Real.sqrt 11 : ℂ)⁻¹ • even11Fourier h)
  rw [even11Fourier_dilate, LinearMap.map_smul]

/-- The normalized semilinear intertwining law.  The only additional factor
is `even11NormalizationTwist`, whose square is one. -/
theorem even11FourierNormalized_ringEquiv
    (sigma : ℂ ≃+* ℂ) (u : (ZMod 11)ˣ)
    (hchar : ∀ z : ZMod 11,
      sigma (ZMod.stdAddChar z) = ZMod.stdAddChar (u.val * z))
    (h : Even6 ℂ) :
    even6Map sigma (even11FourierNormalized h) =
      even11NormalizationTwist sigma •
        even11Dilate u
          (even11FourierNormalized (even6Map sigma h)) := by
  have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 11)).ne'
  funext i
  have hF := congrFun (even11Fourier_ringEquiv sigma u hchar h) i
  change sigma (even11Fourier h i) =
    even11Dilate u (even11Fourier (even6Map sigma h)) i at hF
  have hsigma : sigma (Real.sqrt 11 : ℂ) ≠ 0 := by
    intro hzero
    apply hs
    apply sigma.injective
    rw [map_zero]
    exact hzero
  change sigma ((Real.sqrt 11 : ℂ)⁻¹ * even11Fourier h i) =
    even11NormalizationTwist sigma *
      even11Dilate u
        ((Real.sqrt 11 : ℂ)⁻¹ • even11Fourier (even6Map sigma h)) i
  simp only [map_mul, LinearMap.map_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [map_inv₀, hF]
  simp only [even11NormalizationTwist]
  field_simp [hs, hsigma]

/-- Applying such an automorphism to a normalized fixed-slice vector gives a
fixed-slice vector for the Fourier operator twisted by the induced output
dilation.  The harmless normalization sign has been removed projectively. -/
theorem even11_fixedSliceEq_ringEquiv_twisted
    (sigma : ℂ ≃+* ℂ) (u : (ZMod 11)ˣ)
    (hchar : ∀ z : ZMod 11,
      sigma (ZMod.stdAddChar z) = ZMod.stdAddChar (u.val * z))
    {h : Even6 ℂ} (hh : FixedSliceEq even11FourierNormalized h) :
    FixedSliceEq
      ((even11Dilate u).comp even11FourierNormalized)
      (even6Map sigma h) := by
  let Ftwist : Even6 ℂ →ₗ[ℂ] Even6 ℂ :=
    (even11Dilate u).comp even11FourierNormalized
  have hintertwine : ∀ x : Even6 ℂ,
      even6Map sigma (even11FourierNormalized x) =
        (even11NormalizationTwist sigma • Ftwist) (even6Map sigma x) := by
    intro x
    simpa [Ftwist] using even11FourierNormalized_ringEquiv sigma u hchar x
  have htransport : FixedSliceEq
      (even11NormalizationTwist sigma • Ftwist)
      (even6Map sigma h) :=
    fixedSliceEq_ringEquiv sigma hintertwine hh
  exact (fixedSliceEq_smul_iff
    (even11NormalizationTwist_ne_zero sigma) (even6Map sigma h)).mp
      htransport

/-- The same semilinear transport carries the squared quotient invariant to
its field conjugate; the normalization sign disappears because it squares to
one. -/
theorem even11_fixedSliceUValue_ringEquiv_twisted
    (sigma : ℂ ≃+* ℂ) (u : (ZMod 11)ˣ)
    (hchar : ∀ z : ZMod 11,
      sigma (ZMod.stdAddChar z) = ZMod.stdAddChar (u.val * z))
    (h : Even6 ℂ) :
    fixedSliceUValue
        ((even11Dilate u).comp even11FourierNormalized)
        (even6Map sigma h) =
      sigma (fixedSliceUValue even11FourierNormalized h) := by
  let Ftwist : Even6 ℂ →ₗ[ℂ] Even6 ℂ :=
    (even11Dilate u).comp even11FourierNormalized
  have hintertwine : ∀ x : Even6 ℂ,
      even6Map sigma (even11FourierNormalized x) =
        (even11NormalizationTwist sigma • Ftwist) (even6Map sigma x) := by
    intro x
    simpa [Ftwist] using even11FourierNormalized_ringEquiv sigma u hchar x
  have htransport :=
    fixedSliceUValue_ringEquiv sigma hintertwine h
  rw [fixedSliceUValue_smul_operator_of_sq_eq_one
    (even11NormalizationTwist_sq sigma)] at htransport
  exact htransport

/-- If `v²` induces the output dilation `u`, inverse dilation by `v`
converts a twisted fixed-slice vector back into an ordinary one. -/
theorem even11_fixedSliceEq_compensate_dilation
    (u v : (ZMod 11)ˣ)
    (hsquare : ∀ x : Even6 ℂ,
      even11Dilate v (even11Dilate v x) = even11Dilate u x)
    {g : Even6 ℂ}
    (hg : FixedSliceEq
      ((even11Dilate u).comp even11FourierNormalized) g) :
    FixedSliceEq even11FourierNormalized (even11Dilate v⁻¹ g) := by
  have hfourier :
      even11FourierNormalized (even11Dilate v⁻¹ g) =
        even11Dilate v (even11FourierNormalized g) := by
    simpa using even11FourierNormalized_dilate v⁻¹ g
  have hproduct (j : Fin 6) :
      fourierCoordProduct even11FourierNormalized
          (even11Dilate v⁻¹ g) j =
        fourierCoordProduct
          ((even11Dilate u).comp even11FourierNormalized) g
          (even11Coordinate (v⁻¹.val * (j.1 : ZMod 11))) := by
    let k : Fin 6 := even11Coordinate (v⁻¹.val * (j.1 : ZMod 11))
    have hcoord : even11Dilate v⁻¹ g j = g k := rfl
    have hstep := congrFun
      (even11Dilate_inv_dilate v
        (even11Dilate v (even11FourierNormalized g))) j
    change even11Dilate v
        (even11Dilate v (even11FourierNormalized g)) k =
      even11Dilate v (even11FourierNormalized g) j at hstep
    rw [hsquare] at hstep
    simp only [fourierCoordProduct, LinearMap.comp_apply]
    rw [hfourier, hcoord, hstep]
  intro j
  calc
    fourierCoordProduct even11FourierNormalized
        (even11Dilate v⁻¹ g) j =
      fourierCoordProduct
        ((even11Dilate u).comp even11FourierNormalized) g
        (even11Coordinate (v⁻¹.val * (j.1 : ZMod 11))) := hproduct j
    _ = fourierCoordProduct
        ((even11Dilate u).comp even11FourierNormalized) g 0 := hg _
    _ = fourierCoordProduct even11FourierNormalized
        (even11Dilate v⁻¹ g) 0 := by
      simpa using (hproduct 0).symm

/-- Compensation does not alter the quotient invariant: every dilation fixes
the zero input and output coordinates from which `u` is formed. -/
theorem even11_fixedSliceUValue_compensate_dilation
    (u v : (ZMod 11)ˣ) (g : Even6 ℂ) :
    fixedSliceUValue even11FourierNormalized (even11Dilate v⁻¹ g) =
      fixedSliceUValue
        ((even11Dilate u).comp even11FourierNormalized) g := by
  have hfourier :
      even11FourierNormalized (even11Dilate v⁻¹ g) =
        even11Dilate v (even11FourierNormalized g) := by
    simpa using even11FourierNormalized_dilate v⁻¹ g
  have hfourierZero :
      even11FourierNormalized (even11Dilate v⁻¹ g) 0 =
        even11FourierNormalized g 0 := by
    rw [hfourier, even11Dilate_apply_zero]
  simp [fixedSliceUValue, fixedSliceQNum, fixedSliceQDen,
    hfourierZero, LinearMap.comp_apply]

/-- Complete geometric semilinear transport.  A nonzero fixed-slice vector
is sent to another nonzero vector in the original fixed slice whose quotient
invariant is the prescribed field conjugate. -/
theorem even11_fixedSlice_semilinear_transport
    (sigma : ℂ ≃+* ℂ) (u : (ZMod 11)ˣ)
    (hchar : ∀ z : ZMod 11,
      sigma (ZMod.stdAddChar z) = ZMod.stdAddChar (u.val * z))
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hh : FixedSliceEq even11FourierNormalized h) :
    ∃ h' : Even6 ℂ,
      h' ≠ 0 ∧
      FixedSliceEq even11FourierNormalized h' ∧
      fixedSliceUValue even11FourierNormalized h' =
        sigma (fixedSliceUValue even11FourierNormalized h) := by
  obtain ⟨v, hv⟩ := even11Dilate_exists_square u
  let g : Even6 ℂ := even6Map sigma h
  refine ⟨even11Dilate v⁻¹ g, ?_, ?_, ?_⟩
  · have hg : g ≠ 0 := by
      simpa [g] using (even6Map_injective sigma).ne hnz
    intro hzero
    apply hg
    have := congrArg (even11Dilate v) hzero
    simpa [g] using this
  · apply even11_fixedSliceEq_compensate_dilation u v hv
    exact even11_fixedSliceEq_ringEquiv_twisted sigma u hchar hh
  · rw [even11_fixedSliceUValue_compensate_dilation u v]
    exact even11_fixedSliceUValue_ringEquiv_twisted sigma u hchar h

/-- The compensating coordinate dilation fixes the concrete homogeneous
quotient invariant.  Only the zero coordinates of `h` and its normalized DFT
enter `u`, and both are unchanged by the inverse-dilation intertwining law. -/
theorem even11_fixedSliceUValue_dilate
    (u : (ZMod 11)ˣ) (h : Even6 ℂ) :
    fixedSliceUValue even11FourierNormalized (even11Dilate u h) =
      fixedSliceUValue even11FourierNormalized h := by
  have hfourierZero :
      even11FourierNormalized (even11Dilate u h) 0 =
        even11FourierNormalized h 0 := by
    rw [even11FourierNormalized_dilate, even11Dilate_apply_zero]
  simp [fixedSliceUValue, fixedSliceQNum, fixedSliceQDen, hfourierZero]

/-- The corresponding normalized full DFT on eleven coordinates. -/
def even11FullFourierNormalized :
    (ZMod 11 → ℂ) →ₗ[ℂ] (ZMod 11 → ℂ) :=
  ((Real.sqrt 11 : ℂ)⁻¹) •
    (ZMod.dft : (ZMod 11 → ℂ) ≃ₗ[ℂ] (ZMod 11 → ℂ)).toLinearMap

/-- The even-coordinate lift also intertwines the normalized transforms. -/
theorem even11Lift_fourierNormalized (h : Even6 ℂ) :
    even11Lift (even11FourierNormalized h) =
      even11FullFourierNormalized (even11Lift h) := by
  simp [even11FourierNormalized, even11FullFourierNormalized,
    even11Lift_fourier]

/-- Concrete normalized instance of the abstract Fourier lift. -/
def even11FourierNormalizedLift :
    EvenFourierLift even11FourierNormalized even11FullFourierNormalized where
  lift := even11Lift
  lift_injective := even11Lift_injective
  coord_of_full := even11Coordinate
  lift_apply := even11Lift_apply
  intertwine := even11Lift_fourierNormalized

/-- The concrete order-11 Fourier operator preserves the projective fixed
slice. -/
theorem even11_fixedSliceEq_fourier {h : Even6 ℂ}
    (hh : FixedSliceEq even11Fourier h) :
    FixedSliceEq even11Fourier (even11Fourier h) :=
  fixedSliceEq_fourier_of_sq_smul even11Fourier_sq hh

/-- The normalized concrete Fourier operator preserves the same fixed-slice
equations and acts involutively. -/
theorem even11_normalized_fixedSliceEq_fourier {h : Even6 ℂ}
    (hh : FixedSliceEq even11FourierNormalized h) :
    FixedSliceEq even11FourierNormalized (even11FourierNormalized h) :=
  fixedSliceEq_fourier even11FourierNormalized_sq hh

/-- The concrete normalized Fourier action preserves the homogeneous quotient
invariant equation. -/
theorem even11_fixedSliceUEquation_fourier
    {h : Even6 ℂ} {u : ℂ}
    (hu : fixedSliceUEquation even11FourierNormalized h u) :
    fixedSliceUEquation even11FourierNormalized
      (even11FourierNormalized h) u :=
  fixedSliceUEquation_fourier even11FourierNormalized_sq hu

/-- Concrete instance of the abstract six-to-eleven-coordinate Fourier lift. -/
def even11FourierLift :
    EvenFourierLift even11Fourier
      (ZMod.dft : (ZMod 11 → ℂ) ≃ₗ[ℂ] (ZMod 11 → ℂ)).toLinearMap where
  lift := even11Lift
  lift_injective := even11Lift_injective
  coord_of_full := even11Coordinate
  lift_apply := even11Lift_apply
  intertwine := even11Lift_fourier

/-- The remaining full-support uncertainty statement descends to the concrete
six-coordinate order-11 Fourier operator. -/
theorem even11_noDisjointFourierSupport
    (hu : FullNoDisjointFourierSupport
      (ZMod.dft : (ZMod 11 → ℂ) ≃ₗ[ℂ] (ZMod 11 → ℂ)).toLinearMap) :
    NoDisjointFourierSupport even11Fourier :=
  noDisjointFourierSupport_of_full even11FourierLift hu

/-- The normalized full-support statement descends through the normalized
lift as well. -/
theorem even11_normalized_noDisjointFourierSupport
    (hu : FullNoDisjointFourierSupport even11FullFourierNormalized) :
    NoDisjointFourierSupport even11FourierNormalized :=
  noDisjointFourierSupport_of_full even11FourierNormalizedLift hu

/-- Consequently the concrete order-11 fixed slice has no projective boundary
once the full prime-support uncertainty input is supplied. -/
theorem even11_fixedSlice_common_ne_zero
    (hu : FullNoDisjointFourierSupport
      (ZMod.dft : (ZMod 11 → ℂ) ≃ₗ[ℂ] (ZMod 11 → ℂ)).toLinearMap)
    {h : Even6 ℂ} (hnz : h ≠ 0) (hh : FixedSliceEq even11Fourier h) :
    fourierCoordProduct even11Fourier h 0 ≠ 0 :=
  fixedSlice_common_ne_zero_of_full_uncertainty even11FourierLift hu hnz hh

/-- Normalized form of the concrete no-boundary endpoint used by the quotient
invariant development. -/
theorem even11_normalized_fixedSlice_common_ne_zero
    (hu : FullNoDisjointFourierSupport even11FullFourierNormalized)
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hh : FixedSliceEq even11FourierNormalized h) :
    fourierCoordProduct even11FourierNormalized h 0 ≠ 0 :=
  fixedSlice_common_ne_zero_of_full_uncertainty
    even11FourierNormalizedLift hu hnz hh

end

end Biunimodular.F11
