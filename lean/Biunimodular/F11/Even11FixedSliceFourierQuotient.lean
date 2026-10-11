/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Ring.BooleanRing
import Biunimodular.F11.Even11FixedSliceProjective
import Biunimodular.F11.Even11PrincipalMinorCertificate

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod
open scoped LinearAlgebra.Projectivization

noncomputable section

/-!
# The free Fourier quotient of the concrete F11 fixed slice

The normalized Fourier involution has no fixed point on the projective fixed
slice.  It therefore defines a free `Bool`-action and a canonical two-sheeted
orbit quotient.
-/

/-- Lookup table for the six even-coordinate orbits in their natural
`0, ..., 10` order. -/
def even11CoordinateTable : Fin 11 → Fin 6 :=
  ![0, 1, 2, 3, 4, 5, 5, 4, 3, 2, 1]

@[simp] theorem even11Coordinate_eq_table (x : Fin 11) :
    even11Coordinate x = even11CoordinateTable x := by
  fin_cases x <;> native_decide

/-- At frequency zero, the even order-11 Fourier transform is the weighted
sum of the six orbit coordinates. -/
theorem even11Fourier_zero (h : Even6 ℂ) :
    even11Fourier h 0 =
      h 0 + 2 * (h 1 + h 2 + h 3 + h 4 + h 5) := by
  rw [even11Fourier_apply]
  change ZMod.dft (even11Lift h) 0 = _
  rw [ZMod.dft_apply_zero]
  change (∑ x : Fin 11, h (even11Coordinate x)) = _
  simp [even11CoordinateTable, Fin.sum_univ_succ]
  ring

/-- No nonzero vector on the concrete fixed slice is a projective Fourier
eigenvector.  The fixed-slice equations force all six coordinate squares to
agree.  The zero-frequency equation would then make an odd integer square
equal to `11`, which is impossible. -/
theorem even11_normalized_fixedSlice_not_eigen
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hh : FixedSliceEq even11FourierNormalized h)
    {a : ℂ} (heigen : even11FourierNormalized h = a • h) : False := by
  have hcommon : fourierCoordProduct even11FourierNormalized h 0 ≠ 0 :=
    even11_normalized_fixedSlice_common_ne_zero_certified hnz hh
  have hzero : h 0 ≠ 0 := fixedSlice_all_h_nonzero hh hcommon 0
  have ha2 : a * a = 1 := by
    have hsq := congrFun (even11FourierNormalized_sq h) 0
    rw [heigen] at hsq
    simp only [LinearMap.map_smul, heigen, Pi.smul_apply, smul_eq_mul] at hsq
    apply mul_right_cancel₀ hzero
    calc
      (a * a) * h 0 = a * (a * h 0) := by ring
      _ = h 0 := hsq
      _ = 1 * h 0 := by simp
  have ha : a ≠ 0 := by
    intro ha
    rw [ha] at ha2
    norm_num at ha2
  have hcoordSq (j : Fin 6) : h j * h j = h 0 * h 0 := by
    have hp := hh j
    simp only [fourierCoordProduct, heigen, Pi.smul_apply, smul_eq_mul] at hp
    apply mul_left_cancel₀ ha
    calc
      a * (h j * h j) = h j * (a * h j) := by ring
      _ = h 0 * (a * h 0) := hp
      _ = a * (h 0 * h 0) := by ring
  have hsign (j : Fin 6) : h j = h 0 ∨ h j = -h 0 :=
    mul_self_eq_mul_self_iff.mp (hcoordSq j)
  have hsqrt : (Real.sqrt 11 : ℂ) * (Real.sqrt 11 : ℂ) = 11 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 11)
  have hsqrt_ne : (Real.sqrt 11 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 11)).ne'
  have hfrequency := congrFun heigen 0
  change (Real.sqrt 11 : ℂ)⁻¹ * even11Fourier h 0 = a * h 0 at hfrequency
  rw [even11Fourier_zero] at hfrequency
  have hsum :
      h 0 + 2 * (h 1 + h 2 + h 3 + h 4 + h 5) =
        (Real.sqrt 11 : ℂ) * a * h 0 := by
    calc
      h 0 + 2 * (h 1 + h 2 + h 3 + h 4 + h 5) =
          (Real.sqrt 11 : ℂ) *
            ((Real.sqrt 11 : ℂ)⁻¹ *
              (h 0 + 2 * (h 1 + h 2 + h 3 + h 4 + h 5))) := by
                field_simp
      _ = (Real.sqrt 11 : ℂ) * (a * h 0) := by rw [hfrequency]
      _ = (Real.sqrt 11 : ℂ) * a * h 0 := by ring
  have hratio :
      (h 0 + 2 * (h 1 + h 2 + h 3 + h 4 + h 5)) * (h 0)⁻¹ =
        (Real.sqrt 11 : ℂ) * a := by
    rw [hsum]
    field_simp
  have hsqrtA : ((Real.sqrt 11 : ℂ) * a) ^ 2 = 11 := by
    rw [pow_two]
    calc
      (Real.sqrt 11 : ℂ) * a * ((Real.sqrt 11 : ℂ) * a) =
          ((Real.sqrt 11 : ℂ) * (Real.sqrt 11 : ℂ)) * (a * a) := by ring
      _ = 11 := by rw [hsqrt, ha2]; norm_num
  rcases hsign 1 with h1 | h1 <;>
    rcases hsign 2 with h2 | h2 <;>
    rcases hsign 3 with h3 | h3 <;>
    rcases hsign 4 with h4 | h4 <;>
    rcases hsign 5 with h5 | h5 <;>
    simp only [h1, h2, h3, h4, h5] at hratio <;>
    ring_nf at hratio <;>
    simp [hzero] at hratio <;>
    have hratioSq := congrArg (fun z : ℂ => z ^ 2) hratio <;>
    rw [hsqrtA] at hratioSq <;>
    norm_num at hratioSq

/-- The projective Fourier involution has no fixed point on the concrete
fixed-slice locus. -/
theorem even11ProjectiveFourier_ne_of_fixedSlice
    {p : Even11ProjectiveSpace} (hp : even11ProjectiveFixedSlice p) :
    even11ProjectiveFourier p ≠ p := by
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveFixedSlice_mk] at hp
      intro hfixed
      rw [even11ProjectiveFourier_mk,
        Projectivization.mk_eq_mk_iff'] at hfixed
      rcases hfixed with ⟨a, ha⟩
      exact even11_normalized_fixedSlice_not_eigen hnz hp ha.symm

@[simp] theorem even11FixedSliceFourier_ne
    (p : Even11FixedSlicePoint) : even11FixedSliceFourier p ≠ p := by
  intro hp
  apply even11ProjectiveFourier_ne_of_fixedSlice p.2
  exact congrArg Subtype.val hp

/-- The additive Boolean group acts by the identity and the Fourier
involution. -/
def even11FixedSliceVAdd (b : Bool) (p : Even11FixedSlicePoint) :
    Even11FixedSlicePoint :=
  bif b then even11FixedSliceFourier p else p

instance : VAdd Bool Even11FixedSlicePoint :=
  ⟨even11FixedSliceVAdd⟩

@[simp] theorem false_vadd_even11FixedSlicePoint
    (p : Even11FixedSlicePoint) : false +ᵥ p = p := rfl

@[simp] theorem true_vadd_even11FixedSlicePoint
    (p : Even11FixedSlicePoint) : true +ᵥ p = even11FixedSliceFourier p := rfl

instance : AddAction Bool Even11FixedSlicePoint where
  zero_vadd p := by rfl
  add_vadd b c p := by
    cases b <;> cases c <;> simp [Bool.add_eq_xor]

/-- The Boolean Fourier action is free. -/
instance : IsCancelVAdd Bool Even11FixedSlicePoint where
  right_cancel' b c p hbc := by
    cases b <;> cases c
    · rfl
    · change p = even11FixedSliceFourier p at hbc
      exact (even11FixedSliceFourier_ne p hbc.symm).elim
    · change even11FixedSliceFourier p = p at hbc
      exact (even11FixedSliceFourier_ne p hbc).elim
    · rfl

/-- The orbit space of the free projective Fourier involution. -/
abbrev Even11FixedSliceFourierQuotient :=
  AddAction.orbitRel.Quotient Bool Even11FixedSlicePoint

/-- Fourier-related fixed-slice points have the same quotient class. -/
@[simp] theorem even11FixedSliceFourier_quotient_mk
    (p : Even11FixedSlicePoint) :
    (Quotient.mk'' (even11FixedSliceFourier p) :
      Even11FixedSliceFourierQuotient) = Quotient.mk'' p := by
  simpa using
    (AddAction.orbitRel.Quotient.quotient_vadd_eq
      (g := true) (a := p))

/-- The free Fourier quotient gives a canonical two-sheet decomposition of
the concrete fixed slice. -/
noncomputable def even11FixedSliceTwoSheeted :
    Even11FixedSlicePoint ≃ Even11FixedSliceFourierQuotient × Bool :=
  AddAction.selfEquivOrbitsQuotientProd
    (fun p => IsCancelVAdd.stabilizer_eq_bot p)

end

end Biunimodular.F11
