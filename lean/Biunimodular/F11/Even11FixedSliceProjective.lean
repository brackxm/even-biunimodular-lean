/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Biunimodular.F11.Even11FourierLift

set_option autoImplicit false

namespace Biunimodular.F11

open scoped LinearAlgebra.Projectivization

noncomputable section

/-!
# The concrete projective fixed slice at p = 11

This file turns the homogeneous vector equations `FixedSliceEq` into an
honest predicate on projective five-space.  It also lifts the normalized even
Fourier involution to projective space and then restricts it to the concrete
fixed-slice subtype.
-/

/-- Projective five-space of nonzero even six-coordinate vectors. -/
abbrev Even11ProjectiveSpace := ℙ ℂ (Even6 ℂ)

/-- The homogeneous fixed-slice predicate descended to projective space. -/
def even11ProjectiveFixedSlice : Even11ProjectiveSpace → Prop :=
  Projectivization.lift
    (fun h : {h : Even6 ℂ // h ≠ 0} =>
      FixedSliceEq even11FourierNormalized h.1)
    (by
      intro a b c hab
      have hc : c ≠ 0 := by
        intro hc
        apply a.2
        rw [hab, hc, zero_smul]
      apply propext
      rw [hab]
      exact fixedSliceEq_smul_vector_iff hc b.1)

@[simp] theorem even11ProjectiveFixedSlice_mk
    (h : Even6 ℂ) (hnz : h ≠ 0) :
    even11ProjectiveFixedSlice (Projectivization.mk ℂ h hnz) ↔
      FixedSliceEq even11FourierNormalized h := by
  rfl

/-- The concrete projective fixed-slice point type. -/
abbrev Even11FixedSlicePoint :=
  {p : Even11ProjectiveSpace // even11ProjectiveFixedSlice p}

/-- The normalized Fourier operator is injective, as follows directly from
its involutivity. -/
theorem even11FourierNormalized_injective :
    Function.Injective even11FourierNormalized := by
  intro h k hhk
  rw [← even11FourierNormalized_sq h, ← even11FourierNormalized_sq k, hhk]

/-- The normalized Fourier involution induced on projective five-space. -/
def even11ProjectiveFourier :
    Even11ProjectiveSpace → Even11ProjectiveSpace :=
  Projectivization.map even11FourierNormalized
    even11FourierNormalized_injective

@[simp] theorem even11ProjectiveFourier_mk
    (h : Even6 ℂ) (hnz : h ≠ 0) :
    even11ProjectiveFourier (Projectivization.mk ℂ h hnz) =
      Projectivization.mk ℂ (even11FourierNormalized h)
        (by simpa using even11FourierNormalized_injective.ne hnz) := by
  rfl

/-- The induced projective Fourier map is an involution. -/
@[simp] theorem even11ProjectiveFourier_sq
    (p : Even11ProjectiveSpace) :
    even11ProjectiveFourier (even11ProjectiveFourier p) = p := by
  induction p using Projectivization.ind with
  | h h hnz =>
      simp only [even11ProjectiveFourier_mk]
      simp only [even11FourierNormalized_sq]

/-- Projective Fourier preserves the fixed-slice predicate. -/
theorem even11ProjectiveFixedSlice_fourier
    {p : Even11ProjectiveSpace} (hp : even11ProjectiveFixedSlice p) :
    even11ProjectiveFixedSlice (even11ProjectiveFourier p) := by
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveFourier_mk,
        even11ProjectiveFixedSlice_mk] at ⊢
      exact even11_normalized_fixedSliceEq_fourier hp

/-- Fourier membership is equivalent to membership because the projective
map is involutive. -/
theorem even11ProjectiveFixedSlice_fourier_iff
    (p : Even11ProjectiveSpace) :
    even11ProjectiveFixedSlice (even11ProjectiveFourier p) ↔
      even11ProjectiveFixedSlice p := by
  constructor
  · intro hp
    have := even11ProjectiveFixedSlice_fourier hp
    simpa only [even11ProjectiveFourier_sq] using this
  · exact even11ProjectiveFixedSlice_fourier

/-- The normalized Fourier involution restricted to the concrete fixed
slice. -/
def even11FixedSliceFourier :
    Even11FixedSlicePoint ≃ Even11FixedSlicePoint where
  toFun p := ⟨even11ProjectiveFourier p.1,
    even11ProjectiveFixedSlice_fourier p.2⟩
  invFun p := ⟨even11ProjectiveFourier p.1,
    even11ProjectiveFixedSlice_fourier p.2⟩
  left_inv p := by
    apply Subtype.ext
    exact even11ProjectiveFourier_sq p.1
  right_inv p := by
    apply Subtype.ext
    exact even11ProjectiveFourier_sq p.1

@[simp] theorem even11FixedSliceFourier_apply_coe
    (p : Even11FixedSlicePoint) :
    (even11FixedSliceFourier p).1 = even11ProjectiveFourier p.1 := rfl

@[simp] theorem even11FixedSliceFourier_sq
    (p : Even11FixedSlicePoint) :
    even11FixedSliceFourier (even11FixedSliceFourier p) = p := by
  exact even11FixedSliceFourier.left_inv p

end

end Biunimodular.F11
