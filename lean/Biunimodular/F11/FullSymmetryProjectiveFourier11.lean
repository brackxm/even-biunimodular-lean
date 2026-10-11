/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectiveWeyl11
import Biunimodular.F11.Even11FixedSliceQuotientGeometry
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false

namespace Biunimodular.F11

open scoped LinearAlgebra.Projectivization
open scoped ComplexConjugate

noncomputable section

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- Coordinate reflection `x ↦ -x` on the full signal space. -/
def fullReflectionLinear11 :
    FullSignalSpace11 ≃ₗ[ℂ] FullSignalSpace11 where
  toFun f x := f (-x)
  invFun f x := f (-x)
  left_inv f := by funext x; simp
  right_inv f := by funext x; simp
  map_add' f g := by funext x; rfl
  map_smul' c f := by funext x; rfl

def fullProjectiveReflection11 :
    FullProjectiveSignal11 → FullProjectiveSignal11 :=
  Projectivization.map fullReflectionLinear11.toLinearMap
    fullReflectionLinear11.injective

@[simp] theorem fullProjectiveReflection11_mk
    (f : FullSignalSpace11) (hf : f ≠ 0) :
    fullProjectiveReflection11 (Projectivization.mk ℂ f hf) =
      Projectivization.mk ℂ (fullReflectionLinear11 f)
        (by simpa using fullReflectionLinear11.injective.ne hf) := rfl

/-- The actual (unnormalized) length-eleven DFT on projective signals. -/
def fullProjectiveFourier11 :
    FullProjectiveSignal11 → FullProjectiveSignal11 :=
  Projectivization.map
    (ZMod.dft : FullSignalSpace11 ≃ₗ[ℂ] FullSignalSpace11).toLinearMap
    (ZMod.dft : FullSignalSpace11 ≃ₗ[ℂ] FullSignalSpace11).injective

@[simp] theorem fullProjectiveFourier11_mk
    (f : FullSignalSpace11) (hf : f ≠ 0) :
    fullProjectiveFourier11 (Projectivization.mk ℂ f hf) =
      Projectivization.mk ℂ (ZMod.dft f)
        (by simpa using
          (ZMod.dft : FullSignalSpace11 ≃ₗ[ℂ] FullSignalSpace11).injective.ne hf) :=
  rfl

/-- Fourier squared is reflection on complex projective ten-space. -/
theorem fullProjectiveFourier11_sq (p : FullProjectiveSignal11) :
    fullProjectiveFourier11 (fullProjectiveFourier11 p) =
      fullProjectiveReflection11 p := by
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveFourier11_mk,
        fullProjectiveReflection11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨(11 : ℂ), ?_⟩
      funext x
      simpa [fullReflectionLinear11, Pi.smul_apply] using
        (congrFun (ZMod.dft_dft f) x).symm

/-- Coordinatewise complex conjugation descends to projective signals. -/
def fullConjSignal11 (f : FullSignalSpace11) : FullSignalSpace11 :=
  fun x => conj (f x)

theorem fullConjSignal11_ne_zero {f : FullSignalSpace11} (hf : f ≠ 0) :
    fullConjSignal11 f ≠ 0 := by
  intro hz
  apply hf
  funext x
  have hx := congrFun hz x
  simpa [fullConjSignal11] using congrArg conj hx

def fullProjectiveConj11 :
    FullProjectiveSignal11 → FullProjectiveSignal11 :=
  Projectivization.lift
    (fun h : {f : FullSignalSpace11 // f ≠ 0} =>
      Projectivization.mk ℂ (fullConjSignal11 h.1)
        (fullConjSignal11_ne_zero h.2))
    (by
      intro a b c hab
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨conj c, ?_⟩
      rw [hab]
      funext x
      simp [fullConjSignal11])

@[simp] theorem fullProjectiveConj11_mk
    (f : FullSignalSpace11) (hf : f ≠ 0) :
    fullProjectiveConj11 (Projectivization.mk ℂ f hf) =
      Projectivization.mk ℂ (fullConjSignal11 f)
        (fullConjSignal11_ne_zero hf) := rfl

theorem fullProjectiveConj11_sq (p : FullProjectiveSignal11) :
    fullProjectiveConj11 (fullProjectiveConj11 p) = p := by
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveConj11_mk]
      have hh : fullConjSignal11 (fullConjSignal11 f) = f := by
        funext x
        simp [fullConjSignal11]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      simpa only [one_smul] using hh.symm

/-- Fourier and conjugation satisfy `F C = R C F` on actual signals. -/
theorem fullFourierConjSignal11 (f : FullSignalSpace11) :
    ZMod.dft (fullConjSignal11 f) =
      fullReflectionLinear11 (fullConjSignal11 (ZMod.dft f)) := by
  funext x
  change ZMod.dft (fun j => conj (f j)) x = conj (ZMod.dft f (-x))
  simpa using (even11_conj_dft f (-x)).symm

theorem fullProjectiveFourier11_conj (p : FullProjectiveSignal11) :
    fullProjectiveFourier11 (fullProjectiveConj11 p) =
      fullProjectiveReflection11
        (fullProjectiveConj11 (fullProjectiveFourier11 p)) := by
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveFourier11_mk,
        fullProjectiveConj11_mk, fullProjectiveReflection11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      simpa only [one_smul] using fullFourierConjSignal11 f |>.symm

/-- Dilation by two, with inverse dilation by six modulo eleven. -/
def fullD2Linear11 : FullSignalSpace11 ≃ₗ[ℂ] FullSignalSpace11 where
  toFun f x := f (2 * x)
  invFun f x := f (6 * x)
  left_inv f := by
    funext x
    have hx : (2 : ZMod 11) * (6 * x) = x := by native_decide +revert
    exact congrArg f hx
  right_inv f := by
    funext x
    have hx : (6 : ZMod 11) * (2 * x) = x := by native_decide +revert
    exact congrArg f hx
  map_add' f g := by funext x; rfl
  map_smul' c f := by funext x; rfl

def fullProjectiveD2_11 :
    FullProjectiveSignal11 → FullProjectiveSignal11 :=
  Projectivization.map fullD2Linear11.toLinearMap fullD2Linear11.injective

@[simp] theorem fullProjectiveD2_11_mk
    (f : FullSignalSpace11) (hf : f ≠ 0) :
    fullProjectiveD2_11 (Projectivization.mk ℂ f hf) =
      Projectivization.mk ℂ (fullD2Linear11 f)
        (by simpa using fullD2Linear11.injective.ne hf) := rfl

def fullProjectiveD6_11 :
    FullProjectiveSignal11 → FullProjectiveSignal11 :=
  Projectivization.map fullD2Linear11.symm.toLinearMap
    fullD2Linear11.symm.injective

@[simp] theorem fullProjectiveD6_11_mk
    (f : FullSignalSpace11) (hf : f ≠ 0) :
    fullProjectiveD6_11 (Projectivization.mk ℂ f hf) =
      Projectivization.mk ℂ (fullD2Linear11.symm f)
        (by simpa using fullD2Linear11.symm.injective.ne hf) := rfl

theorem fullProjectiveD2D6_11 (p : FullProjectiveSignal11) :
    fullProjectiveD2_11 (fullProjectiveD6_11 p) = p := by
  induction p using Projectivization.ind with
  | h f hf => simp

theorem fullFourierD2Signal11 (f : FullSignalSpace11) :
    ZMod.dft (fullD2Linear11 f) =
      fullD2Linear11.symm (ZMod.dft f) := by
  funext k
  let u : (ZMod 11)ˣ := Units.mk0 (2 : ZMod 11) (by decide)
  have hu : u⁻¹.val = (6 : ZMod 11) := by native_decide
  have h := ZMod.dft_comp_unitMul f u k
  simpa [fullD2Linear11, u, hu] using h

/-- The projective Fourier transform conjugates dilation by two to its
inverse dilation. -/
theorem fullProjectiveFourier11_dilate (p : FullProjectiveSignal11) :
    fullProjectiveFourier11 (fullProjectiveD2_11 p) =
      fullProjectiveD6_11 (fullProjectiveFourier11 p) := by
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveFourier11_mk,
        fullProjectiveD2_11_mk, fullProjectiveD6_11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      simpa only [one_smul] using (fullFourierD2Signal11 f).symm

end
end Biunimodular.F11
