/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceShapeCertificateData
import Biunimodular.F11.Even11FixedSliceTrace

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

open Polynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

/-!
# Unconditional 32-point geometry of the concrete F11 fixed slice

This file interprets the exact sparse shape identities in
`Even11FixedSliceShapeCertificateData` on the concrete Fourier fixed slice.
All sparse polynomial identities used below are checked by the included
exact certificates.
-/

def even11FixedSliceAffineVector
    (x1 x2 x3 x4 x5 : ℂ) : Even6 ℂ :=
  ![1, x1, x2, x3, x4, x5]

@[simp] theorem even11FixedSliceAffineVector_apply_zero
    (x1 x2 x3 x4 x5 : ℂ) :
    even11FixedSliceAffineVector x1 x2 x3 x4 x5 0 = 1 := rfl

def even11FixedSliceAffineFourier
    (x1 x2 x3 x4 x5 : ℂ) : Even6 ℂ
  | 0 => 1 + 2*x1 + 2*x2 + 2*x3 + 2*x4 + 2*x5
  | 1 => 1 + even11Alpha*x1 + (even11Alpha^2-2)*x2 +
      (even11Alpha^3-3*even11Alpha)*x3 +
      (even11Alpha^4-4*even11Alpha^2+2)*x4 +
      (-even11Alpha^4-even11Alpha^3+3*even11Alpha^2+
        2*even11Alpha-1)*x5
  | 2 => 1 + (even11Alpha^2-2)*x1 +
      (even11Alpha^4-4*even11Alpha^2+2)*x2 +
      (-even11Alpha^4-even11Alpha^3+3*even11Alpha^2+
        2*even11Alpha-1)*x3 +
      (even11Alpha^3-3*even11Alpha)*x4 + even11Alpha*x5
  | 3 => 1 + (even11Alpha^3-3*even11Alpha)*x1 +
      (-even11Alpha^4-even11Alpha^3+3*even11Alpha^2+
        2*even11Alpha-1)*x2 +
      (even11Alpha^2-2)*x3 + even11Alpha*x4 +
      (even11Alpha^4-4*even11Alpha^2+2)*x5
  | 4 => 1 + (even11Alpha^4-4*even11Alpha^2+2)*x1 +
      (even11Alpha^3-3*even11Alpha)*x2 + even11Alpha*x3 +
      (-even11Alpha^4-even11Alpha^3+3*even11Alpha^2+
        2*even11Alpha-1)*x4 + (even11Alpha^2-2)*x5
  | 5 => 1 + (-even11Alpha^4-even11Alpha^3+3*even11Alpha^2+
        2*even11Alpha-1)*x1 + even11Alpha*x2 +
      (even11Alpha^4-4*even11Alpha^2+2)*x3 +
      (even11Alpha^2-2)*x4 + (even11Alpha^3-3*even11Alpha)*x5

theorem even11Fourier_affine_apply
    (x1 x2 x3 x4 x5 : ℂ) :
    even11Fourier (even11FixedSliceAffineVector x1 x2 x3 x4 x5) =
      even11FixedSliceAffineFourier x1 x2 x3 x4 x5 := by
  funext i
  rw [← congrFun (even6LinearMatrix_mulVec even11Fourier
    (even11FixedSliceAffineVector x1 x2 x3 x4 x5)) i]
  rw [← even11FourierPolynomialEvalMatrix_eq]
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      even11FourierPolynomialEvalMatrix, even11FourierPolyEntry,
      even11FoldExponent, even11CosRep, even11FixedSliceAffineVector,
      even11FixedSliceAffineFourier] <;>
    ring

private theorem fixedSliceOriginalSystem_eval
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceOriginalSystem.map (fun polynomial =>
      fixedSliceSparseEval polynomial x5 x4 x3 x2 x1 trace) =
      [x1 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 1 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       x2 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 2 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       x3 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 3 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       x4 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 4 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       x5 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 5 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       trace - even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0] := by
  norm_num [fixedSliceOriginalSystem, fixedSliceOriginal1,
    fixedSliceOriginal2, fixedSliceOriginal3, fixedSliceOriginal4,
    fixedSliceOriginal5, fixedSliceOriginal6, fixedSliceSparseEval,
    fixedSliceSparseTermEval, fixedSliceAlphaEval,
    even11FixedSliceAffineFourier]
  all_goals ring_nf
  all_goals simp

theorem fixedSliceOriginalSystem_vanish_of_fixedSlice
    (x1 x2 x3 x4 x5 : ℂ)
    (hfixed : FixedSliceEq even11Fourier
      (even11FixedSliceAffineVector x1 x2 x3 x4 x5)) :
    ∀ generator ∈ fixedSliceOriginalSystem,
      fixedSliceSparseEval generator x5 x4 x3 x2 x1
        (even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0) = 0 := by
  intro generator hgenerator
  have hmember : fixedSliceSparseEval generator x5 x4 x3 x2 x1
      (even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0) ∈
      fixedSliceOriginalSystem.map (fun polynomial =>
        fixedSliceSparseEval polynomial x5 x4 x3 x2 x1
          (even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0)) :=
    List.mem_map.mpr ⟨generator, hgenerator, rfl⟩
  rw [fixedSliceOriginalSystem_eval] at hmember
  unfold FixedSliceEq fourierCoordProduct at hfixed
  rw [even11Fourier_affine_apply] at hfixed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with h | h | h | h | h | h
  · rw [h, sub_eq_zero]
    simpa [even11FixedSliceAffineVector] using hfixed 1
  · rw [h, sub_eq_zero]
    simpa [even11FixedSliceAffineVector] using hfixed 2
  · rw [h, sub_eq_zero]
    simpa [even11FixedSliceAffineVector] using hfixed 3
  · rw [h, sub_eq_zero]
    simpa [even11FixedSliceAffineVector] using hfixed 4
  · rw [h, sub_eq_zero]
    simpa [even11FixedSliceAffineVector] using hfixed 5
  · rw [h, sub_self]

theorem fixedSlice_of_originalSystem_vanish
    (x1 x2 x3 x4 x5 trace : ℂ)
    (hzero : ∀ generator ∈ fixedSliceOriginalSystem,
      fixedSliceSparseEval generator x5 x4 x3 x2 x1 trace = 0) :
    FixedSliceEq even11Fourier
        (even11FixedSliceAffineVector x1 x2 x3 x4 x5) ∧
      trace = even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0 := by
  let values : List ℂ :=
      [x1 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 1 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       x2 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 2 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       x3 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 3 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       x4 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 4 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       x5 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 5 -
          even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0,
       trace - even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0]
  have hvalues : ∀ value ∈ values, value = 0 := by
    intro value hvalue
    have hlist := fixedSliceOriginalSystem_eval x5 x4 x3 x2 x1 trace
    change fixedSliceOriginalSystem.map (fun polynomial =>
      fixedSliceSparseEval polynomial x5 x4 x3 x2 x1 trace) = values at hlist
    rw [← hlist] at hvalue
    obtain ⟨generator, hgenerator, rfl⟩ := List.mem_map.mp hvalue
    exact hzero generator hgenerator
  have h1 := hvalues
    (x1 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 1 -
      even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0) (by simp [values])
  have h2 := hvalues
    (x2 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 2 -
      even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0) (by simp [values])
  have h3 := hvalues
    (x3 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 3 -
      even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0) (by simp [values])
  have h4 := hvalues
    (x4 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 4 -
      even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0) (by simp [values])
  have h5 := hvalues
    (x5 * even11FixedSliceAffineFourier x1 x2 x3 x4 x5 5 -
      even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0) (by simp [values])
  have ht := hvalues
    (trace - even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0)
      (by simp [values])
  constructor
  · unfold FixedSliceEq fourierCoordProduct
    rw [even11Fourier_affine_apply]
    intro j
    fin_cases j
    · rfl
    · simpa [even11FixedSliceAffineVector] using sub_eq_zero.mp h1
    · simpa [even11FixedSliceAffineVector] using sub_eq_zero.mp h2
    · simpa [even11FixedSliceAffineVector] using sub_eq_zero.mp h3
    · simpa [even11FixedSliceAffineVector] using sub_eq_zero.mp h4
    · simpa [even11FixedSliceAffineVector] using sub_eq_zero.mp h5
  · exact sub_eq_zero.mp ht

def fixedSliceShapeTail1 : FixedSliceSparsePolynomial := fixedSliceShape2.tail
def fixedSliceShapeTail2 : FixedSliceSparsePolynomial := fixedSliceShape3.tail
def fixedSliceShapeTail3 : FixedSliceSparsePolynomial := fixedSliceShape4.tail
def fixedSliceShapeTail4 : FixedSliceSparsePolynomial := fixedSliceShape5.tail
def fixedSliceShapeTail5 : FixedSliceSparsePolynomial := fixedSliceShape6.tail

theorem fixedSliceShapeTail1_traceOnly :
    fixedSliceSparseTraceOnly fixedSliceShapeTail1 := by
  unfold fixedSliceSparseTraceOnly
  native_decide

theorem fixedSliceShapeTail2_traceOnly :
    fixedSliceSparseTraceOnly fixedSliceShapeTail2 := by
  unfold fixedSliceSparseTraceOnly
  native_decide

theorem fixedSliceShapeTail3_traceOnly :
    fixedSliceSparseTraceOnly fixedSliceShapeTail3 := by
  unfold fixedSliceSparseTraceOnly
  native_decide

theorem fixedSliceShapeTail4_traceOnly :
    fixedSliceSparseTraceOnly fixedSliceShapeTail4 := by
  unfold fixedSliceSparseTraceOnly
  native_decide

theorem fixedSliceShapeTail5_traceOnly :
    fixedSliceSparseTraceOnly fixedSliceShapeTail5 := by
  unfold fixedSliceSparseTraceOnly
  native_decide

def fixedSliceReconstruct1 (trace : ℂ) : ℂ :=
  -fixedSliceSparseEval fixedSliceShapeTail1 0 0 0 0 0 trace /
    fixedSliceShapeCoordinateScale

def fixedSliceReconstruct2 (trace : ℂ) : ℂ :=
  -fixedSliceSparseEval fixedSliceShapeTail2 0 0 0 0 0 trace /
    fixedSliceShapeCoordinateScale

def fixedSliceReconstruct3 (trace : ℂ) : ℂ :=
  -fixedSliceSparseEval fixedSliceShapeTail3 0 0 0 0 0 trace /
    fixedSliceShapeCoordinateScale

def fixedSliceReconstruct4 (trace : ℂ) : ℂ :=
  -fixedSliceSparseEval fixedSliceShapeTail4 0 0 0 0 0 trace /
    fixedSliceShapeCoordinateScale

def fixedSliceReconstruct5 (trace : ℂ) : ℂ :=
  -fixedSliceSparseEval fixedSliceShapeTail5 0 0 0 0 0 trace /
    fixedSliceShapeCoordinateScale

theorem fixedSliceShapeCoordinateScale_ne_zero :
    (fixedSliceShapeCoordinateScale : ℂ) ≠ 0 := by
  norm_num [fixedSliceShapeCoordinateScale]

theorem fixedSliceShape2_eval
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval fixedSliceShape2 x5 x4 x3 x2 x1 trace =
      fixedSliceShapeCoordinateScale * x1 +
        fixedSliceSparseEval fixedSliceShapeTail1 0 0 0 0 0 trace := by
  have hform : fixedSliceShape2 =
      ⟨⟨fixedSliceShapeCoordinateScale, 0, 0, 0, 0⟩,
        ⟨0, 0, 0, 0, 1, 0⟩⟩ :: fixedSliceShapeTail1 := by
    native_decide
  rw [hform]
  change _ + fixedSliceSparseEval fixedSliceShapeTail1
      x5 x4 x3 x2 x1 trace = _
  rw [fixedSliceSparseEval_traceOnly fixedSliceShapeTail1_traceOnly]
  simp [fixedSliceSparseTermEval, fixedSliceAlphaEval,
    fixedSliceShapeCoordinateScale]

theorem fixedSliceShape3_eval
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval fixedSliceShape3 x5 x4 x3 x2 x1 trace =
      fixedSliceShapeCoordinateScale * x2 +
        fixedSliceSparseEval fixedSliceShapeTail2 0 0 0 0 0 trace := by
  have hform : fixedSliceShape3 =
      ⟨⟨fixedSliceShapeCoordinateScale, 0, 0, 0, 0⟩,
        ⟨0, 0, 0, 1, 0, 0⟩⟩ :: fixedSliceShapeTail2 := by
    native_decide
  rw [hform]
  change _ + fixedSliceSparseEval fixedSliceShapeTail2
      x5 x4 x3 x2 x1 trace = _
  rw [fixedSliceSparseEval_traceOnly fixedSliceShapeTail2_traceOnly]
  simp [fixedSliceSparseTermEval, fixedSliceAlphaEval,
    fixedSliceShapeCoordinateScale]

theorem fixedSliceShape4_eval
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval fixedSliceShape4 x5 x4 x3 x2 x1 trace =
      fixedSliceShapeCoordinateScale * x3 +
        fixedSliceSparseEval fixedSliceShapeTail3 0 0 0 0 0 trace := by
  have hform : fixedSliceShape4 =
      ⟨⟨fixedSliceShapeCoordinateScale, 0, 0, 0, 0⟩,
        ⟨0, 0, 1, 0, 0, 0⟩⟩ :: fixedSliceShapeTail3 := by
    native_decide
  rw [hform]
  change _ + fixedSliceSparseEval fixedSliceShapeTail3
      x5 x4 x3 x2 x1 trace = _
  rw [fixedSliceSparseEval_traceOnly fixedSliceShapeTail3_traceOnly]
  simp [fixedSliceSparseTermEval, fixedSliceAlphaEval,
    fixedSliceShapeCoordinateScale]

theorem fixedSliceShape5_eval
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval fixedSliceShape5 x5 x4 x3 x2 x1 trace =
      fixedSliceShapeCoordinateScale * x4 +
        fixedSliceSparseEval fixedSliceShapeTail4 0 0 0 0 0 trace := by
  have hform : fixedSliceShape5 =
      ⟨⟨fixedSliceShapeCoordinateScale, 0, 0, 0, 0⟩,
        ⟨0, 1, 0, 0, 0, 0⟩⟩ :: fixedSliceShapeTail4 := by
    native_decide
  rw [hform]
  change _ + fixedSliceSparseEval fixedSliceShapeTail4
      x5 x4 x3 x2 x1 trace = _
  rw [fixedSliceSparseEval_traceOnly fixedSliceShapeTail4_traceOnly]
  simp [fixedSliceSparseTermEval, fixedSliceAlphaEval,
    fixedSliceShapeCoordinateScale]

theorem fixedSliceShape6_eval
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval fixedSliceShape6 x5 x4 x3 x2 x1 trace =
      fixedSliceShapeCoordinateScale * x5 +
        fixedSliceSparseEval fixedSliceShapeTail5 0 0 0 0 0 trace := by
  have hform : fixedSliceShape6 =
      ⟨⟨fixedSliceShapeCoordinateScale, 0, 0, 0, 0⟩,
        ⟨1, 0, 0, 0, 0, 0⟩⟩ :: fixedSliceShapeTail5 := by
    native_decide
  rw [hform]
  change _ + fixedSliceSparseEval fixedSliceShapeTail5
      x5 x4 x3 x2 x1 trace = _
  rw [fixedSliceSparseEval_traceOnly fixedSliceShapeTail5_traceOnly]
  simp [fixedSliceSparseTermEval, fixedSliceAlphaEval,
    fixedSliceShapeCoordinateScale]

theorem fixedSliceShape1_eval
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval fixedSliceShape1 x5 x4 x3 x2 x1 trace =
      fixedSliceTraceP32.eval₂ (Int.castRingHom ℂ) trace := by
  norm_num [fixedSliceShape1, fixedSliceSparseEval,
    fixedSliceSparseTermEval, fixedSliceAlphaEval, fixedSliceTraceP32,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow]
  ring

private theorem fixedSliceReconstruct1_eq_of_shape
    {x5 x4 x3 x2 x1 trace : ℂ}
    (hshape : fixedSliceSparseEval fixedSliceShape2
      x5 x4 x3 x2 x1 trace = 0) :
    x1 = fixedSliceReconstruct1 trace := by
  rw [fixedSliceShape2_eval] at hshape
  unfold fixedSliceReconstruct1
  apply (eq_div_iff fixedSliceShapeCoordinateScale_ne_zero).2
  linear_combination hshape

private theorem fixedSliceReconstruct2_eq_of_shape
    {x5 x4 x3 x2 x1 trace : ℂ}
    (hshape : fixedSliceSparseEval fixedSliceShape3
      x5 x4 x3 x2 x1 trace = 0) :
    x2 = fixedSliceReconstruct2 trace := by
  rw [fixedSliceShape3_eval] at hshape
  unfold fixedSliceReconstruct2
  apply (eq_div_iff fixedSliceShapeCoordinateScale_ne_zero).2
  linear_combination hshape

private theorem fixedSliceReconstruct3_eq_of_shape
    {x5 x4 x3 x2 x1 trace : ℂ}
    (hshape : fixedSliceSparseEval fixedSliceShape4
      x5 x4 x3 x2 x1 trace = 0) :
    x3 = fixedSliceReconstruct3 trace := by
  rw [fixedSliceShape4_eval] at hshape
  unfold fixedSliceReconstruct3
  apply (eq_div_iff fixedSliceShapeCoordinateScale_ne_zero).2
  linear_combination hshape

private theorem fixedSliceReconstruct4_eq_of_shape
    {x5 x4 x3 x2 x1 trace : ℂ}
    (hshape : fixedSliceSparseEval fixedSliceShape5
      x5 x4 x3 x2 x1 trace = 0) :
    x4 = fixedSliceReconstruct4 trace := by
  rw [fixedSliceShape5_eval] at hshape
  unfold fixedSliceReconstruct4
  apply (eq_div_iff fixedSliceShapeCoordinateScale_ne_zero).2
  linear_combination hshape

private theorem fixedSliceReconstruct5_eq_of_shape
    {x5 x4 x3 x2 x1 trace : ℂ}
    (hshape : fixedSliceSparseEval fixedSliceShape6
      x5 x4 x3 x2 x1 trace = 0) :
    x5 = fixedSliceReconstruct5 trace := by
  rw [fixedSliceShape6_eval] at hshape
  unfold fixedSliceReconstruct5
  apply (eq_div_iff fixedSliceShapeCoordinateScale_ne_zero).2
  linear_combination hshape

private theorem fixedSliceShapeSystem_vanish_at_reconstruction
    {trace : ℂ}
    (hroot : fixedSliceTraceP32.eval₂ (Int.castRingHom ℂ) trace = 0) :
    ∀ shape ∈ fixedSliceShapeSystem,
      fixedSliceSparseEval shape
        (fixedSliceReconstruct5 trace) (fixedSliceReconstruct4 trace)
        (fixedSliceReconstruct3 trace) (fixedSliceReconstruct2 trace)
        (fixedSliceReconstruct1 trace) trace = 0 := by
  intro shape hshape
  simp only [fixedSliceShapeSystem, List.mem_cons,
    List.not_mem_nil, or_false] at hshape
  rcases hshape with h | h | h | h | h | h
  · subst shape
    rw [fixedSliceShape1_eval]
    exact hroot
  · subst shape
    rw [fixedSliceShape2_eval]
    unfold fixedSliceReconstruct1
    field_simp [fixedSliceShapeCoordinateScale_ne_zero]
    rw [div_self fixedSliceShapeCoordinateScale_ne_zero]
    ring
  · subst shape
    rw [fixedSliceShape3_eval]
    unfold fixedSliceReconstruct2
    field_simp [fixedSliceShapeCoordinateScale_ne_zero]
    rw [div_self fixedSliceShapeCoordinateScale_ne_zero]
    ring
  · subst shape
    rw [fixedSliceShape4_eval]
    unfold fixedSliceReconstruct3
    field_simp [fixedSliceShapeCoordinateScale_ne_zero]
    rw [div_self fixedSliceShapeCoordinateScale_ne_zero]
    ring
  · subst shape
    rw [fixedSliceShape5_eval]
    unfold fixedSliceReconstruct4
    field_simp [fixedSliceShapeCoordinateScale_ne_zero]
    rw [div_self fixedSliceShapeCoordinateScale_ne_zero]
    ring
  · subst shape
    rw [fixedSliceShape6_eval]
    unfold fixedSliceReconstruct5
    field_simp [fixedSliceShapeCoordinateScale_ne_zero]
    rw [div_self fixedSliceShapeCoordinateScale_ne_zero]
    ring

private theorem even11_fixedSlice_affine_shape
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hfixed : FixedSliceEq even11Fourier h) :
    let trace := even11Fourier h 0 / h 0
    fixedSliceTraceP32.eval₂ (Int.castRingHom ℂ) trace = 0 ∧
      h 1 / h 0 = fixedSliceReconstruct1 trace ∧
      h 2 / h 0 = fixedSliceReconstruct2 trace ∧
      h 3 / h 0 = fixedSliceReconstruct3 trace ∧
      h 4 / h 0 = fixedSliceReconstruct4 trace ∧
      h 5 / h 0 = fixedSliceReconstruct5 trace := by
  have hcommon := even11_fixedSlice_common_ne_zero_certified hnz hfixed
  have hh0 : h 0 ≠ 0 := fixedSlice_all_h_nonzero hfixed hcommon 0
  let x1 := h 1 / h 0
  let x2 := h 2 / h 0
  let x3 := h 3 / h 0
  let x4 := h 4 / h 0
  let x5 := h 5 / h 0
  let trace := even11Fourier h 0 / h 0
  have hnormalize : (h 0)⁻¹ • h =
      even11FixedSliceAffineVector x1 x2 x3 x4 x5 := by
    funext i
    fin_cases i <;>
      simp [even11FixedSliceAffineVector, x1, x2, x3, x4, x5,
        smul_eq_mul, hh0]
    all_goals rw [div_eq_mul_inv]
    all_goals ring
  have hfixedAffine : FixedSliceEq even11Fourier
      (even11FixedSliceAffineVector x1 x2 x3 x4 x5) := by
    rw [← hnormalize]
    exact (fixedSliceEq_smul_vector_iff (inv_ne_zero hh0) h).2 hfixed
  have htrace : even11FixedSliceAffineFourier x1 x2 x3 x4 x5 0 = trace := by
    rw [← even11Fourier_affine_apply]
    rw [← hnormalize]
    simp [trace, div_eq_mul_inv, mul_comm]
  have horiginal := fixedSliceOriginalSystem_vanish_of_fixedSlice
    x1 x2 x3 x4 x5 hfixedAffine
  rw [htrace] at horiginal
  have hshape := fixedSliceShapeSystem_vanish
    x5 x4 x3 x2 x1 trace horiginal
  have hs1 := hshape fixedSliceShape1 (by simp [fixedSliceShapeSystem])
  have hs2 := hshape fixedSliceShape2 (by simp [fixedSliceShapeSystem])
  have hs3 := hshape fixedSliceShape3 (by simp [fixedSliceShapeSystem])
  have hs4 := hshape fixedSliceShape4 (by simp [fixedSliceShapeSystem])
  have hs5 := hshape fixedSliceShape5 (by simp [fixedSliceShapeSystem])
  have hs6 := hshape fixedSliceShape6 (by simp [fixedSliceShapeSystem])
  refine ⟨?_, fixedSliceReconstruct1_eq_of_shape hs2,
    fixedSliceReconstruct2_eq_of_shape hs3,
    fixedSliceReconstruct3_eq_of_shape hs4,
    fixedSliceReconstruct4_eq_of_shape hs5,
    fixedSliceReconstruct5_eq_of_shape hs6⟩
  rw [fixedSliceShape1_eval] at hs1
  exact hs1

private theorem fixedSliceTraceRoot_eval
    (trace : FixedSliceTraceRoot) :
    fixedSliceTraceP32.eval₂ (Int.castRingHom ℂ) (trace : ℂ) = 0 := by
  have hroot := (Polynomial.mem_rootSet.mp trace.2).2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    fixedSliceTraceP32Q_map_complex] at hroot
  rw [Polynomial.eval₂_eq_eval_map]
  exact hroot

private theorem fixedSlicePoint_of_trace_exists
    (trace : FixedSliceTraceRoot) :
    ∃ p : Even11FixedSlicePoint,
      even11FixedSliceTrace p = (trace : ℂ) := by
  let x1 := fixedSliceReconstruct1 (trace : ℂ)
  let x2 := fixedSliceReconstruct2 (trace : ℂ)
  let x3 := fixedSliceReconstruct3 (trace : ℂ)
  let x4 := fixedSliceReconstruct4 (trace : ℂ)
  let x5 := fixedSliceReconstruct5 (trace : ℂ)
  let h := even11FixedSliceAffineVector x1 x2 x3 x4 x5
  have hshape := fixedSliceShapeSystem_vanish_at_reconstruction
    (fixedSliceTraceRoot_eval trace)
  have horiginal := fixedSliceOriginalSystem_vanish_of_shape
    x5 x4 x3 x2 x1 (trace : ℂ) hshape
  obtain ⟨hfixed, htrace⟩ := fixedSlice_of_originalSystem_vanish
    x1 x2 x3 x4 x5 (trace : ℂ) horiginal
  have hnz : h ≠ 0 := by
    intro hzero
    have := congrFun hzero 0
    norm_num [h, even11FixedSliceAffineVector] at this
  let p : Even11FixedSlicePoint :=
    ⟨Projectivization.mk ℂ h hnz,
      (even11ProjectiveFixedSlice_mk h hnz).2
        ((even11_fixedSliceEq_normalized_iff h).2 hfixed)⟩
  refine ⟨p, ?_⟩
  change even11Fourier h 0 / h 0 = (trace : ℂ)
  rw [even11Fourier_affine_apply]
  simpa [h, even11FixedSliceAffineVector] using htrace.symm

theorem even11FixedSliceTrace_isRoot
    (p : Even11FixedSlicePoint) :
    (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot
      (even11FixedSliceTrace p) := by
  rcases p with ⟨p, hp⟩
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveFixedSlice_mk] at hp
      have hfixed : FixedSliceEq even11Fourier h :=
        (even11_fixedSliceEq_normalized_iff h).mp hp
      have hshape := even11_fixedSlice_affine_shape hnz hfixed
      change (fixedSliceTraceP32.map (Int.castRingHom ℂ)).eval
        (even11Fourier h 0 / h 0) = 0
      rw [← Polynomial.eval₂_eq_eval_map]
      exact hshape.1

theorem even11FixedSliceTrace_injective :
    Function.Injective even11FixedSliceTrace := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ htrace
  apply Subtype.ext
  induction p using Projectivization.ind with
  | h h hnz =>
    induction q using Projectivization.ind with
    | h k knz =>
      rw [even11ProjectiveFixedSlice_mk] at hp hq
      have hfixed : FixedSliceEq even11Fourier h :=
        (even11_fixedSliceEq_normalized_iff h).mp hp
      have kfixed : FixedSliceEq even11Fourier k :=
        (even11_fixedSliceEq_normalized_iff k).mp hq
      have hhcommon :=
        even11_fixedSlice_common_ne_zero_certified hnz hfixed
      have hkcommon :=
        even11_fixedSlice_common_ne_zero_certified knz kfixed
      have hh0 : h 0 ≠ 0 := fixedSlice_all_h_nonzero hfixed hhcommon 0
      have hk0 : k 0 ≠ 0 := fixedSlice_all_h_nonzero kfixed hkcommon 0
      have hshape := even11_fixedSlice_affine_shape hnz hfixed
      have kshape := even11_fixedSlice_affine_shape knz kfixed
      dsimp only at hshape kshape
      change even11Fourier h 0 / h 0 =
        even11Fourier k 0 / k 0 at htrace
      have h1 : h 1 / h 0 = k 1 / k 0 := by
        rw [hshape.2.1, kshape.2.1, htrace]
      have h2 : h 2 / h 0 = k 2 / k 0 := by
        rw [hshape.2.2.1, kshape.2.2.1, htrace]
      have h3 : h 3 / h 0 = k 3 / k 0 := by
        rw [hshape.2.2.2.1, kshape.2.2.2.1, htrace]
      have h4 : h 4 / h 0 = k 4 / k 0 := by
        rw [hshape.2.2.2.2.1, kshape.2.2.2.2.1, htrace]
      have h5 : h 5 / h 0 = k 5 / k 0 := by
        rw [hshape.2.2.2.2.2, kshape.2.2.2.2.2, htrace]
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨h 0 / k 0, ?_⟩
      funext i
      fin_cases i
      · simp [smul_eq_mul, hk0]
      · change (h 0 / k 0) * k 1 = h 1
        field_simp [hh0, hk0] at h1 ⊢
        linear_combination -h1
      · change (h 0 / k 0) * k 2 = h 2
        field_simp [hh0, hk0] at h2 ⊢
        linear_combination -h2
      · change (h 0 / k 0) * k 3 = h 3
        field_simp [hh0, hk0] at h3 ⊢
        linear_combination -h3
      · change (h 0 / k 0) * k 4 = h 4
        field_simp [hh0, hk0] at h4 ⊢
        linear_combination -h4
      · change (h 0 / k 0) * k 5 = h 5
        field_simp [hh0, hk0] at h5 ⊢
        linear_combination -h5

/-- The complete exact 32-point trace-shape certificate. -/
theorem even11FixedSliceTraceGeometryCertificate :
    Even11FixedSliceTraceGeometryCertificate where
  trace_isRoot := even11FixedSliceTrace_isRoot
  trace_bijective := by
    constructor
    · intro p q hpq
      apply even11FixedSliceTrace_injective
      exact congrArg Subtype.val hpq
    · intro trace
      obtain ⟨p, hp⟩ := fixedSlicePoint_of_trace_exists trace
      refine ⟨p, ?_⟩
      apply Subtype.ext
      exact hp

/-- Unconditional concrete fixed-slice geometry: the Fourier-orbit quotient
is in value-preserving bijection with the sixteen certified roots of `P16`. -/
theorem even11FixedSliceGeometryCertificate :
    Even11FixedSliceGeometryCertificate :=
  even11FixedSliceTraceGeometryCertificate.toGeometryCertificate


end

end Biunimodular.F11
