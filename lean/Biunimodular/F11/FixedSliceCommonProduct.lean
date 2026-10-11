/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Intrinsic Fourier-conjugate fixed-slice algebra

This module isolates the algebraic core of the F11 fixed-slice theorem without
choosing numerical eigenspace bases. An even Fourier operator is represented
abstractly by a linear involution `F` on six coordinates. The projective
fixed-slice equations are exactly equality of the six coordinate products

  h_j * (F h)_j.

The module is deliberately independent of interval/Krawczyk data.
-/

abbrev Even6 (R : Type*) := Fin 6 → R

section Field

variable {K : Type*} [Field K]

/-- Coordinate product of a vector and its Fourier image. -/
def fourierCoordProduct (F : Even6 K →ₗ[K] Even6 K)
    (h : Even6 K) (j : Fin 6) : K := h j * (F h) j

/-- The five homogeneous fixed-slice equations, written intrinsically. -/
def FixedSliceEq (F : Even6 K →ₗ[K] Even6 K) (h : Even6 K) : Prop :=
  ∀ j : Fin 6, fourierCoordProduct F h j = fourierCoordProduct F h 0

/-- Apply a field equivalence coordinatewise to an even six-coordinate
vector. This is the underlying semilinear action used in Galois transport. -/
def even6Map {L : Type*} [Field L] (sigma : K ≃+* L) (h : Even6 K) : Even6 L :=
  fun j => sigma (h j)

@[simp] theorem even6Map_apply {L : Type*} [Field L]
    (sigma : K ≃+* L) (h : Even6 K) (j : Fin 6) :
    even6Map sigma h j = sigma (h j) := rfl

@[simp] theorem even6Map_zero {L : Type*} [Field L]
    (sigma : K ≃+* L) : even6Map sigma (0 : Even6 K) = 0 := by
  funext j
  simp

theorem even6Map_injective {L : Type*} [Field L]
    (sigma : K ≃+* L) : Function.Injective (even6Map sigma) := by
  intro h k hmap
  funext j
  apply sigma.injective
  exact congrFun hmap j

/-- Coordinate products commute with a field equivalence whenever the source
and target Fourier operators are intertwined by its coordinatewise action. -/
theorem fourierCoordProduct_ringEquiv
    {L : Type*} [Field L]
    (sigma : K ≃+* L)
    {F : Even6 K →ₗ[K] Even6 K}
    {F' : Even6 L →ₗ[L] Even6 L}
    (hintertwine : ∀ x, even6Map sigma (F x) = F' (even6Map sigma x))
    (h : Even6 K) (j : Fin 6) :
    fourierCoordProduct F' (even6Map sigma h) j =
      sigma (fourierCoordProduct F h j) := by
  have hF := congrFun (hintertwine h) j
  change sigma (F h j) = F' (even6Map sigma h) j at hF
  simp [fourierCoordProduct, hF]

/-- Semilinear transport of the intrinsic fixed-slice equations. -/
theorem fixedSliceEq_ringEquiv
    {L : Type*} [Field L]
    (sigma : K ≃+* L)
    {F : Even6 K →ₗ[K] Even6 K}
    {F' : Even6 L →ₗ[L] Even6 L}
    (hintertwine : ∀ x, even6Map sigma (F x) = F' (even6Map sigma x))
    {h : Even6 K} (hh : FixedSliceEq F h) :
    FixedSliceEq F' (even6Map sigma h) := by
  intro j
  rw [fourierCoordProduct_ringEquiv sigma hintertwine,
    fourierCoordProduct_ringEquiv sigma hintertwine, hh j]

/-- Multiplying the Fourier operator by a nonzero scalar does not change the
projective fixed-slice equations. -/
theorem fixedSliceEq_smul_iff
    {F : Even6 K →ₗ[K] Even6 K} {c : K} (hc : c ≠ 0) (h : Even6 K) :
    FixedSliceEq (c • F) h ↔ FixedSliceEq F h := by
  constructor
  · intro hh j
    apply mul_left_cancel₀ hc
    calc
      c * fourierCoordProduct F h j = fourierCoordProduct (c • F) h j := by
        simp [fourierCoordProduct]
        ring
      _ = fourierCoordProduct (c • F) h 0 := hh j
      _ = c * fourierCoordProduct F h 0 := by
        simp [fourierCoordProduct]
        ring
  · intro hh j
    calc
      fourierCoordProduct (c • F) h j = c * fourierCoordProduct F h j := by
        simp [fourierCoordProduct]
        ring
      _ = c * fourierCoordProduct F h 0 := by rw [hh j]
      _ = fourierCoordProduct (c • F) h 0 := by
        simp [fourierCoordProduct]
        ring

/-- The fixed-slice equations are homogeneous in the vector variable, so
rescaling a vector by a nonzero scalar does not change membership in the
projective fixed slice. -/
theorem fixedSliceEq_smul_vector_iff
    {F : Even6 K →ₗ[K] Even6 K} {c : K} (hc : c ≠ 0) (h : Even6 K) :
    FixedSliceEq F (c • h) ↔ FixedSliceEq F h := by
  have hscale (j : Fin 6) :
      fourierCoordProduct F (c • h) j =
        (c * c) * fourierCoordProduct F h j := by
    simp only [fourierCoordProduct, LinearMap.map_smul, Pi.smul_apply,
      smul_eq_mul]
    ring
  constructor
  · intro hh j
    have hj := hh j
    rw [hscale j, hscale 0] at hj
    apply mul_left_cancel₀ (mul_ne_zero hc hc)
    exact hj
  · intro hh j
    rw [hscale j, hscale 0, hh j]

/-- All six coordinate products have one common value. -/
theorem fixedSliceEq_common
    {F : Even6 K →ₗ[K] Even6 K} {h : Even6 K}
    (hh : FixedSliceEq F h) (i j : Fin 6) :
    fourierCoordProduct F h i = fourierCoordProduct F h j := by
  rw [hh i, hh j]

/-- If the common product is nonzero, then every coordinate of `h` is nonzero. -/
theorem fixedSlice_all_h_nonzero
    {F : Even6 K →ₗ[K] Even6 K} {h : Even6 K}
    (hh : FixedSliceEq F h)
    (h0 : fourierCoordProduct F h 0 ≠ 0) :
    ∀ j, h j ≠ 0 := by
  intro j hj
  have hp := hh j
  rw [fourierCoordProduct, hj, zero_mul] at hp
  exact h0 hp.symm

/-- If the common product is nonzero, then every Fourier coordinate is nonzero. -/
theorem fixedSlice_all_Fh_nonzero
    {F : Even6 K →ₗ[K] Even6 K} {h : Even6 K}
    (hh : FixedSliceEq F h)
    (h0 : fourierCoordProduct F h 0 ≠ 0) :
    ∀ j, F h j ≠ 0 := by
  intro j hj
  have hp := hh j
  rw [fourierCoordProduct, hj, mul_zero] at hp
  exact h0 hp.symm

/-- On the non-boundary locus the Fourier image is coordinatewise reciprocal,
up to the common scalar. -/
theorem fixedSlice_fourier_eq_common_mul_inv
    {F : Even6 K →ₗ[K] Even6 K} {h : Even6 K}
    (hh : FixedSliceEq F h)
    (h0 : fourierCoordProduct F h 0 ≠ 0) :
    ∀ j,
      F h j = fourierCoordProduct F h 0 * (h j)⁻¹ := by
  intro j
  have hj := fixedSlice_all_h_nonzero hh h0 j
  have hp := hh j
  rw [fourierCoordProduct] at hp ⊢
  apply (mul_left_cancel₀ hj)
  calc
    h j * F h j = fourierCoordProduct F h 0 := hp
    _ = h j * (fourierCoordProduct F h 0 * (h j)⁻¹) := by
      field_simp

/-- If the common product vanishes then each coordinate pair has disjoint
support: at every coordinate, `h_j = 0` or `(Fh)_j = 0`. -/
theorem fixedSlice_zero_common_support_disjoint
    {F : Even6 K →ₗ[K] Even6 K} {h : Even6 K}
    (hh : FixedSliceEq F h)
    (hzero : fourierCoordProduct F h 0 = 0) :
    ∀ j, h j = 0 ∨ F h j = 0 := by
  intro j
  have hp := hh j
  rw [hzero] at hp
  exact mul_eq_zero.mp hp

end Field

end Biunimodular.F11
