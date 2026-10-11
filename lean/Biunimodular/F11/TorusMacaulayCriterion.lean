/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- A square coefficient minor with a right inverse determines all listed
monomial values from the equations and a known solution. -/
theorem torusMacaulay_values_eq_of_right_inverse
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι R) (hMN : M * N = 1)
    (values point constant : ι → R)
    (hvalues : Matrix.vecMul values M + constant = 0)
    (hpoint : Matrix.vecMul point M + constant = 0) : values = point := by
  have he : Matrix.vecMul values M = Matrix.vecMul point M :=
    add_right_cancel (hvalues.trans hpoint.symm)
  have hc := congrArg (fun v => Matrix.vecMul v N) he
  simpa only [Matrix.vecMul_vecMul, hMN, Matrix.vecMul_one] using hc

theorem torusMacaulay_values_eq_of_unit_det
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (hM : IsUnit M.det)
    (values point constant : ι → R)
    (hvalues : Matrix.vecMul values M + constant = 0)
    (hpoint : Matrix.vecMul point M + constant = 0) : values = point :=
  torusMacaulay_values_eq_of_right_inverse M M⁻¹
    (Matrix.mul_nonsing_inv M hM) values point constant hvalues hpoint

/-- An invertible reduction certifies a nonzero determinant after any
injective characteristic-zero embedding of the integral coefficient ring. -/
theorem torusMacaulay_det_ne_zero_of_reduction
    {A F K : Type*} [CommRing A] [CommRing F] [Nontrivial F] [CommRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (embed : A →+* K) (reduce : A →+* F) (hinj : Function.Injective embed)
    (M : Matrix ι ι A) (B : Matrix ι ι F)
    (hMB : reduce.mapMatrix M * B = 1) : (embed.mapMatrix M).det ≠ 0 := by
  intro hzero
  have hA : M.det = 0 := by
    apply hinj
    simpa only [map_zero, RingHom.map_det] using hzero
  have hF : (reduce.mapMatrix M).det = 0 := by
    rw [← RingHom.map_det, hA, map_zero]
  exact (Matrix.det_ne_zero_of_right_inverse hMB) hF

end
end Biunimodular.F11
