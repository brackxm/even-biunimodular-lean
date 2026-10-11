/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectiveEvenGenerators11

set_option autoImplicit false

namespace Biunimodular.F11

open scoped LinearAlgebra.Projectivization

noncomputable section

/-- Any invertible complex-linear operator induces a projective permutation. -/
def projectivizeLinearEquiv11
    (e : FullSignalSpace11 ≃ₗ[ℂ] FullSignalSpace11) :
    Equiv.Perm FullProjectiveSignal11 where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h f hf =>
        simp only [Projectivization.map_mk]
        simp
  right_inv p := by
    induction p using Projectivization.ind with
    | h f hf =>
        simp only [Projectivization.map_mk]
        simp

def projectiveD2Perm11 : Equiv.Perm FullProjectiveSignal11 :=
  projectivizeLinearEquiv11 fullD2Linear11

def projectiveFPerm11 : Equiv.Perm FullProjectiveSignal11 :=
  projectivizeLinearEquiv11
    (ZMod.dft : FullSignalSpace11 ≃ₗ[ℂ] FullSignalSpace11)

def projectiveRPerm11 : Equiv.Perm FullProjectiveSignal11 :=
  projectivizeLinearEquiv11 fullReflectionLinear11

def projectiveCPerm11 : Equiv.Perm FullProjectiveSignal11 where
  toFun := fullProjectiveConj11
  invFun := fullProjectiveConj11
  left_inv := fullProjectiveConj11_sq
  right_inv := fullProjectiveConj11_sq

theorem projectiveD2Perm11_apply (p : FullProjectiveSignal11) :
    projectiveD2Perm11 p = fullProjectiveD2_11 p := rfl
theorem projectiveFPerm11_apply (p : FullProjectiveSignal11) :
    projectiveFPerm11 p = fullProjectiveFourier11 p := rfl
theorem projectiveRPerm11_apply (p : FullProjectiveSignal11) :
    projectiveRPerm11 p = fullProjectiveReflection11 p := rfl
theorem projectiveCPerm11_apply (p : FullProjectiveSignal11) :
    projectiveCPerm11 p = fullProjectiveConj11 p := rfl
theorem projectiveD2Perm11_inv_apply (p : FullProjectiveSignal11) :
    projectiveD2Perm11⁻¹ p = fullProjectiveD6_11 p := rfl

theorem projectiveFPerm11_sq :
    projectiveFPerm11 ^ 2 = projectiveRPerm11 := by
  apply Equiv.ext
  intro p
  exact fullProjectiveFourier11_sq p

theorem projectiveCPerm11_sq : projectiveCPerm11 ^ 2 = 1 := by
  apply Equiv.ext
  intro p
  exact fullProjectiveConj11_sq p

theorem projectiveRPerm11_sq : projectiveRPerm11 ^ 2 = 1 := by
  apply Equiv.ext
  intro p
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [pow_two, Equiv.Perm.mul_apply,
        projectiveRPerm11_apply, fullProjectiveReflection11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      funext x
      simp [fullReflectionLinear11]

theorem projectiveFPerm11_conj :
    projectiveFPerm11 * projectiveCPerm11 =
      projectiveRPerm11 * projectiveCPerm11 * projectiveFPerm11 := by
  apply Equiv.ext
  intro p
  exact fullProjectiveFourier11_conj p

theorem projectiveFPerm11_dilate :
    projectiveFPerm11 * projectiveD2Perm11 =
      projectiveD2Perm11⁻¹ * projectiveFPerm11 := by
  apply Equiv.ext
  intro p
  exact fullProjectiveFourier11_dilate p

theorem projectiveD2Perm11_pow_five :
    projectiveD2Perm11 ^ 5 = projectiveRPerm11 := by
  apply Equiv.ext
  intro p
  induction p using Projectivization.ind with
  | h f hf =>
      change fullProjectiveD2_11
          (fullProjectiveD2_11
            (fullProjectiveD2_11
              (fullProjectiveD2_11
                (fullProjectiveD2_11 (Projectivization.mk ℂ f hf))))) =
        fullProjectiveReflection11 (Projectivization.mk ℂ f hf)
      simp only [fullProjectiveD2_11_mk,
        fullProjectiveReflection11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      funext x
      simp only [one_smul]
      change f (-x) = f (2 * (2 * (2 * (2 * (2 * x)))))
      congr 1
      native_decide +revert

theorem projectiveD2Perm11_pow_ten :
    projectiveD2Perm11 ^ 10 = 1 := by
  calc
    projectiveD2Perm11 ^ 10 = (projectiveD2Perm11 ^ 5) ^ 2 := by group
    _ = projectiveRPerm11 ^ 2 := by rw [projectiveD2Perm11_pow_five]
    _ = 1 := projectiveRPerm11_sq

theorem projectiveCPerm11_comm_dilate :
    projectiveCPerm11 * projectiveD2Perm11 =
      projectiveD2Perm11 * projectiveCPerm11 := by
  apply Equiv.ext
  intro p
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [Equiv.Perm.mul_apply,
        projectiveCPerm11_apply, projectiveD2Perm11_apply,
        fullProjectiveConj11_mk, fullProjectiveD2_11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      funext x
      simp [fullConjSignal11, fullD2Linear11]

end
end Biunimodular.F11
