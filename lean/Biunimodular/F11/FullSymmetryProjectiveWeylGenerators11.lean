/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectivePermutations11

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar
open scoped ComplexConjugate LinearAlgebra.Projectivization

noncomputable section

private theorem two_six_shift11 (x a : ZMod 11) :
    2 * (x + 6 * a) = 2 * x + a := by
  ring_nf
  have h12 : (12 : ZMod 11) = 1 := by decide
  rw [h12, mul_one]

theorem fullD2WeylLinear11 (a b : ZMod 11) (f : FullSignalSpace11) :
    fullD2Linear11 (fullWeylLinear11 a b f) =
      fullWeylLinear11 (6 * a) (2 * b) (fullD2Linear11 f) := by
  funext x
  change (stdAddChar (b * (2 * x)) : ℂ) * f (2 * x + a) =
    stdAddChar ((2 * b) * x) * f (2 * (x + 6 * a))
  rw [two_six_shift11]
  congr 1
  ring

theorem fullReflectionWeylLinear11 (a b : ZMod 11)
    (f : FullSignalSpace11) :
    fullReflectionLinear11 (fullWeylLinear11 a b f) =
      fullWeylLinear11 (-a) (-b) (fullReflectionLinear11 f) := by
  funext x
  change (stdAddChar (b * -x) : ℂ) * f (-x + a) =
    stdAddChar ((-b) * x) * f (-(x + -a))
  congr 1 <;> ring

theorem fullConjWeylSignal11 (a b : ZMod 11)
    (f : FullSignalSpace11) :
    fullConjSignal11 (fullWeylLinear11 a b f) =
      fullWeylLinear11 a (-b) (fullConjSignal11 f) := by
  funext x
  change conj ((stdAddChar (b * x) : ℂ) * f (x + a)) =
    stdAddChar ((-b) * x) * conj (f (x + a))
  rw [map_mul]
  congr 1
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  ring

theorem fullFourierWeylSignal11 (a b : ZMod 11)
    (f : FullSignalSpace11) :
    ZMod.dft (fullWeylLinear11 a b f) =
      (stdAddChar (-(a * b)) : ℂ) •
        fullWeylLinear11 (-b) a (ZMod.dft f) := by
  funext k
  have hcoef (j : ZMod 11) :
      (stdAddChar (-(j * k)) : ℂ) * stdAddChar (b * j) =
        stdAddChar (-(a * b)) *
          (stdAddChar (a * k) *
            stdAddChar (-((j + a) * (k - b)))) := by
    rw [← map_add_eq_mul, ← map_add_eq_mul, ← map_add_eq_mul]
    congr 1
    ring
  simp only [Pi.smul_apply, ZMod.dft_apply, smul_eq_mul]
  simp only [fullWeylLinear11, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ZMod.dft_apply, smul_eq_mul]
  simp only [← sub_eq_add_neg]
  change (∑ j : ZMod 11,
      (stdAddChar (-(j * k)) : ℂ) *
        (stdAddChar (b * j) * f (j + a))) =
    stdAddChar (-(a * b)) *
      (stdAddChar (a * k) *
        ∑ t : ZMod 11,
          (stdAddChar (-(t * (k - b))) : ℂ) * f t)
  calc
    _ = ∑ j : ZMod 11,
          stdAddChar (-(a * b)) *
            (stdAddChar (a * k) *
              (stdAddChar (-((j + a) * (k - b))) * f (j + a))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, hcoef]
      ring
    _ = stdAddChar (-(a * b)) *
          (stdAddChar (a * k) *
            ∑ j : ZMod 11,
              (stdAddChar (-((j + a) * (k - b))) : ℂ) * f (j + a)) := by
      simp [Finset.mul_sum]
    _ = _ := by
      congr 2
      exact Fintype.sum_equiv (Equiv.addRight a)
        (fun j : ZMod 11 =>
          (stdAddChar (-((j + a) * (k - b))) : ℂ) * f (j + a))
        (fun t : ZMod 11 =>
          (stdAddChar (-(t * (k - b))) : ℂ) * f t)
        (by intro j; rfl)

theorem fullProjectiveD2Weyl11 (a b : ZMod 11)
    (p : FullProjectiveSignal11) :
    fullProjectiveD2_11
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b)) p) =
    fullProjectiveWeyl11 (Multiplicative.ofAdd (6 * a, 2 * b))
      (fullProjectiveD2_11 p) := by
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveWeyl11_mk, fullProjectiveD2_11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      change (1 : ℂ) • fullWeylLinear11 (6 * a) (2 * b) (fullD2Linear11 f) =
        fullD2Linear11 (fullWeylLinear11 a b f)
      simpa only [one_smul] using (fullD2WeylLinear11 a b f).symm

theorem fullProjectiveReflectionWeyl11 (a b : ZMod 11)
    (p : FullProjectiveSignal11) :
    fullProjectiveReflection11
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b)) p) =
    fullProjectiveWeyl11 (Multiplicative.ofAdd (-a, -b))
      (fullProjectiveReflection11 p) := by
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveWeyl11_mk, fullProjectiveReflection11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      change (1 : ℂ) • fullWeylLinear11 (-a) (-b) (fullReflectionLinear11 f) =
        fullReflectionLinear11 (fullWeylLinear11 a b f)
      simpa only [one_smul] using (fullReflectionWeylLinear11 a b f).symm

theorem fullProjectiveConjWeyl11 (a b : ZMod 11)
    (p : FullProjectiveSignal11) :
    fullProjectiveConj11
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b)) p) =
    fullProjectiveWeyl11 (Multiplicative.ofAdd (a, -b))
      (fullProjectiveConj11 p) := by
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveWeyl11_mk, fullProjectiveConj11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      change (1 : ℂ) • fullWeylLinear11 a (-b) (fullConjSignal11 f) =
        fullConjSignal11 (fullWeylLinear11 a b f)
      simpa only [one_smul] using (fullConjWeylSignal11 a b f).symm

theorem fullProjectiveFourierWeyl11 (a b : ZMod 11)
    (p : FullProjectiveSignal11) :
    fullProjectiveFourier11
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b)) p) =
    fullProjectiveWeyl11 (Multiplicative.ofAdd (-b, a))
      (fullProjectiveFourier11 p) := by
  induction p using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveWeyl11_mk, fullProjectiveFourier11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨stdAddChar (-(a * b)), ?_⟩
      change (stdAddChar (-(a * b)) : ℂ) •
          fullWeylLinear11 (-b) a (ZMod.dft f) =
        ZMod.dft (fullWeylLinear11 a b f)
      exact (fullFourierWeylSignal11 a b f).symm

theorem linearD11_weyl_label (a b : ZMod 11) :
    linearFourierWeylLabelAction11 linearD11
      (Multiplicative.ofAdd (a, b)) =
    Multiplicative.ofAdd (6 * a, 2 * b) := by
  native_decide +revert

theorem linearC11_weyl_label (a b : ZMod 11) :
    linearFourierWeylLabelAction11 linearC11
      (Multiplicative.ofAdd (a, b)) =
    Multiplicative.ofAdd (a, -b) := by
  native_decide +revert

theorem linearF11_weyl_label (a b : ZMod 11) :
    linearFourierWeylLabelAction11 linearF11
      (Multiplicative.ofAdd (a, b)) =
    Multiplicative.ofAdd (-b, a) := by
  native_decide +revert

theorem linearR11_weyl_label (a b : ZMod 11) :
    linearFourierWeylLabelAction11 linearR11
      (Multiplicative.ofAdd (a, b)) =
    Multiplicative.ofAdd (-a, -b) := by
  native_decide +revert

theorem projectiveD2Perm11_weyl_intertwine
    (p : WeylLabels11) (z : FullProjectiveSignal11) :
    projectiveD2Perm11 (p • z) =
      (linearFourierWeylAction11 linearD11 p) •
        projectiveD2Perm11 z := by
  rcases p with ⟨a, b⟩
  change projectiveD2Perm11
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b)) z) =
    fullProjectiveWeyl11
      (linearFourierWeylLabelAction11 linearD11
        (Multiplicative.ofAdd (a, b))) (projectiveD2Perm11 z)
  rw [linearD11_weyl_label]
  exact fullProjectiveD2Weyl11 a b z

theorem projectiveCPerm11_weyl_intertwine
    (p : WeylLabels11) (z : FullProjectiveSignal11) :
    projectiveCPerm11 (p • z) =
      (linearFourierWeylAction11 linearC11 p) •
        projectiveCPerm11 z := by
  rcases p with ⟨a, b⟩
  change projectiveCPerm11
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b)) z) =
    fullProjectiveWeyl11
      (linearFourierWeylLabelAction11 linearC11
        (Multiplicative.ofAdd (a, b))) (projectiveCPerm11 z)
  rw [linearC11_weyl_label]
  exact fullProjectiveConjWeyl11 a b z

theorem projectiveFPerm11_weyl_intertwine
    (p : WeylLabels11) (z : FullProjectiveSignal11) :
    projectiveFPerm11 (p • z) =
      (linearFourierWeylAction11 linearF11 p) •
        projectiveFPerm11 z := by
  rcases p with ⟨a, b⟩
  change projectiveFPerm11
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b)) z) =
    fullProjectiveWeyl11
      (linearFourierWeylLabelAction11 linearF11
        (Multiplicative.ofAdd (a, b))) (projectiveFPerm11 z)
  rw [linearF11_weyl_label]
  exact fullProjectiveFourierWeyl11 a b z

theorem projectiveRPerm11_weyl_intertwine
    (p : WeylLabels11) (z : FullProjectiveSignal11) :
    projectiveRPerm11 (p • z) =
      (linearFourierWeylAction11 linearR11 p) •
        projectiveRPerm11 z := by
  rcases p with ⟨a, b⟩
  change projectiveRPerm11
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b)) z) =
    fullProjectiveWeyl11
      (linearFourierWeylLabelAction11 linearR11
        (Multiplicative.ofAdd (a, b))) (projectiveRPerm11 z)
  rw [linearR11_weyl_label]
  exact fullProjectiveReflectionWeyl11 a b z

end
end Biunimodular.F11
