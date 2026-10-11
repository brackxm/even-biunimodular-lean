/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryFiniteParity11
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Projectivization.Basic

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev FullSignalSpace11 := ZMod 11 → ℂ
abbrev FullProjectiveSignal11 := ℙ ℂ FullSignalSpace11

/-- The actual Weyl translation/modulation on eleven-coordinate signals. -/
def fullWeylLinear11 (a b : ZMod 11) :
    FullSignalSpace11 →ₗ[ℂ] FullSignalSpace11 where
  toFun f x := stdAddChar (b * x) * f (x + a)
  map_add' f g := by
    funext x
    simp [mul_add]
  map_smul' c f := by
    funext x
    simp [smul_eq_mul, mul_left_comm]

theorem fullWeylLinear11_injective (a b : ZMod 11) :
    Function.Injective (fullWeylLinear11 a b) := by
  intro f g h
  funext x
  have hx := congrFun h (x - a)
  change (stdAddChar (b * (x - a)) : ℂ) * f (x - a + a) =
      stdAddChar (b * (x - a)) * g (x - a + a) at hx
  simp only [sub_add_cancel] at hx
  apply mul_left_cancel₀ _ hx
  rw [ZMod.stdAddChar_apply]
  exact Circle.coe_ne_zero _

theorem fullWeylLinear11_comp (a b c d : ZMod 11)
    (f : FullSignalSpace11) :
    fullWeylLinear11 a b (fullWeylLinear11 c d f) =
      (stdAddChar (d * a) : ℂ) • fullWeylLinear11 (a + c) (b + d) f := by
  funext x
  change (stdAddChar (b * x) : ℂ) *
      (stdAddChar (d * (x + a)) * f (x + a + c)) =
    stdAddChar (d * a) *
      (stdAddChar ((b + d) * x) * f (x + (a + c)))
  have harg : b * x + d * (x + a) = d * a + (b + d) * x := by ring
  calc
    _ = stdAddChar (b * x + d * (x + a)) * f (x + a + c) := by
      rw [map_add_eq_mul]
      ring
    _ = stdAddChar (d * a + (b + d) * x) * f (x + (a + c)) := by
      rw [harg]
      congr 1
      ring
    _ = _ := by rw [map_add_eq_mul]; ring

noncomputable def fullProjectiveWeyl11
    (p : WeylLabels11) : FullProjectiveSignal11 → FullProjectiveSignal11 :=
  Projectivization.map
    (fullWeylLinear11 (Multiplicative.toAdd p).1
      (Multiplicative.toAdd p).2)
    (fullWeylLinear11_injective _ _)

@[simp] theorem fullProjectiveWeyl11_mk
    (p : WeylLabels11) (f : FullSignalSpace11) (hf : f ≠ 0) :
    fullProjectiveWeyl11 p (Projectivization.mk ℂ f hf) =
      Projectivization.mk ℂ
        (fullWeylLinear11 (Multiplicative.toAdd p).1
          (Multiplicative.toAdd p).2 f)
        (by simpa using
          (fullWeylLinear11_injective
            (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2).ne hf) := rfl

theorem fullProjectiveWeyl11_identity (z : FullProjectiveSignal11) :
    fullProjectiveWeyl11 1 z = z := by
  induction z using Projectivization.ind with
  | h f hf =>
      rw [fullProjectiveWeyl11_mk]
      have heq : fullWeylLinear11 0 0 f = f := by
        funext x
        simp [fullWeylLinear11]
      simp [heq]

theorem fullProjectiveWeyl11_comp
    (a b c d : ZMod 11) (z : FullProjectiveSignal11) :
    fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b))
      (fullProjectiveWeyl11 (Multiplicative.ofAdd (c, d)) z) =
    fullProjectiveWeyl11 (Multiplicative.ofAdd (a + c, b + d)) z := by
  induction z using Projectivization.ind with
  | h f hf =>
      simp only [fullProjectiveWeyl11_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      exact ⟨stdAddChar (d * a), (fullWeylLinear11_comp a b c d f).symm⟩

instance : MulAction WeylLabels11 FullProjectiveSignal11 where
  smul := fullProjectiveWeyl11
  one_smul := fullProjectiveWeyl11_identity
  mul_smul p q z := by
    cases p with
    | mk a b =>
      cases q with
      | mk c d =>
        exact (fullProjectiveWeyl11_comp a b c d z).symm

end
end Biunimodular.F11
