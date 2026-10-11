/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectiveFourier11
import Biunimodular.F11.FullSymmetryWeylEvenReduction11

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar
open scoped LinearAlgebra.Projectivization

noncomputable section

theorem signalOnZMod11_function_ne_zero (z : ZeroAutocorrSignal11) :
    signalOnZMod11 z ≠ 0 := by
  intro hz
  have hzero := congrFun hz 0
  simp [signalOnZMod11_zero] at hzero

/-- The actual projective line of a normalized even biunimodular signal. -/
def fullProjectiveOfSignal11 (z : ZeroAutocorrSignal11) :
    FullProjectiveSignal11 :=
  Projectivization.mk ℂ (signalOnZMod11 z)
    (signalOnZMod11_function_ne_zero z)

theorem fullProjectiveOfSignal11_reflection (z : ZeroAutocorrSignal11) :
    fullProjectiveReflection11 (fullProjectiveOfSignal11 z) =
      fullProjectiveOfSignal11 z := by
  rw [fullProjectiveOfSignal11, fullProjectiveReflection11_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨1, ?_⟩
  funext x
  simp [fullReflectionLinear11, signalOnZMod11_even]

/-- The concrete projective Weyl action is free at every non-Gaussian
normalized even biunimodular signal. -/
theorem fullProjectiveOfSignal11_weyl_stabilizer_trivial
    (z : ZeroAutocorrSignal11)
    (hNonG : ¬ IsQuadraticGaussianSignal11 z)
    (p : WeylLabels11)
    (hp : p • fullProjectiveOfSignal11 z = fullProjectiveOfSignal11 z) :
    p = 1 := by
  cases p with
  | mk a b =>
      change fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b))
        (fullProjectiveOfSignal11 z) = fullProjectiveOfSignal11 z at hp
      rw [fullProjectiveOfSignal11, fullProjectiveWeyl11_mk] at hp
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
      have hst (x : ZMod 11) :
          stdAddChar (b * x) * signalOnZMod11 z (x + a) =
            c * signalOnZMod11 z x := by
        simpa [fullWeylLinear11, Pi.smul_apply, smul_eq_mul] using
          (congrFun hc x).symm
      obtain ⟨ha, hb⟩ := signal11_weyl_stabilizer_trivial
        z hNonG a b c hst
      subst a
      subst b
      rfl

/-- A projective Weyl step between normalized even signals with a
non-Gaussian source identifies the signals themselves. -/
theorem fullProjectiveWeyl11_even_nonGaussian_eq
    (z w : ZeroAutocorrSignal11)
    (hNonG : ¬ IsQuadraticGaussianSignal11 z)
    (p : WeylLabels11)
    (hp : p • fullProjectiveOfSignal11 z = fullProjectiveOfSignal11 w) :
    p = 1 ∧ z.signal = w.signal := by
  cases p with
  | mk a b =>
      change fullProjectiveWeyl11 (Multiplicative.ofAdd (a, b))
        (fullProjectiveOfSignal11 z) = fullProjectiveOfSignal11 w at hp
      rw [fullProjectiveOfSignal11, fullProjectiveWeyl11_mk] at hp
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
      have hst (x : ZMod 11) :
          stdAddChar (b * x) * signalOnZMod11 z (x + a) =
            c * signalOnZMod11 w x := by
        simpa [fullWeylLinear11, Pi.smul_apply, smul_eq_mul] using
          (congrFun hc x).symm
      obtain ⟨ha, hb⟩ := nonGaussian_even_weyl_relation_trivial
        z w hNonG a b c hst
      have hpoint := nonGaussian_even_weyl_relation_eq z w hNonG a b c hst
      constructor
      · subst a
        subst b
        rfl
      · funext j
        have hj := hpoint (j.val : ZMod 11)
        simpa [signalOnZMod11, ZMod.val_natCast_of_lt j.isLt] using hj

end
end Biunimodular.F11
