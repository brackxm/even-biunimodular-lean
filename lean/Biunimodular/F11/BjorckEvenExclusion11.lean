/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PhaseSignalSemantic11
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-!
The square-class obstruction at length eleven.  The arguments below need only
the three-valued shape of a Björck--Saffari seed, not its particular phase
parameters or the biunimodularity equations.
-/

/-- The zero, quadratic-residue, and nonresidue classes in `ZMod 11`. -/
def squareClass11 (x : ZMod 11) : Fin 3 :=
  if x = 0 then 0 else if x ∈ ({1, 3, 4, 5, 9} : Finset (ZMod 11)) then 1 else 2

theorem squareClass11_eq_one_iff (x : ZMod 11) :
    squareClass11 x = 1 ↔ x ≠ 0 ∧ ∃ y : ZMod 11, y ^ 2 = x := by
  native_decide +revert

theorem squareClass11_eq_two_iff (x : ZMod 11) :
    squareClass11 x = 2 ↔ x ≠ 0 ∧ ¬ ∃ y : ZMod 11, y ^ 2 = x := by
  native_decide +revert

/-- A normalized square-class seed with arbitrary nonzero class values. -/
def squareClassSeed11 (u v : ℂ) (x : ZMod 11) : ℂ :=
  if squareClass11 x = 0 then 1 else if squareClass11 x = 1 then u else v

theorem squareClassSeed11_ne_zero {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (x : ZMod 11) : squareClassSeed11 u v x ≠ 0 := by
  unfold squareClassSeed11
  split_ifs <;> simp_all

/-- Among eleven arguments, two distinct ones have the same class at both
ends of the reflection pair about any center. -/
theorem squareClass11_collision (t : ZMod 11) :
    ∃ x y : ZMod 11, x ≠ y ∧
      squareClass11 (t - x) = squareClass11 (t - y) ∧
      squareClass11 (t + x) = squareClass11 (t + y) := by
  native_decide +revert

/-- Every affine reflection sends some residue to a nonresidue. -/
theorem squareClass11_crosses (t : ZMod 11) :
    ∃ x : ZMod 11,
      squareClass11 (t - x) = 1 ∧ squareClass11 (t + x) = 2 := by
  native_decide +revert

theorem squareClassSeed11_eq_of_class_eq (u v : ℂ) {x y : ZMod 11}
    (h : squareClass11 x = squareClass11 y) :
    squareClassSeed11 u v x = squareClassSeed11 u v y := by
  simp only [squareClassSeed11, h]

/-- No translate of a square-class seed with distinct residue and
nonresidue values is even. -/
theorem squareClassSeed11_no_even_translate {u v : ℂ} (huv : u ≠ v)
    (t : ZMod 11) :
    ¬ ∀ x : ZMod 11,
      squareClassSeed11 u v (t - x) = squareClassSeed11 u v (t + x) := by
  intro heven
  obtain ⟨x, hx1, hx2⟩ := squareClass11_crosses t
  have h := heven x
  simp only [squareClassSeed11, hx1, hx2] at h
  exact huv h

/-- Translation followed by modulation of a square-class seed. -/
noncomputable def modulatedSquareClassSeed11 (u v : ℂ) (j t x : ZMod 11) : ℂ :=
  stdAddChar (j * x) * squareClassSeed11 u v (t + x)

private theorem even_modulated_char_relation (f : ZMod 11 → ℂ)
    (j t x : ZMod 11)
    (heven : ∀ y : ZMod 11,
      stdAddChar (j * -y) * f (t - y) =
        stdAddChar (j * y) * f (t + y)) :
    stdAddChar (2 * j * x) * f (t + x) = f (t - x) := by
  have hprod : stdAddChar (j * x) * stdAddChar (j * -x) = 1 := by
    rw [← map_add_eq_mul]
    have hz : j * x + j * -x = 0 := by ring
    rw [hz]
    simp
  have h := congrArg (fun z : ℂ => stdAddChar (j * x) * z) (heven x)
  have hleft :
      stdAddChar (j * x) * (stdAddChar (j * -x) * f (t - x)) =
        f (t - x) := by
    rw [← mul_assoc, hprod, one_mul]
  rw [hleft] at h
  calc
    stdAddChar (2 * j * x) * f (t + x) =
        (stdAddChar (j * x) * stdAddChar (j * x)) * f (t + x) := by
          congr 1
          rw [← map_add_eq_mul]
          congr 1
          ring
    _ = f (t - x) := by
      rw [mul_assoc]
      exact h.symm

/-- No translated or modulated square-class seed at length eleven can be
even when its residue and nonresidue values are distinct and nonzero. The
value at zero is fixed to one and may be a third distinct value. -/
theorem modulatedSquareClassSeed11_not_even {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (j t : ZMod 11) :
    ¬ ∀ x : ZMod 11,
      modulatedSquareClassSeed11 u v j t (-x) =
        modulatedSquareClassSeed11 u v j t x := by
  intro heven
  have heven' (x : ZMod 11) :
      stdAddChar (j * -x) * squareClassSeed11 u v (t - x) =
        stdAddChar (j * x) * squareClassSeed11 u v (t + x) := by
    simpa [modulatedSquareClassSeed11, sub_eq_add_neg] using heven x
  obtain ⟨x, y, hxy, hminus, hplus⟩ := squareClass11_collision t
  have hx := even_modulated_char_relation (squareClassSeed11 u v) j t x heven'
  have hy := even_modulated_char_relation (squareClassSeed11 u v) j t y heven'
  have hminus' := squareClassSeed11_eq_of_class_eq u v hminus
  have hplus' := squareClassSeed11_eq_of_class_eq u v hplus
  rw [← hminus', ← hplus'] at hy
  have hchar : stdAddChar (2 * j * x) = stdAddChar (2 * j * y) := by
    exact mul_right_cancel₀ (squareClassSeed11_ne_zero hu hv (t + x))
      (hx.trans hy.symm)
  have heq : 2 * j * x = 2 * j * y := ZMod.injective_stdAddChar hchar
  have hprod : (2 : ZMod 11) * j * (x - y) = 0 := by
    calc
      (2 : ZMod 11) * j * (x - y) = 2 * j * x - 2 * j * y := by ring
      _ = 0 := sub_eq_zero.mpr heq
  have hj : j = 0 := by
    rcases mul_eq_zero.mp hprod with hz | hz
    · exact (mul_eq_zero.mp hz).resolve_left (by decide)
    · exact False.elim ((sub_ne_zero.mpr hxy) hz)
  have hseed : ∀ x : ZMod 11,
      squareClassSeed11 u v (t - x) = squareClassSeed11 u v (t + x) := by
    intro z
    simpa [hj] using heven' z
  exact squareClassSeed11_no_even_translate huv t hseed

/-- The same family indexed as the repository's length-eleven signals. -/
noncomputable def modulatedSquareClassSignal11
    (u v : ℂ) (j t : ZMod 11) (x : Fin 11) : ℂ :=
  modulatedSquareClassSeed11 u v j t (x.1 : ZMod 11)

theorem modulatedSquareClassSignal11_not_even {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (j t : ZMod 11) :
    ¬ ∀ x : Fin 11,
      modulatedSquareClassSignal11 u v j t (neg11 x) =
        modulatedSquareClassSignal11 u v j t x := by
  intro heven
  apply modulatedSquareClassSeed11_not_even hu hv huv j t
  intro x
  let i : Fin 11 := ⟨x.val, x.val_lt⟩
  have hi : (i.1 : ZMod 11) = x := by native_decide +revert
  have hneg : ((neg11 i).1 : ZMod 11) = -x := by native_decide +revert
  simpa [modulatedSquareClassSignal11, hi, hneg] using heven i

/-- The square-class exclusion stated on the formal normalized-even signal type. -/
private theorem zeroAutocorrSignal11_squareClass_contradiction
    (z : ZeroAutocorrSignal11) {c u v : ℂ}
    (hc : c ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (j t : ZMod 11)
    (hseed : ∀ x : Fin 11,
      z.signal x = c * modulatedSquareClassSignal11 u v j t x) : False := by
  apply modulatedSquareClassSignal11_not_even hu hv huv j t
  intro x
  apply mul_left_cancel₀ hc
  calc
    c * modulatedSquareClassSignal11 u v j t (neg11 x) =
        z.signal (neg11 x) := (hseed _).symm
    _ = z.signal x := z.even x
    _ = c * modulatedSquareClassSignal11 u v j t x := hseed x

/-- The square-class family with distinct residue and nonresidue values,
allowing translation, modulation, and projective rescaling. -/
def IsSquareClassFamily11 (z : ZeroAutocorrSignal11) : Prop :=
  ∃ c u v : ℂ, c ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
    ∃ j t : ZMod 11, ∀ x : Fin 11,
      z.signal x = c * modulatedSquareClassSignal11 u v j t x

/-- In particular, no normalized even biunimodular signal belongs to the
translated, modulated, projectively rescaled square-class family. -/
theorem zeroAutocorrSignal11_not_squareClassFamily (z : ZeroAutocorrSignal11) :
    ¬ IsSquareClassFamily11 z := by
  rintro ⟨c, u, v, hc, hu, hv, huv, j, t, hseed⟩
  exact zeroAutocorrSignal11_squareClass_contradiction z hc hu hv huv j t hseed

end Biunimodular.F11
