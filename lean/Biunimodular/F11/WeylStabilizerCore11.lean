/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ProofTactics
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-!
The nonzero-translation case of the projective Weyl stabilizer lemma.
Evenness fixes the scalar at the edge `5a -> 6a = -5a`.  The recurrence then
identifies the signal with a quadratic additive character on the entire cyclic
group.  The finite field identities are checked directly at modulus eleven.
-/

theorem five_edge (a : ZMod 11) :
    (5 : ZMod 11) * a + a = -((5 : ZMod 11) * a) := by
  native_decide +revert

theorem quadratic_coeff_id (a b : ZMod 11) (ha : a ≠ 0) :
    ((5 : ZMod 11) * b * a⁻¹) * a ^ 2 = 5 * b * a ∧
    b + 2 * ((5 : ZMod 11) * b * a⁻¹) * a = 0 := by
  native_decide +revert

/-- An even nowhere-zero normalized function stabilized by a nonzero Weyl
translation is a quadratic additive character. -/
theorem even_weyl_is_quadratic
    (f : ZMod 11 → ℂ) (hf0 : f 0 = 1)
    (hfeven : ∀ x : ZMod 11, f (-x) = f x)
    (hfnz : ∀ x : ZMod 11, f x ≠ 0)
    (a b : ZMod 11) (ha : a ≠ 0) (c : ℂ)
    (hst : ∀ x : ZMod 11,
      stdAddChar (b * x) * f (x + a) = c * f x) :
    ∃ q : ZMod 11, ∀ x : ZMod 11,
      f x = stdAddChar (q * x ^ 2) := by
  let q : ZMod 11 := 5 * b * a⁻¹
  let g : ZMod 11 → ℂ := fun x => stdAddChar (q * x ^ 2)
  have hc : c = stdAddChar (5 * b * a) := by
    have hs := hst (5 * a)
    rw [five_edge, hfeven] at hs
    have hcancel : stdAddChar (b * (5 * a)) = c :=
      mul_right_cancel₀ (hfnz (5 * a)) hs
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcancel.symm
  have hq_a : q * a ^ 2 = 5 * b * a := (quadratic_coeff_id a b ha).1
  have hcross : b + 2 * q * a = 0 := (quadratic_coeff_id a b ha).2
  have hg (x : ZMod 11) :
      stdAddChar (b * x) * g (x + a) =
        stdAddChar (5 * b * a) * g x := by
    dsimp [g]
    rw [← map_add_eq_mul, ← map_add_eq_mul]
    congr 1
    calc
      b * x + q * (x + a) ^ 2 =
          q * x ^ 2 + (b + 2 * q * a) * x + q * a ^ 2 := by ring
      _ = q * x ^ 2 + q * a ^ 2 := by rw [hcross]; ring
      _ = q * x ^ 2 + 5 * b * a := by rw [hq_a]
      _ = 5 * b * a + q * x ^ 2 := by ring
  have hstep (x : ZMod 11) (heq : f x = g x) : f (x + a) = g (x + a) := by
    have hf := hst x
    rw [hc, heq] at hf
    have hchar : (stdAddChar (b * x) : ℂ) ≠ 0 := by
      rw [ZMod.stdAddChar_apply]
      exact Circle.coe_ne_zero _
    exact mul_left_cancel₀ hchar (hf.trans (hg x).symm)
  have hnat : ∀ n : ℕ, f ((n : ZMod 11) * a) = g ((n : ZMod 11) * a) := by
    intro n
    induction n with
    | zero => simpa [g] using hf0
    | succ n ih =>
      have hs := hstep ((n : ZMod 11) * a) ih
      have heq : (((n + 1 : ℕ) : ZMod 11) * a) = (n : ZMod 11) * a + a := by
        push_cast
        ring
      simpa only [heq] using hs
  refine ⟨q, ?_⟩
  intro x
  have hrepr : (((x * a⁻¹).val : ZMod 11) * a) = x := by
    rw [ZMod.natCast_zmod_val]
    field_simp [ha]
  have h := hnat (x * a⁻¹).val
  rw [hrepr] at h
  simpa [g] using h

end Biunimodular.F11
