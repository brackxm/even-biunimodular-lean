/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.WeylStabilizer11

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- A projective Weyl transformation between two normalized even
non-Gaussian signals has trivial translation and modulation labels. -/
theorem nonGaussian_even_weyl_relation_trivial
    (z w : ZeroAutocorrSignal11)
    (hNonG : ¬ IsQuadraticGaussianSignal11 z)
    (a b : ZMod 11) (c : ℂ)
    (h : ∀ x : ZMod 11,
      stdAddChar (b * x) * signalOnZMod11 z (x + a) =
        c * signalOnZMod11 w x) :
    a = 0 ∧ b = 0 := by
  let f := signalOnZMod11 z
  let g := signalOnZMod11 w
  have hpair (x : ZMod 11) :
      stdAddChar (b * (x + a)) * f (x + 2 * a) =
        stdAddChar (-(b * (x + a))) * f x := by
    have hpos := h (x + a)
    have hneg := h (-(x + a))
    have hevenf := signalOnZMod11_even z x
    have heveng := signalOnZMod11_even w (x + a)
    dsimp [f, g] at *
    convert hpos.trans ((congrArg (fun t : ℂ => c * t) heveng).symm.trans hneg.symm) using 1 <;>
      (try ring); simp [hevenf]
  let d : ℂ := stdAddChar (2 * b * a)
  have hd : d ≠ 0 := by
    dsimp [d]
    rw [ZMod.stdAddChar_apply]
    exact Circle.coe_ne_zero _
  have hst (x : ZMod 11) :
      stdAddChar ((2 * b) * x) * f (x + 2 * a) = d⁻¹ * f x := by
    have hp := hpair x
    have hsq : (stdAddChar (b * (x + a)) : ℂ) ^ 2 * f (x + 2 * a) = f x := by
      calc
        _ = stdAddChar (b * (x + a)) *
            (stdAddChar (b * (x + a)) * f (x + 2 * a)) := by ring
        _ = stdAddChar (b * (x + a)) *
            (stdAddChar (-(b * (x + a))) * f x) := by rw [hp]
        _ = f x := by rw [← mul_assoc, ← map_add_eq_mul]; simp
    have hdouble : (stdAddChar (b * (x + a)) : ℂ) ^ 2 =
        d * stdAddChar ((2 * b) * x) := by
      rw [pow_two, ← map_add_eq_mul, ← map_add_eq_mul]
      congr 1
      ring
    rw [hdouble] at hsq
    apply mul_left_cancel₀ hd
    calc
      d * (stdAddChar ((2 * b) * x) * f (x + 2 * a)) = f x := by
        simpa only [mul_assoc] using hsq
      _ = d * (d⁻¹ * f x) := by simp [hd]
  have hlabels := signal11_weyl_stabilizer_trivial z hNonG
    (2 * a) (2 * b) d⁻¹ hst
  have htwo : (2 : ZMod 11) ≠ 0 := by decide
  constructor
  · apply mul_left_cancel₀ htwo
    simpa using hlabels.1
  · apply mul_left_cancel₀ htwo
    simpa using hlabels.2

/-- Projectively, no Weyl transformation relates two distinct normalized
even non-Gaussian signals. -/
theorem nonGaussian_even_weyl_relation_eq
    (z w : ZeroAutocorrSignal11)
    (hNonG : ¬ IsQuadraticGaussianSignal11 z)
    (a b : ZMod 11) (c : ℂ)
    (h : ∀ x : ZMod 11,
      stdAddChar (b * x) * signalOnZMod11 z (x + a) =
        c * signalOnZMod11 w x) :
    (∀ x : ZMod 11, signalOnZMod11 z x = signalOnZMod11 w x) := by
  obtain ⟨ha, hb⟩ := nonGaussian_even_weyl_relation_trivial z w hNonG a b c h
  have hc : c = 1 := by
    have hzero := h 0
    simpa [ha, hb, signalOnZMod11_zero] using hzero.symm
  intro x
  have hx := h x
  simpa [ha, hb, hc] using hx

end Biunimodular.F11
