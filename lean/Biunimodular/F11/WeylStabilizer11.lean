/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PhaseSemanticCompletion11
import Biunimodular.F11.WeylStabilizerCore11

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar

/-- Read a length-eleven signal using field indices. -/
def signalOnZMod11 (z : ZeroAutocorrSignal11) (x : ZMod 11) : ℂ :=
  z.signal ⟨x.val, x.val_lt⟩

theorem signalOnZMod11_zero (z : ZeroAutocorrSignal11) :
    signalOnZMod11 z 0 = 1 := by
  simpa [signalOnZMod11] using z.normalized

theorem signalOnZMod11_even (z : ZeroAutocorrSignal11) (x : ZMod 11) :
    signalOnZMod11 z (-x) = signalOnZMod11 z x := by
  let i : Fin 11 := ⟨x.val, x.val_lt⟩
  have hneg : (neg11 i).1 = (-x).val := by native_decide +revert
  have heq : neg11 i = (⟨(-x).val, (-x).val_lt⟩ : Fin 11) :=
    Fin.ext hneg
  change z.signal ⟨(-x).val, (-x).val_lt⟩ = z.signal i
  rw [← heq]
  exact z.even i

theorem signalOnZMod11_ne_zero (z : ZeroAutocorrSignal11) (x : ZMod 11) :
    signalOnZMod11 z x ≠ 0 := by
  intro hzero
  have hnorm := z.normSq_one ⟨x.val, x.val_lt⟩
  change Complex.normSq (signalOnZMod11 z x) = 1 at hnorm
  simp [hzero] at hnorm

theorem signalOnZMod11_gaussian_iff (z : ZeroAutocorrSignal11) (q : ZMod 11) :
    (∀ x : ZMod 11, signalOnZMod11 z x = stdAddChar (q * x ^ 2)) ↔
      (∀ t : Fin 11,
        z.signal t = stdAddChar (q * (t.1 : ZMod 11) ^ 2)) := by
  constructor
  · intro h t
    have ht := h (t.1 : ZMod 11)
    simpa [signalOnZMod11, ZMod.val_cast_of_lt t.isLt] using ht
  · intro h x
    simpa [signalOnZMod11, ZMod.natCast_zmod_val] using
      h ⟨x.val, x.val_lt⟩

theorem signalOnZMod11_quadratic_nonzero
    (z : ZeroAutocorrSignal11) (q : ZMod 11)
    (hquad : ∀ x : ZMod 11,
      signalOnZMod11 z x = stdAddChar (q * x ^ 2)) : q ≠ 0 := by
  intro hq
  have hall : ∀ t : Fin 11, z.signal t = 1 := by
    intro t
    have ht := (signalOnZMod11_gaussian_iff z q).mp hquad t
    simpa [hq] using ht
  have hcorr := z.zero_autocorr (1 : Fin 11) (by decide)
  simp [autocorr11, hall] at hcorr

/-- A projective Weyl stabilizer with nonzero translation forces the genuine
quadratic-Gaussian family on a normalized even biunimodular signal. -/
theorem signal11_gaussian_of_weyl_stabilizer
    (z : ZeroAutocorrSignal11) (a b : ZMod 11) (ha : a ≠ 0) (c : ℂ)
    (hst : ∀ x : ZMod 11,
      stdAddChar (b * x) * signalOnZMod11 z (x + a) =
        c * signalOnZMod11 z x) :
    IsQuadraticGaussianSignal11 z := by
  obtain ⟨q, hquad⟩ := even_weyl_is_quadratic
    (signalOnZMod11 z) (signalOnZMod11_zero z)
    (signalOnZMod11_even z) (signalOnZMod11_ne_zero z)
    a b ha c hst
  exact ⟨q, signalOnZMod11_quadratic_nonzero z q hquad,
    (signalOnZMod11_gaussian_iff z q).mp hquad⟩

/-- The only Weyl labels stabilizing a non-Gaussian even signal projectively
are the identity labels. -/
theorem signal11_weyl_stabilizer_trivial
    (z : ZeroAutocorrSignal11)
    (hNonG : ¬ IsQuadraticGaussianSignal11 z)
    (a b : ZMod 11) (c : ℂ)
    (hst : ∀ x : ZMod 11,
      stdAddChar (b * x) * signalOnZMod11 z (x + a) =
        c * signalOnZMod11 z x) :
    a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra hne
    exact hNonG (signal11_gaussian_of_weyl_stabilizer z a b hne c hst)
  have hc : c = 1 := by
    have hzero := hst 0
    simpa [ha, signalOnZMod11_zero] using hzero.symm
  have hchar : (stdAddChar b : ℂ) = 1 := by
    have hone := hst 1
    have hs : stdAddChar b * signalOnZMod11 z 1 =
        1 * signalOnZMod11 z 1 := by simpa [ha, hc] using hone
    exact mul_right_cancel₀ (signalOnZMod11_ne_zero z 1) hs
  have hb : b = 0 := by
    apply ZMod.injective_stdAddChar
    simpa using hchar
  exact ⟨ha, hb⟩

end Biunimodular.F11
