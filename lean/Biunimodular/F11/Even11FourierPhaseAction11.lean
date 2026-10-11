/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FourierPhysicalInvariant

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Biunimodular.F11

open ZMod
open scoped ComplexConjugate

noncomputable section

/-- The full field-indexed signal of a physical phase solution. -/
def phaseOnZMod11 (x : PhaseCoords11) (t : ZMod 11) : ℂ :=
  phaseSignal11 x ⟨t.val, t.val_lt⟩

theorem phaseOnZMod11_zero (x : PhaseCoords11) :
    phaseOnZMod11 x 0 = 1 := by
  rfl

theorem phaseOnZMod11_even (x : PhaseCoords11) :
    Function.Even (phaseOnZMod11 x) := by
  intro t
  have hneg :
      neg11 (⟨t.val, t.val_lt⟩ : Fin 11) =
        ⟨(-t).val, (-t).val_lt⟩ := by
    apply Fin.ext
    native_decide +revert
  change phaseSignal11 x ⟨(-t).val, (-t).val_lt⟩ =
    phaseSignal11 x ⟨t.val, t.val_lt⟩
  rw [← hneg]
  exact phaseSignal11_even x _

theorem phaseOnZMod11_normSq_one
    (s : PhaseSolution11) (t : ZMod 11) :
    Complex.normSq (phaseOnZMod11 s.1 t) = 1 := by
  exact phaseSignal11_normSq_one s.1 s.2.1 _

/-- The phase equations force the cyclic autocorrelation to be the eleven
point delta function, including its value at zero. -/
theorem phaseOnZMod11_autocorrelation
    (s : PhaseSolution11) (r : ZMod 11) :
    cyclicAutocorrelation11 (phaseOnZMod11 s.1) r =
      if r = 0 then 11 else 0 := by
  by_cases hr : r = 0
  · subst r
    simp only [cyclicAutocorrelation11, add_zero, ite_true]
    have hterm (t : ZMod 11) :
        phaseOnZMod11 s.1 t * star (phaseOnZMod11 s.1 t) =
          (1 : ℂ) := by
      rw [mul_comm]
      change conj (phaseOnZMod11 s.1 t) * phaseOnZMod11 s.1 t = 1
      rw [← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast phaseOnZMod11_normSq_one s t
    simp_rw [hterm]
    simp
  · have hrfin : (⟨r.val, r.val_lt⟩ : Fin 11) ≠ 0 := by
      intro hz
      apply hr
      have hv := congrArg Fin.val hz
      apply ZMod.val_injective 11
      simpa using hv
    have hzero := phaseSolution_all_nonzero_autocorr_zero s.1 s.2
      ⟨r.val, r.val_lt⟩ hrfin
    have hbridge := autocorr11_eq_cyclicAutocorrelation11
      (phaseSignal11 s.1) ⟨r.val, r.val_lt⟩
    have hfunc :
        (fun t : ZMod 11 => phaseSignal11 s.1 t) = phaseOnZMod11 s.1 := by
      funext t
      rfl
    rw [hfunc] at hbridge
    have hcast : ((⟨r.val, r.val_lt⟩ : Fin 11) : ZMod 11) = r := by
      rfl
    rw [hcast] at hbridge
    simpa [hr] using hbridge.symm.trans hzero

/-- Every Fourier coefficient of a physical phase solution has squared
modulus eleven before unitary normalization. -/
theorem phaseOnZMod11_dft_normSq
    (s : PhaseSolution11) (k : ZMod 11) :
    Complex.normSq (ZMod.dft (phaseOnZMod11 s.1) k) = 11 := by
  have hWK := dft_cyclicAutocorrelation11 (phaseOnZMod11 s.1) k
  rw [show cyclicAutocorrelation11 (phaseOnZMod11 s.1) =
    (fun r : ZMod 11 => if r = 0 then (11 : ℂ) else 0) from by
      funext r
      exact phaseOnZMod11_autocorrelation s r] at hWK
  simp [ZMod.dft_apply] at hWK
  exact_mod_cast hWK.symm

/-- The six independent values of the physical phase vector. -/
def phaseEvenVector11 (s : PhaseSolution11) : Even6 ℂ :=
  even11Restrict (phaseOnZMod11 s.1)

@[simp] theorem phaseEvenVector11_zero (s : PhaseSolution11) :
    phaseEvenVector11 s 0 = 1 := by
  exact phaseOnZMod11_zero s.1

theorem phaseEvenVector11_lift (s : PhaseSolution11) :
    even11Lift (phaseEvenVector11 s) = phaseOnZMod11 s.1 := by
  exact even11Lift_restrict_of_even _ (phaseOnZMod11_even s.1)

private theorem fin11_zmod_cast (t : Fin 11) :
    (t.1 : ZMod 11) = (t : ZMod 11) := by
  exact Fin.cast_val_eq_self t

theorem phaseCoordsOfEven11_phaseEvenVector11 (s : PhaseSolution11) :
    phaseCoordsOfEven11 (phaseEvenVector11 s) = s.1 := by
  have hpoint (i : Fin 6) :
      phaseEvenVector11 s i =
        phaseSignal11 s.1 ⟨i.val, by omega⟩ := by
    change phaseSignal11 s.1
        ⟨((i.val : ZMod 11)).val, _⟩ = _
    congr 1
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (by omega : i.val < 11)
  rcases s with ⟨x, hx⟩
  cases x
  simp [phaseCoordsOfEven11, hpoint,
    phaseSignal11, phaseC]

/-- The unitary Fourier transform of every physical phase vector is flat at
all eleven frequencies. -/
theorem phaseEvenVector11_fourier_normSq_one
    (s : PhaseSolution11) (k : ZMod 11) :
    Complex.normSq
        (even11Lift (even11FourierNormalized (phaseEvenVector11 s)) k) = 1 := by
  have hscale : Complex.normSq ((Real.sqrt 11 : ℂ)⁻¹) = (11 : ℝ)⁻¹ := by
    simp
  have hflat := phaseOnZMod11_dft_normSq s k
  have hFourier :
      even11Lift (even11FourierNormalized (phaseEvenVector11 s)) k =
        (Real.sqrt 11 : ℂ)⁻¹ *
          ZMod.dft (phaseOnZMod11 s.1) k := by
    have hl := congrFun (even11Lift_fourier (phaseEvenVector11 s)) k
    change even11Fourier (phaseEvenVector11 s) (even11Coordinate k) =
      ZMod.dft (even11Lift (phaseEvenVector11 s)) k at hl
    change (Real.sqrt 11 : ℂ)⁻¹ *
      even11Fourier (phaseEvenVector11 s) (even11Coordinate k) = _
    rw [hl, phaseEvenVector11_lift]
  rw [hFourier, Complex.normSq_mul, hscale, hflat]
  norm_num

/-- Fourier normalization maps every physical phase solution to a physical
phase solution.  This is the signal-level closure needed by the full orbit
argument. -/
theorem phaseEvenVector11_normalizedFourier_isPhaseSolution
    (s : PhaseSolution11) :
    (phaseCoordsOfEven11
      (even11NormalizeFourier (phaseEvenVector11 s))).IsPhaseSolution := by
  let h : Even6 ℂ := phaseEvenVector11 s
  let g : Even6 ℂ := even11NormalizeFourier h
  let gamma : ℂ := even11FourierNormalized h 0
  have hgamma : Complex.normSq gamma = 1 := by
    simpa [gamma, h, even11Lift_apply, even11Coordinate_zero] using
      phaseEvenVector11_fourier_normSq_one s 0
  have hgamma0 : gamma ≠ 0 := by
    intro hz
    simp [hz] at hgamma
  have hg0 : g 0 = 1 := even11NormalizeFourier_zero h hgamma0
  have htime (k : ZMod 11) :
      Complex.normSq (even11Lift g k) = 1 := by
    have hF := phaseEvenVector11_fourier_normSq_one s k
    change Complex.normSq (even11Lift
      (even11FourierNormalized h) k) = 1 at hF
    have hvalue : even11Lift g k =
        gamma⁻¹ * even11Lift (even11FourierNormalized h) k := rfl
    rw [hvalue, Complex.normSq_mul, Complex.normSq_inv, hgamma, hF]
    norm_num
  have hFourierRaw (k : ZMod 11) :
      ZMod.dft (even11Lift g) k =
        (Real.sqrt 11 : ℂ) * gamma⁻¹ * even11Lift h k := by
    have hsqrt : (Real.sqrt 11 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 11)).ne'
    have hLift := congrFun (even11Lift_fourier g) k
    have hNorm := congrFun (even11Fourier_normalizeFourier h) (even11Coordinate k)
    change even11FourierNormalized g (even11Coordinate k) =
      gamma⁻¹ * h (even11Coordinate k) at hNorm
    have hRaw : even11Fourier g (even11Coordinate k) =
        (Real.sqrt 11 : ℂ) * gamma⁻¹ * h (even11Coordinate k) := by
      calc
        even11Fourier g (even11Coordinate k) =
            (Real.sqrt 11 : ℂ) *
              even11FourierNormalized g (even11Coordinate k) := by
                simp [even11FourierNormalized, hsqrt]
        _ = (Real.sqrt 11 : ℂ) *
              (gamma⁻¹ * h (even11Coordinate k)) := by rw [hNorm]
        _ = _ := by ring
    change even11Fourier g (even11Coordinate k) =
      ZMod.dft (even11Lift g) k at hLift
    rw [← hLift, hRaw]
    rfl
  have hFourierFlat (k : ZMod 11) :
      Complex.normSq (ZMod.dft (even11Lift g) k) = 11 := by
    have hnormh : Complex.normSq (even11Lift h k) = 1 := by
      rw [phaseEvenVector11_lift]
      exact phaseOnZMod11_normSq_one s k
    have hsqrt : Complex.normSq (Real.sqrt 11 : ℂ) = 11 := by
      simp
    rw [hFourierRaw k, Complex.normSq_mul, Complex.normSq_mul,
      hsqrt, Complex.normSq_inv, hgamma, hnormh]
    norm_num
  have hphaseSignal (t : Fin 11) :
      phaseSignal11 (phaseCoordsOfEven11 g) t =
        even11Lift g (t.1 : ZMod 11) := by
    rw [phaseSignal11_phaseCoordsOfEven11 g (by simp [hg0]) t]
    simp [hg0]
  apply isPhaseSolution_of_normSq_autocorr11
  · intro t
    rw [hphaseSignal]
    exact htime (t.1 : ZMod 11)
  · intro r hr
    have hzero := cyclicAutocorrelation11_eq_zero_of_dft_normSq
      (even11Lift g) hFourierFlat (r.1 : ZMod 11) (by
        intro hz
        apply hr
        apply Fin.ext
        have hv := congrArg ZMod.val hz
        simp only [ZMod.val_natCast_of_lt r.isLt, ZMod.val_zero] at hv
        change r.val = 0
        exact hv)
    rw [autocorr11_eq_cyclicAutocorrelation11]
    have hfunc :
        (fun t : ZMod 11 => phaseSignal11 (phaseCoordsOfEven11 g) t) =
          even11Lift g := by
      funext t
      fin_cases t <;>
        (convert hphaseSignal _ using 1; congr 1)
    rw [hfunc]
    simpa only [fin11_zmod_cast] using hzero

/-- Normalized unitary Fourier transform on the actual physical phase
solution type. -/
def phaseSolution11Fourier (s : PhaseSolution11) : PhaseSolution11 :=
  ⟨phaseCoordsOfEven11
      (even11NormalizeFourier (phaseEvenVector11 s)),
    phaseEvenVector11_normalizedFourier_isPhaseSolution s⟩

/-- The concrete normalized Fourier step stays in the same ten-element
dilation/conjugation orbit of a physical phase solution. -/
theorem phaseSolution11_normalizedFourier_same_orbit
    (s : PhaseSolution11) :
    ∃ g : EvenSymmetry11,
      phaseSolution11Fourier s = g • s := by
  have hF0 : Complex.normSq
      (even11FourierNormalized (phaseEvenVector11 s) 0) = 1 := by
    simpa [even11Lift_apply, even11Coordinate_zero] using
      phaseEvenVector11_fourier_normSq_one s 0
  have hphase : (phaseCoordsOfEven11 (phaseEvenVector11 s)).IsPhaseSolution := by
    rw [phaseCoordsOfEven11_phaseEvenVector11]
    exact s.2
  obtain ⟨g, hg⟩ := even11NormalizeFourier_same_phase_orbit
    (phaseEvenVector11 s) (phaseEvenVector11_zero s) hF0 hphase
    (phaseEvenVector11_normalizedFourier_isPhaseSolution s)
  have hs : (⟨phaseCoordsOfEven11 (phaseEvenVector11 s), hphase⟩ :
      PhaseSolution11) = s := by
    apply Subtype.ext
    exact phaseCoordsOfEven11_phaseEvenVector11 s
  rw [hs] at hg
  exact ⟨g, hg⟩

/-- The physical invariant is unchanged by the concrete normalized Fourier
operator on phase solutions. -/
theorem phaseSolution11Fourier_invariantU (s : PhaseSolution11) :
    phaseInvariantU11 (phaseSolution11Fourier s).1 =
      phaseInvariantU11 s.1 := by
  obtain ⟨g, hg⟩ := phaseSolution11_normalizedFourier_same_orbit s
  rw [hg]
  exact phaseInvariantU11_smul g s.1

end

end Biunimodular.F11
