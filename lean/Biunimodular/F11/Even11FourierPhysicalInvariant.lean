/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PhaseInvariantOrbitSeparation11

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

/-!
# Physical Fourier invariant at length eleven

The calculation here is on actual even six-coordinate vectors and the
concrete normalized DFT.  On biunimodular vectors its hypotheses are the
normalization at zero and Fourier flatness at zero.
-/

/-- The zero-frequency real coefficient used by the physical orbit
classification, expressed directly on the even-vector model. -/
def even11PhysicalQ (h : Even6 ℂ) : ℝ :=
  (even11FourierNormalized h 0).re

def even11PhysicalU (h : Even6 ℂ) : ℝ :=
  even11PhysicalQ h ^ 2

/-- Fourier transform followed by normalization at coordinate zero. -/
def even11NormalizeFourier (h : Even6 ℂ) : Even6 ℂ :=
  (even11FourierNormalized h 0)⁻¹ • even11FourierNormalized h

/-- The normalized Fourier step restores the zero coordinate to one. -/
theorem even11NormalizeFourier_zero (h : Even6 ℂ)
    (hF0 : even11FourierNormalized h 0 ≠ 0) :
    even11NormalizeFourier h 0 = 1 := by
  simp [even11NormalizeFourier, hF0]

/-- For an even vector, applying the Fourier involution after normalization
returns the original vector divided by its zero-frequency coefficient. -/
theorem even11Fourier_normalizeFourier (h : Even6 ℂ) :
    even11FourierNormalized (even11NormalizeFourier h) =
      (even11FourierNormalized h 0)⁻¹ • h := by
  simp [even11NormalizeFourier, even11FourierNormalized_sq]

/-- The zero-frequency real coefficient survives normalized Fourier
transformation whenever the original and transformed zero coordinates have
modulus one. -/
theorem even11PhysicalQ_normalizeFourier
    (h : Even6 ℂ) (h0 : h 0 = 1)
    (hF0 : Complex.normSq (even11FourierNormalized h 0) = 1) :
    even11PhysicalQ (even11NormalizeFourier h) = even11PhysicalQ h := by
  have hconj : (even11FourierNormalized h 0)⁻¹ =
      star (even11FourierNormalized h 0) := by
    rw [Complex.inv_def, hF0]
    simp
  simp [even11PhysicalQ, even11Fourier_normalizeFourier,
    h0, hconj]

/-- In particular the squared physical quotient invariant is unchanged. -/
theorem even11PhysicalU_normalizeFourier
    (h : Even6 ℂ) (h0 : h 0 = 1)
    (hF0 : Complex.normSq (even11FourierNormalized h 0) = 1) :
    even11PhysicalU (even11NormalizeFourier h) = even11PhysicalU h := by
  rw [even11PhysicalU, even11PhysicalU,
    even11PhysicalQ_normalizeFourier h h0 hF0]

/-- For a vector normalized at zero, the vector-level coefficient is exactly
the physical phase-coordinate invariant. -/
theorem even11PhysicalQ_eq_phaseInvariantQ11
    (h : Even6 ℂ) (h0 : h 0 = 1) :
    even11PhysicalQ h = phaseInvariantQ11 (phaseCoordsOfEven11 h) := by
  have hsInv : (Real.sqrt 11 : ℂ)⁻¹ =
      ((Real.sqrt 11)⁻¹ : ℝ) := by
    exact_mod_cast rfl
  have hF : even11FourierNormalized h 0 =
      (Real.sqrt 11 : ℂ)⁻¹ *
        (1 + 2 * (h 1 + h 2 + h 3 + h 4 + h 5)) := by
    change (Real.sqrt 11 : ℂ)⁻¹ * even11Fourier h 0 = _
    rw [even11Fourier_zero, h0]
  rw [even11PhysicalQ, hF, hsInv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re, Complex.one_re]
  simp [phaseInvariantQ11, phaseCoordsOfEven11, h0]
  ring

/-- When both endpoints of the normalized Fourier step are physical phase
solutions, Fourier preservation of `u` and the exact eight-orbit
classification place them in the same concrete symmetry orbit. -/
theorem even11NormalizeFourier_same_phase_orbit
    (h : Even6 ℂ) (h0 : h 0 = 1)
    (hF0 : Complex.normSq (even11FourierNormalized h 0) = 1)
    (hphase : (phaseCoordsOfEven11 h).IsPhaseSolution)
    (hTphase :
      (phaseCoordsOfEven11 (even11NormalizeFourier h)).IsPhaseSolution) :
    ∃ g : EvenSymmetry11,
      (⟨phaseCoordsOfEven11 (even11NormalizeFourier h), hTphase⟩ :
        PhaseSolution11) =
        g • (⟨phaseCoordsOfEven11 h, hphase⟩ : PhaseSolution11) := by
  let s : PhaseSolution11 := ⟨phaseCoordsOfEven11 h, hphase⟩
  let t : PhaseSolution11 :=
    ⟨phaseCoordsOfEven11 (even11NormalizeFourier h), hTphase⟩
  have ht0 : even11NormalizeFourier h 0 = 1 := by
    apply even11NormalizeFourier_zero
    intro hz
    simp [hz] at hF0
  have hu : phaseInvariantU11 t.1 = phaseInvariantU11 s.1 := by
    change phaseInvariantU11
        (phaseCoordsOfEven11 (even11NormalizeFourier h)) =
      phaseInvariantU11 (phaseCoordsOfEven11 h)
    simp only [phaseInvariantU11]
    rw [← even11PhysicalQ_eq_phaseInvariantQ11 h h0,
      ← even11PhysicalQ_eq_phaseInvariantQ11
        (even11NormalizeFourier h) ht0]
    exact even11PhysicalU_normalizeFourier h h0 hF0
  have hq := (phaseSolution11_same_orbit_iff_u_eq t s).2 hu
  have hrel := Quotient.exact hq
  change MulAction.orbitRel EvenSymmetry11 PhaseSolution11 t s at hrel
  rw [MulAction.orbitRel_apply] at hrel
  rcases hrel with ⟨g, hg⟩
  exact ⟨g, hg.symm⟩

end

end Biunimodular.F11
