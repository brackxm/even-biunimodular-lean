/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ProofTactics
import Mathlib.Analysis.Real.Sqrt
import Biunimodular.F11.PhaseSymmetry11

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# The physical quotient invariant on p = 11 phase solutions

The real part of the unitary Fourier coefficient at zero is

`q = (1 + 2 * (a + c + e + g + j)) / sqrt 11`,

and the physical orbit invariant is `u = q²`.  This file proves directly
from the phase equations that `0 ≤ u ≤ 1` and proves that `u` descends
through the concrete dilation/conjugation action.
-/

/-- The real part of the unitary zero-frequency Fourier coefficient. -/
noncomputable def phaseInvariantQ11 (x : PhaseCoords11) : ℝ :=
  (1 + 2 * (x.a + x.c + x.e + x.g + x.j)) / Real.sqrt 11

/-- The squared physical invariant used to label the eight `H`-orbits. -/
noncomputable def phaseInvariantU11 (x : PhaseCoords11) : ℝ :=
  phaseInvariantQ11 x ^ 2

@[simp] theorem phaseInvariantQ11_dilate (x : PhaseCoords11) :
    phaseInvariantQ11 (phaseDilate11 x) = phaseInvariantQ11 x := by
  simp only [phaseInvariantQ11, phaseDilate11]
  ring

@[simp] theorem phaseInvariantQ11_conjugate (x : PhaseCoords11) :
    phaseInvariantQ11 (phaseConjugate11 x) = phaseInvariantQ11 x := by
  rfl

private theorem phaseInvariantQ11_dilation_pow
    (n : ℕ) (x : PhaseCoords11) :
    phaseInvariantQ11 ((phaseDilationGenerator11 ^ n) • x) =
      phaseInvariantQ11 x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_smul, phaseDilationGenerator11_smul,
        phaseInvariantQ11_dilate, ih]

private theorem phaseInvariantQ11_conjugation_pow
    (n : ℕ) (x : PhaseCoords11) :
    phaseInvariantQ11 ((phaseConjugationGenerator11 ^ n) • x) =
      phaseInvariantQ11 x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_smul, phaseConjugationGenerator11_smul,
        phaseInvariantQ11_conjugate, ih]

/-- `q` is invariant under every normalized even symmetry. -/
theorem phaseInvariantQ11_smul
    (g : EvenSymmetry11) (x : PhaseCoords11) :
    phaseInvariantQ11 (g • x) = phaseInvariantQ11 x := by
  rw [evenSymmetry11_generator_decomposition g, mul_smul,
    phaseInvariantQ11_dilation_pow, phaseInvariantQ11_conjugation_pow]

/-- `u = q²` is invariant under every normalized even symmetry. -/
theorem phaseInvariantU11_smul
    (g : EvenSymmetry11) (x : PhaseCoords11) :
    phaseInvariantU11 (g • x) = phaseInvariantU11 x := by
  simp [phaseInvariantU11, phaseInvariantQ11_smul]

/-- The phase equations force the squared modulus of the zero-frequency
Fourier numerator to be exactly `11`. -/
theorem phaseInvariant11_components_identity
    (x : PhaseCoords11) (hs : x.IsPhaseSolution) :
    (1 + 2 * (x.a + x.c + x.e + x.g + x.j)) ^ 2 +
      (2 * (x.b + x.d + x.f + x.h + x.k)) ^ 2 = 11 := by
  rcases hs with ⟨⟨hab, hcd, hef, hgh, hjk⟩, h1, h2, h3, h4, h5⟩
  simp only [PhaseCoords11.E1] at h1
  simp only [PhaseCoords11.E2] at h2
  simp only [PhaseCoords11.E3] at h3
  simp only [PhaseCoords11.E4] at h4
  simp only [PhaseCoords11.E5] at h5
  nlinarith

/-- Every physical phase solution has an admissible invariant value
`0 ≤ u ≤ 1`. -/
theorem phaseInvariantU11_mem_unitInterval
    (x : PhaseCoords11) (hs : x.IsPhaseSolution) :
    0 ≤ phaseInvariantU11 x ∧ phaseInvariantU11 x ≤ 1 := by
  have hsqrt : (Real.sqrt 11) ^ 2 = 11 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11)]
  have hcomponents := phaseInvariant11_components_identity x hs
  have hnum :
      (1 + 2 * (x.a + x.c + x.e + x.g + x.j)) ^ 2 ≤ 11 := by
    nlinarith [sq_nonneg (2 * (x.b + x.d + x.f + x.h + x.k))]
  constructor
  · exact sq_nonneg _
  · rw [phaseInvariantU11, phaseInvariantQ11, div_pow, hsqrt]
    exact (div_le_one (by norm_num : (0 : ℝ) < 11)).2 hnum

/-- The orbit space of normalized even phase solutions under dilation and
conjugation. -/
abbrev PhaseSolution11Orbit :=
  MulAction.orbitRel.Quotient EvenSymmetry11 PhaseSolution11

/-- The physical invariant descended to the actual symmetry quotient. -/
noncomputable def phaseSolution11OrbitInvariantU : PhaseSolution11Orbit → ℝ :=
  Quotient.lift (fun s : PhaseSolution11 => phaseInvariantU11 s.1) (by
    intro a b hab
    rcases hab with ⟨g, rfl⟩
    exact phaseInvariantU11_smul g b.1)

@[simp] theorem phaseSolution11OrbitInvariantU_mk (s : PhaseSolution11) :
    phaseSolution11OrbitInvariantU (Quotient.mk'' s) =
      phaseInvariantU11 s.1 :=
  rfl

end Biunimodular.F11
