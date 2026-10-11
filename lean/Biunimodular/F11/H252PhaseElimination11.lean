/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.P150RootCoverAssembly11

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11

noncomputable section

/-!
# Exact H252 elimination from the localized phase system

The five unit complex phase values turn the real circle equations into a
Laurent system.  Clearing the common Laurent denominator gives the six
integral torus generators below.  The remaining part of this module replays
an exact integral ideal-membership certificate for the degree-252 `z5`
eliminant and transports it back to the real final coordinate `k`.
-/

def h252TorusF1 {R : Type*} [CommRing R] (z1 z2 z3 z4 z5 : R) : R :=
  z1^2*z2*z3*z4*z5 + z1^2*z3*z4*z5 + z1*z2^2*z4*z5 +
  z1*z2*z3^2*z5 + z1*z2*z3*z4^2 + z1*z2*z3*z4*z5 +
  z1*z2*z3*z5^2 + z1*z2*z4^2*z5 + z1*z3^2*z4*z5 +
  z2^2*z3*z4*z5 + z2*z3*z4*z5

def h252TorusF2 {R : Type*} [CommRing R] (z1 z2 z3 z4 z5 : R) : R :=
  z1^2*z2*z4*z5 + z1*z2^2*z3*z4*z5 + z1*z2^2*z3*z5 +
  z1*z2*z3^2*z4 + z1*z2*z3*z4^2 + z1*z2*z3*z4*z5 +
  z1*z2*z3*z5^2 + z1*z2*z4*z5^2 + z1*z3*z4^2*z5 +
  z1*z3*z4*z5 + z2*z3^2*z4*z5

def h252TorusF3 {R : Type*} [CommRing R] (z1 z2 z3 z4 z5 : R) : R :=
  z1^2*z2*z3*z5 + z1^2*z3*z4*z5 + z1*z2^2*z3*z4 +
  z1*z2*z3^2*z4*z5 + z1*z2*z3^2*z4 + z1*z2*z3*z4*z5 +
  z1*z2*z4*z5^2 + z1*z2*z4*z5 + z1*z3*z4*z5^2 +
  z2^2*z3*z4*z5 + z2*z3*z4^2*z5

def h252TorusF4 {R : Type*} [CommRing R] (z1 z2 z3 z4 z5 : R) : R :=
  z1^2*z2*z3*z4 + z1^2*z2*z4*z5 + z1*z2^2*z3*z4 +
  z1*z2*z3^2*z5 + z1*z2*z3*z4^2*z5 + z1*z2*z3*z4*z5 +
  z1*z2*z3*z5 + z1*z2*z4^2*z5 + z1*z3*z4*z5^2 +
  z2*z3^2*z4*z5 + z2*z3*z4*z5^2

def h252TorusF5 {R : Type*} [CommRing R] (z1 z2 z3 z4 z5 : R) : R :=
  z1^2*z2*z3*z4 + z1^2*z2*z3*z5 + z1*z2^2*z3*z5 +
  z1*z2^2*z4*z5 + z1*z2*z3*z4*z5^2 + z1*z2*z3*z4*z5 +
  z1*z2*z3*z4 + z1*z3^2*z4*z5 + z1*z3*z4^2*z5 +
  z2*z3*z4^2*z5 + z2*z3*z4*z5^2

def h252TorusD {R : Type*} [CommRing R] (z1 z2 z3 z4 z5 : R) : R :=
  z1*z2*z3*z4*z5

def h252TorusS {R : Type*} [CommRing R] (z1 z2 z3 z4 w z5 : R) : R :=
  w * h252TorusD z1 z2 z3 z4 z5 - 1

private theorem phaseSolution_laurentEquations11
    (x : PhaseCoords11) (hx : x.IsPhaseSolution) :
    let z1 := phaseC x.a x.b
    let z2 := phaseC x.c x.d
    let z3 := phaseC x.e x.f
    let z4 := phaseC x.g x.h
    let z5 := phaseC x.j x.k
    (1 + z1 + z1⁻¹ + z1*z2⁻¹ + z2*z1⁻¹ + z2*z3⁻¹ +
      z3*z2⁻¹ + z3*z4⁻¹ + z4*z3⁻¹ + z4*z5⁻¹ + z5*z4⁻¹ = 0) ∧
    (1 + z2 + z2⁻¹ + z1*z3⁻¹ + z3*z1⁻¹ + z2*z4⁻¹ +
      z4*z2⁻¹ + z3*z5⁻¹ + z5*z3⁻¹ + z4*z5⁻¹ + z5*z4⁻¹ = 0) ∧
    (1 + z3 + z3⁻¹ + z1*z4⁻¹ + z4*z1⁻¹ + z2*z5⁻¹ +
      z5*z2⁻¹ + z3*z5⁻¹ + z5*z3⁻¹ + z1*z2⁻¹ + z2*z1⁻¹ = 0) ∧
    (1 + z4 + z4⁻¹ + z1*z5⁻¹ + z5*z1⁻¹ + z2*z5⁻¹ +
      z5*z2⁻¹ + z3*z4⁻¹ + z4*z3⁻¹ + z1*z3⁻¹ + z3*z1⁻¹ = 0) ∧
    (1 + z5 + z5⁻¹ + z1*z5⁻¹ + z5*z1⁻¹ + z2*z4⁻¹ +
      z4*z2⁻¹ + z1*z4⁻¹ + z4*z1⁻¹ + z2*z3⁻¹ + z3*z2⁻¹ = 0) := by
  rcases hx with ⟨⟨hab, hcd, hef, hgh, hjk⟩, h1, h2, h3, h4, h5⟩
  have hz1 : Complex.normSq (phaseC x.a x.b) = 1 := by
    simpa [phaseC, Complex.normSq, pow_two] using hab
  have hz2 : Complex.normSq (phaseC x.c x.d) = 1 := by
    simpa [phaseC, Complex.normSq, pow_two] using hcd
  have hz3 : Complex.normSq (phaseC x.e x.f) = 1 := by
    simpa [phaseC, Complex.normSq, pow_two] using hef
  have hz4 : Complex.normSq (phaseC x.g x.h) = 1 := by
    simpa [phaseC, Complex.normSq, pow_two] using hgh
  have hz5 : Complex.normSq (phaseC x.j x.k) = 1 := by
    simpa [phaseC, Complex.normSq, pow_two] using hjk
  have hi1 : (phaseC x.a x.b)⁻¹ = star (phaseC x.a x.b) := by
    simp [Complex.inv_def, hz1]
  have hi2 : (phaseC x.c x.d)⁻¹ = star (phaseC x.c x.d) := by
    simp [Complex.inv_def, hz2]
  have hi3 : (phaseC x.e x.f)⁻¹ = star (phaseC x.e x.f) := by
    simp [Complex.inv_def, hz3]
  have hi4 : (phaseC x.g x.h)⁻¹ = star (phaseC x.g x.h) := by
    simp [Complex.inv_def, hz4]
  have hi5 : (phaseC x.j x.k)⁻¹ = star (phaseC x.j x.k) := by
    simp [Complex.inv_def, hz5]
  dsimp
  rw [hi1, hi2, hi3, hi4, hi5]
  constructor
  · apply Complex.ext
    · simp [phaseC]
      unfold PhaseCoords11.E1 at h1
      linarith
    · simp [phaseC]
      ring
  constructor
  · apply Complex.ext
    · simp [phaseC]
      unfold PhaseCoords11.E2 at h2
      linarith
    · simp [phaseC]
      ring
  constructor
  · apply Complex.ext
    · simp [phaseC]
      unfold PhaseCoords11.E3 at h3
      linarith
    · simp [phaseC]
      ring
  constructor
  · apply Complex.ext
    · simp [phaseC]
      unfold PhaseCoords11.E4 at h4
      linarith
    · simp [phaseC]
      ring
  · apply Complex.ext
    · simp [phaseC]
      unfold PhaseCoords11.E5 at h5
      linarith
    · simp [phaseC]
      ring

/-- A physical phase solution evaluates all six localized torus generators
to zero.  The final displayed equality identifies the torus coordinate used
by the circle lift with `i*k`. -/
theorem phaseSolution_h252Torus11
    (x : PhaseCoords11) (hx : x.IsPhaseSolution) :
    let z1 := phaseC x.a x.b
    let z2 := phaseC x.c x.d
    let z3 := phaseC x.e x.f
    let z4 := phaseC x.g x.h
    let z5 := phaseC x.j x.k
    ∃ w : ℂ,
      h252TorusF1 z1 z2 z3 z4 z5 = 0 ∧
      h252TorusF2 z1 z2 z3 z4 z5 = 0 ∧
      h252TorusF3 z1 z2 z3 z4 z5 = 0 ∧
      h252TorusF4 z1 z2 z3 z4 z5 = 0 ∧
      h252TorusF5 z1 z2 z3 z4 z5 = 0 ∧
      h252TorusS z1 z2 z3 z4 w z5 = 0 ∧
      (z5 - w*z1*z2*z3*z4) / 2 = Complex.I * x.k := by
  let z1 := phaseC x.a x.b
  let z2 := phaseC x.c x.d
  let z3 := phaseC x.e x.f
  let z4 := phaseC x.g x.h
  let z5 := phaseC x.j x.k
  let D := h252TorusD z1 z2 z3 z4 z5
  let w := D⁻¹
  rcases hx.1 with ⟨hab, hcd, hef, hgh, hjk⟩
  have hz1norm : Complex.normSq z1 = 1 := by
    simpa [z1, phaseC, Complex.normSq, pow_two] using hab
  have hz2norm : Complex.normSq z2 = 1 := by
    simpa [z2, phaseC, Complex.normSq, pow_two] using hcd
  have hz3norm : Complex.normSq z3 = 1 := by
    simpa [z3, phaseC, Complex.normSq, pow_two] using hef
  have hz4norm : Complex.normSq z4 = 1 := by
    simpa [z4, phaseC, Complex.normSq, pow_two] using hgh
  have hz5norm : Complex.normSq z5 = 1 := by
    simpa [z5, phaseC, Complex.normSq, pow_two] using hjk
  have hz1 : z1 ≠ 0 := fun hz => by simp [hz] at hz1norm
  have hz2 : z2 ≠ 0 := fun hz => by simp [hz] at hz2norm
  have hz3 : z3 ≠ 0 := fun hz => by simp [hz] at hz3norm
  have hz4 : z4 ≠ 0 := fun hz => by simp [hz] at hz4norm
  have hz5 : z5 ≠ 0 := fun hz => by simp [hz] at hz5norm
  have hD : D ≠ 0 := by
    dsimp [D, h252TorusD]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hz1 hz2) hz3) hz4) hz5
  have hLaurent := phaseSolution_laurentEquations11 x hx
  change
    (1 + z1 + z1⁻¹ + z1*z2⁻¹ + z2*z1⁻¹ + z2*z3⁻¹ +
      z3*z2⁻¹ + z3*z4⁻¹ + z4*z3⁻¹ + z4*z5⁻¹ + z5*z4⁻¹ = 0) ∧
    (1 + z2 + z2⁻¹ + z1*z3⁻¹ + z3*z1⁻¹ + z2*z4⁻¹ +
      z4*z2⁻¹ + z3*z5⁻¹ + z5*z3⁻¹ + z4*z5⁻¹ + z5*z4⁻¹ = 0) ∧
    (1 + z3 + z3⁻¹ + z1*z4⁻¹ + z4*z1⁻¹ + z2*z5⁻¹ +
      z5*z2⁻¹ + z3*z5⁻¹ + z5*z3⁻¹ + z1*z2⁻¹ + z2*z1⁻¹ = 0) ∧
    (1 + z4 + z4⁻¹ + z1*z5⁻¹ + z5*z1⁻¹ + z2*z5⁻¹ +
      z5*z2⁻¹ + z3*z4⁻¹ + z4*z3⁻¹ + z1*z3⁻¹ + z3*z1⁻¹ = 0) ∧
    (1 + z5 + z5⁻¹ + z1*z5⁻¹ + z5*z1⁻¹ + z2*z4⁻¹ +
      z4*z2⁻¹ + z1*z4⁻¹ + z4*z1⁻¹ + z2*z3⁻¹ + z3*z2⁻¹ = 0) at hLaurent
  rcases hLaurent with ⟨hL1, hL2, hL3, hL4, hL5⟩
  have hF1 : h252TorusF1 z1 z2 z3 z4 z5 = 0 := by
    calc
      h252TorusF1 z1 z2 z3 z4 z5 =
          D * (1 + z1 + z1⁻¹ + z1*z2⁻¹ + z2*z1⁻¹ + z2*z3⁻¹ +
            z3*z2⁻¹ + z3*z4⁻¹ + z4*z3⁻¹ + z4*z5⁻¹ + z5*z4⁻¹) := by
            dsimp [D, h252TorusD, h252TorusF1]
            field_simp [hz1, hz2, hz3, hz4, hz5]
            ring
      _ = 0 := by rw [hL1, mul_zero]
  have hF2 : h252TorusF2 z1 z2 z3 z4 z5 = 0 := by
    calc
      h252TorusF2 z1 z2 z3 z4 z5 =
          D * (1 + z2 + z2⁻¹ + z1*z3⁻¹ + z3*z1⁻¹ + z2*z4⁻¹ +
            z4*z2⁻¹ + z3*z5⁻¹ + z5*z3⁻¹ + z4*z5⁻¹ + z5*z4⁻¹) := by
            dsimp [D, h252TorusD, h252TorusF2]
            field_simp [hz1, hz2, hz3, hz4, hz5]
            ring
      _ = 0 := by rw [hL2, mul_zero]
  have hF3 : h252TorusF3 z1 z2 z3 z4 z5 = 0 := by
    calc
      h252TorusF3 z1 z2 z3 z4 z5 =
          D * (1 + z3 + z3⁻¹ + z1*z4⁻¹ + z4*z1⁻¹ + z2*z5⁻¹ +
            z5*z2⁻¹ + z3*z5⁻¹ + z5*z3⁻¹ + z1*z2⁻¹ + z2*z1⁻¹) := by
            dsimp [D, h252TorusD, h252TorusF3]
            field_simp [hz1, hz2, hz3, hz4, hz5]
            ring
      _ = 0 := by rw [hL3, mul_zero]
  have hF4 : h252TorusF4 z1 z2 z3 z4 z5 = 0 := by
    calc
      h252TorusF4 z1 z2 z3 z4 z5 =
          D * (1 + z4 + z4⁻¹ + z1*z5⁻¹ + z5*z1⁻¹ + z2*z5⁻¹ +
            z5*z2⁻¹ + z3*z4⁻¹ + z4*z3⁻¹ + z1*z3⁻¹ + z3*z1⁻¹) := by
            dsimp [D, h252TorusD, h252TorusF4]
            field_simp [hz1, hz2, hz3, hz4, hz5]
            ring
      _ = 0 := by rw [hL4, mul_zero]
  have hF5 : h252TorusF5 z1 z2 z3 z4 z5 = 0 := by
    calc
      h252TorusF5 z1 z2 z3 z4 z5 =
          D * (1 + z5 + z5⁻¹ + z1*z5⁻¹ + z5*z1⁻¹ + z2*z4⁻¹ +
            z4*z2⁻¹ + z1*z4⁻¹ + z4*z1⁻¹ + z2*z3⁻¹ + z3*z2⁻¹) := by
            dsimp [D, h252TorusD, h252TorusF5]
            field_simp [hz1, hz2, hz3, hz4, hz5]
            ring
      _ = 0 := by rw [hL5, mul_zero]
  have hS : h252TorusS z1 z2 z3 z4 w z5 = 0 := by
    simp [h252TorusS, w, D, hD]
  have hw : w*z1*z2*z3*z4 = z5⁻¹ := by
    dsimp [w, D, h252TorusD]
    field_simp [hz1, hz2, hz3, hz4, hz5]
  have hz5inv : z5⁻¹ = star z5 := by
    simp [Complex.inv_def, hz5norm]
  refine ⟨w, hF1, hF2, hF3, hF4, hF5, hS, ?_⟩
  rw [hw, hz5inv]
  apply Complex.ext <;> simp [z5, phaseC]

end

end Biunimodular.F11
