/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252LaurentPhaseBridge

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

def h252ComplexPhaseZ {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (i : Fin 5) : R :=
  a i + (algebraMap ℂ R Complex.I) * b i

def h252ComplexPhaseInverse {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (i : Fin 5) : R :=
  a i - (algebraMap ℂ R Complex.I) * b i

theorem h252ComplexPhase_i_sq {R : Type*} [CommRing R] [Algebra ℂ R] :
    (algebraMap ℂ R Complex.I) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]

theorem h252ComplexPhase_units {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (hc : ∀ i, a i ^ 2 + b i ^ 2 = 1) (i : Fin 5) :
    h252ComplexPhaseZ a b i * h252ComplexPhaseInverse a b i = 1 := by
  calc
    _ = a i ^ 2 - (algebraMap ℂ R Complex.I) ^ 2 * b i ^ 2 := by
      simp only [h252ComplexPhaseZ, h252ComplexPhaseInverse]
      ring
    _ = a i ^ 2 + b i ^ 2 := by rw [h252ComplexPhase_i_sq]; ring
    _ = 1 := hc i

/-- The original phase equation E1, over any complex algebra. -/
def h252ComplexPhaseE1 {R : Type*} [CommRing R] (a b : Fin 5 → R) : R :=
  2 * a 0 + 2 * (a 0 * a 1 + b 0 * b 1) + 2 * (a 1 * a 2 + b 1 * b 2) + 2 * (a 2 * a 3 + b 2 * b 3) + 2 * (a 3 * a 4 + b 3 * b 4) + 1

theorem h252LaurentRelation1_complex_phase {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) :
    h252LaurentRelation1 (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b) =
      h252ComplexPhaseE1 a b := by
  simp only [h252LaurentRelation1, h252ComplexPhaseZ,
    h252ComplexPhaseInverse, h252ComplexPhaseE1]
  ring_nf; simp only [h252ComplexPhase_i_sq]; ring

theorem h252ComplexPhaseE1_torus {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (hc : ∀ j, a j ^ 2 + b j ^ 2 = 1)
    (he : h252ComplexPhaseE1 a b = 0) :
    h252TorusF1 (h252ComplexPhaseZ a b 0) (h252ComplexPhaseZ a b 1)
      (h252ComplexPhaseZ a b 2) (h252ComplexPhaseZ a b 3) (h252ComplexPhaseZ a b 4) = 0 := by
  have h := h252LaurentRelation1_cleared
    (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b)
    (h252ComplexPhase_units a b hc)
  rw [h252LaurentRelation1_complex_phase, he, mul_zero] at h
  exact h.symm

/-- The original phase equation E2, over any complex algebra. -/
def h252ComplexPhaseE2 {R : Type*} [CommRing R] (a b : Fin 5 → R) : R :=
  2 * a 1 + 2 * (a 0 * a 2 + b 0 * b 2) + 2 * (a 1 * a 3 + b 1 * b 3) + 2 * (a 2 * a 4 + b 2 * b 4) + 2 * (a 3 * a 4 + b 3 * b 4) + 1

theorem h252LaurentRelation2_complex_phase {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) :
    h252LaurentRelation2 (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b) =
      h252ComplexPhaseE2 a b := by
  simp only [h252LaurentRelation2, h252ComplexPhaseZ,
    h252ComplexPhaseInverse, h252ComplexPhaseE2]
  ring_nf; simp only [h252ComplexPhase_i_sq]; ring

theorem h252ComplexPhaseE2_torus {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (hc : ∀ j, a j ^ 2 + b j ^ 2 = 1)
    (he : h252ComplexPhaseE2 a b = 0) :
    h252TorusF2 (h252ComplexPhaseZ a b 0) (h252ComplexPhaseZ a b 1)
      (h252ComplexPhaseZ a b 2) (h252ComplexPhaseZ a b 3) (h252ComplexPhaseZ a b 4) = 0 := by
  have h := h252LaurentRelation2_cleared
    (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b)
    (h252ComplexPhase_units a b hc)
  rw [h252LaurentRelation2_complex_phase, he, mul_zero] at h
  exact h.symm

/-- The original phase equation E3, over any complex algebra. -/
def h252ComplexPhaseE3 {R : Type*} [CommRing R] (a b : Fin 5 → R) : R :=
  2 * a 2 + 2 * (a 0 * a 3 + b 0 * b 3) + 2 * (a 1 * a 4 + b 1 * b 4) + 2 * (a 2 * a 4 + b 2 * b 4) + 2 * (a 0 * a 1 + b 0 * b 1) + 1

theorem h252LaurentRelation3_complex_phase {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) :
    h252LaurentRelation3 (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b) =
      h252ComplexPhaseE3 a b := by
  simp only [h252LaurentRelation3, h252ComplexPhaseZ,
    h252ComplexPhaseInverse, h252ComplexPhaseE3]
  ring_nf; simp only [h252ComplexPhase_i_sq]; ring

theorem h252ComplexPhaseE3_torus {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (hc : ∀ j, a j ^ 2 + b j ^ 2 = 1)
    (he : h252ComplexPhaseE3 a b = 0) :
    h252TorusF3 (h252ComplexPhaseZ a b 0) (h252ComplexPhaseZ a b 1)
      (h252ComplexPhaseZ a b 2) (h252ComplexPhaseZ a b 3) (h252ComplexPhaseZ a b 4) = 0 := by
  have h := h252LaurentRelation3_cleared
    (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b)
    (h252ComplexPhase_units a b hc)
  rw [h252LaurentRelation3_complex_phase, he, mul_zero] at h
  exact h.symm

/-- The original phase equation E4, over any complex algebra. -/
def h252ComplexPhaseE4 {R : Type*} [CommRing R] (a b : Fin 5 → R) : R :=
  2 * a 3 + 2 * (a 0 * a 4 + b 0 * b 4) + 2 * (a 1 * a 4 + b 1 * b 4) + 2 * (a 2 * a 3 + b 2 * b 3) + 2 * (a 0 * a 2 + b 0 * b 2) + 1

theorem h252LaurentRelation4_complex_phase {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) :
    h252LaurentRelation4 (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b) =
      h252ComplexPhaseE4 a b := by
  simp only [h252LaurentRelation4, h252ComplexPhaseZ,
    h252ComplexPhaseInverse, h252ComplexPhaseE4]
  ring_nf; simp only [h252ComplexPhase_i_sq]; ring

theorem h252ComplexPhaseE4_torus {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (hc : ∀ j, a j ^ 2 + b j ^ 2 = 1)
    (he : h252ComplexPhaseE4 a b = 0) :
    h252TorusF4 (h252ComplexPhaseZ a b 0) (h252ComplexPhaseZ a b 1)
      (h252ComplexPhaseZ a b 2) (h252ComplexPhaseZ a b 3) (h252ComplexPhaseZ a b 4) = 0 := by
  have h := h252LaurentRelation4_cleared
    (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b)
    (h252ComplexPhase_units a b hc)
  rw [h252LaurentRelation4_complex_phase, he, mul_zero] at h
  exact h.symm

/-- The original phase equation E5, over any complex algebra. -/
def h252ComplexPhaseE5 {R : Type*} [CommRing R] (a b : Fin 5 → R) : R :=
  2 * a 4 + 2 * (a 0 * a 4 + b 0 * b 4) + 2 * (a 1 * a 3 + b 1 * b 3) + 2 * (a 0 * a 3 + b 0 * b 3) + 2 * (a 1 * a 2 + b 1 * b 2) + 1

theorem h252LaurentRelation5_complex_phase {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) :
    h252LaurentRelation5 (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b) =
      h252ComplexPhaseE5 a b := by
  simp only [h252LaurentRelation5, h252ComplexPhaseZ,
    h252ComplexPhaseInverse, h252ComplexPhaseE5]
  ring_nf; simp only [h252ComplexPhase_i_sq]; ring

theorem h252ComplexPhaseE5_torus {R : Type*} [CommRing R] [Algebra ℂ R]
    (a b : Fin 5 → R) (hc : ∀ j, a j ^ 2 + b j ^ 2 = 1)
    (he : h252ComplexPhaseE5 a b = 0) :
    h252TorusF5 (h252ComplexPhaseZ a b 0) (h252ComplexPhaseZ a b 1)
      (h252ComplexPhaseZ a b 2) (h252ComplexPhaseZ a b 3) (h252ComplexPhaseZ a b 4) = 0 := by
  have h := h252LaurentRelation5_cleared
    (h252ComplexPhaseZ a b) (h252ComplexPhaseInverse a b)
    (h252ComplexPhase_units a b hc)
  rw [h252LaurentRelation5_complex_phase, he, mul_zero] at h
  exact h.symm

end

end Biunimodular.F11
