/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252ComplexPhasePairs

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

theorem h252TorusCofactor_units {R : Type*} [CommRing R]
    (z : Fin 5 → R) (w : R) (hs : w * h252TorusDVector z = 1) (i : Fin 5) :
    z i * (w * h252TorusCofactor z i) = 1 := by
  fin_cases i
  · change z 0 * (w * (z 1 * z 2 * z 3 * z 4)) = 1
    calc
      _ = w * h252TorusDVector z := by simp only [h252TorusDVector, h252TorusD]; ring
      _ = 1 := hs
  · change z 1 * (w * (z 0 * z 2 * z 3 * z 4)) = 1
    calc
      _ = w * h252TorusDVector z := by simp only [h252TorusDVector, h252TorusD]; ring
      _ = 1 := hs
  · change z 2 * (w * (z 0 * z 1 * z 3 * z 4)) = 1
    calc
      _ = w * h252TorusDVector z := by simp only [h252TorusDVector, h252TorusD]; ring
      _ = 1 := hs
  · change z 3 * (w * (z 0 * z 1 * z 2 * z 4)) = 1
    calc
      _ = w * h252TorusDVector z := by simp only [h252TorusDVector, h252TorusD]; ring
      _ = 1 := hs
  · change z 4 * (w * (z 0 * z 1 * z 2 * z 3)) = 1
    calc
      _ = w * h252TorusDVector z := by simp only [h252TorusDVector, h252TorusD]; ring
      _ = 1 := hs

theorem h252ComplexPhaseFromUnitTorus (z t : Fin 5 → ℂ) (x : ℂ)
    (hu : ∀ i, z i * t i = 1)
    (h1 : h252TorusF1 (z 0) (z 1) (z 2) (z 3) (z 4) = 0)
    (h2 : h252TorusF2 (z 0) (z 1) (z 2) (z 3) (z 4) = 0)
    (h3 : h252TorusF3 (z 0) (z 1) (z 2) (z 3) (z 4) = 0)
    (h4 : h252TorusF4 (z 0) (z 1) (z 2) (z 3) (z 4) = 0)
    (h5 : h252TorusF5 (z 0) (z 1) (z 2) (z 3) (z 4) = 0)
    (hcoord : z 4 ^ 2 - 1 = 2 * z 4 * x) :
    ∃ a b : Fin 5 → ℂ, (∀ i, a i ^ 2 + b i ^ 2 = 1) ∧
      h252ComplexPhaseE1 a b = 0 ∧ h252ComplexPhaseE2 a b = 0 ∧
      h252ComplexPhaseE3 a b = 0 ∧ h252ComplexPhaseE4 a b = 0 ∧
      h252ComplexPhaseE5 a b = 0 ∧ Complex.I * b 4 = x := by
  let a (i : Fin 5) := h252ComplexPairA (z i) (t i)
  let b (i : Fin 5) := h252ComplexPairB (z i) (t i)
  have hZ : h252ComplexPhaseZ a b = z := by
    funext i
    change h252ComplexPairA (z i) (t i) + Complex.I * h252ComplexPairB (z i) (t i) = z i
    exact h252ComplexPair_z _ _
  have hT : h252ComplexPhaseInverse a b = t := by
    funext i
    change h252ComplexPairA (z i) (t i) - Complex.I * h252ComplexPairB (z i) (t i) = t i
    exact h252ComplexPair_inverse _ _
  have hz (i : Fin 5) : z i ≠ 0 := by
    intro hzero
    have h := hu i
    simp [hzero] at h
  have hd : h252TorusDVector z ≠ 0 := by
    simp only [h252TorusDVector, h252TorusD]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)) (hz 3)) (hz 4)
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (h252ComplexPair_circle (z i) (t i)).trans (hu i)
  · have h := h252LaurentRelation1_cleared z t hu
    rw [h1] at h
    have hl := (mul_eq_zero.mp h).resolve_left hd
    have he := h252LaurentRelation1_complex_phase a b
    rw [hZ, hT] at he
    exact he.symm.trans hl
  · have h := h252LaurentRelation2_cleared z t hu
    rw [h2] at h
    have hl := (mul_eq_zero.mp h).resolve_left hd
    have he := h252LaurentRelation2_complex_phase a b
    rw [hZ, hT] at he
    exact he.symm.trans hl
  · have h := h252LaurentRelation3_cleared z t hu
    rw [h3] at h
    have hl := (mul_eq_zero.mp h).resolve_left hd
    have he := h252LaurentRelation3_complex_phase a b
    rw [hZ, hT] at he
    exact he.symm.trans hl
  · have h := h252LaurentRelation4_cleared z t hu
    rw [h4] at h
    have hl := (mul_eq_zero.mp h).resolve_left hd
    have he := h252LaurentRelation4_complex_phase a b
    rw [hZ, hT] at he
    exact he.symm.trans hl
  · have h := h252LaurentRelation5_cleared z t hu
    rw [h5] at h
    have hl := (mul_eq_zero.mp h).resolve_left hd
    have he := h252LaurentRelation5_complex_phase a b
    rw [hZ, hT] at he
    exact he.symm.trans hl
  · exact h252ComplexPair_coordinate (z 4) (t 4) x (hu 4) hcoord

end

end Biunimodular.F11
