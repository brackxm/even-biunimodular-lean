/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252PhaseElimination11

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

def h252TorusDVector {R : Type*} [CommRing R] (z : Fin 5 → R) : R :=
  h252TorusD (z 0) (z 1) (z 2) (z 3) (z 4)

def h252TorusCofactor {R : Type*} [CommRing R] (z : Fin 5 → R) : Fin 5 → R :=
  ![z 1 * z 2 * z 3 * z 4, z 0 * z 2 * z 3 * z 4,
    z 0 * z 1 * z 3 * z 4, z 0 * z 1 * z 2 * z 4,
    z 0 * z 1 * z 2 * z 3]

theorem h252TorusD_mul_inverse {R : Type*} [CommRing R]
    (z t : Fin 5 → R) (hu : ∀ i, z i * t i = 1) (i : Fin 5) :
    h252TorusDVector z * t i = h252TorusCofactor z i := by
  fin_cases i
  · change (z 0 * z 1 * z 2 * z 3 * z 4) * t 0 = z 1 * z 2 * z 3 * z 4
    calc
      _ = (z 0 * t 0) * (z 1 * z 2 * z 3 * z 4) := by ring
      _ = _ := by rw [hu 0]; ring
  · change (z 0 * z 1 * z 2 * z 3 * z 4) * t 1 = z 0 * z 2 * z 3 * z 4
    calc
      _ = (z 1 * t 1) * (z 0 * z 2 * z 3 * z 4) := by ring
      _ = _ := by rw [hu 1]; ring
  · change (z 0 * z 1 * z 2 * z 3 * z 4) * t 2 = z 0 * z 1 * z 3 * z 4
    calc
      _ = (z 2 * t 2) * (z 0 * z 1 * z 3 * z 4) := by ring
      _ = _ := by rw [hu 2]; ring
  · change (z 0 * z 1 * z 2 * z 3 * z 4) * t 3 = z 0 * z 1 * z 2 * z 4
    calc
      _ = (z 3 * t 3) * (z 0 * z 1 * z 2 * z 4) := by ring
      _ = _ := by rw [hu 3]; ring
  · change (z 0 * z 1 * z 2 * z 3 * z 4) * t 4 = z 0 * z 1 * z 2 * z 3
    calc
      _ = (z 4 * t 4) * (z 0 * z 1 * z 2 * z 3) := by ring
      _ = _ := by rw [hu 4]; ring

theorem h252TorusD_mul_pair {R : Type*} [CommRing R]
    (z t : Fin 5 → R) (hu : ∀ i, z i * t i = 1) (a : R) (i : Fin 5) :
    h252TorusDVector z * (a * t i) = a * h252TorusCofactor z i := by
  rw [mul_left_comm, h252TorusD_mul_inverse z t hu]

def h252LaurentRelation1 {R : Type*} [CommRing R]
    (z t : Fin 5 → R) : R :=
  1 + z 0 + t 0 + z 0 * t 1 + z 1 * t 0 + z 1 * t 2 + z 2 * t 1 + z 2 * t 3 + z 3 * t 2 + z 3 * t 4 + z 4 * t 3

theorem h252LaurentRelation1_cleared {R : Type*} [CommRing R]
    (z t : Fin 5 → R) (hu : ∀ j, z j * t j = 1) :
    h252TorusDVector z * h252LaurentRelation1 z t =
      h252TorusF1 (z 0) (z 1) (z 2) (z 3) (z 4) := by
  simp only [h252LaurentRelation1, mul_add, mul_one]
  rw [h252TorusD_mul_inverse z t hu 0]
  simp only [h252TorusD_mul_pair z t hu]
  simp [h252TorusDVector, h252TorusD, h252TorusCofactor, h252TorusF1]
  ring

def h252LaurentRelation2 {R : Type*} [CommRing R]
    (z t : Fin 5 → R) : R :=
  1 + z 1 + t 1 + z 0 * t 2 + z 2 * t 0 + z 1 * t 3 + z 3 * t 1 + z 2 * t 4 + z 4 * t 2 + z 3 * t 4 + z 4 * t 3

theorem h252LaurentRelation2_cleared {R : Type*} [CommRing R]
    (z t : Fin 5 → R) (hu : ∀ j, z j * t j = 1) :
    h252TorusDVector z * h252LaurentRelation2 z t =
      h252TorusF2 (z 0) (z 1) (z 2) (z 3) (z 4) := by
  simp only [h252LaurentRelation2, mul_add, mul_one]
  rw [h252TorusD_mul_inverse z t hu 1]
  simp only [h252TorusD_mul_pair z t hu]
  simp [h252TorusDVector, h252TorusD, h252TorusCofactor, h252TorusF2]
  ring

def h252LaurentRelation3 {R : Type*} [CommRing R]
    (z t : Fin 5 → R) : R :=
  1 + z 2 + t 2 + z 0 * t 3 + z 3 * t 0 + z 1 * t 4 + z 4 * t 1 + z 2 * t 4 + z 4 * t 2 + z 0 * t 1 + z 1 * t 0

theorem h252LaurentRelation3_cleared {R : Type*} [CommRing R]
    (z t : Fin 5 → R) (hu : ∀ j, z j * t j = 1) :
    h252TorusDVector z * h252LaurentRelation3 z t =
      h252TorusF3 (z 0) (z 1) (z 2) (z 3) (z 4) := by
  simp only [h252LaurentRelation3, mul_add, mul_one]
  rw [h252TorusD_mul_inverse z t hu 2]
  simp only [h252TorusD_mul_pair z t hu]
  simp [h252TorusDVector, h252TorusD, h252TorusCofactor, h252TorusF3]
  ring

def h252LaurentRelation4 {R : Type*} [CommRing R]
    (z t : Fin 5 → R) : R :=
  1 + z 3 + t 3 + z 0 * t 4 + z 4 * t 0 + z 1 * t 4 + z 4 * t 1 + z 2 * t 3 + z 3 * t 2 + z 0 * t 2 + z 2 * t 0

theorem h252LaurentRelation4_cleared {R : Type*} [CommRing R]
    (z t : Fin 5 → R) (hu : ∀ j, z j * t j = 1) :
    h252TorusDVector z * h252LaurentRelation4 z t =
      h252TorusF4 (z 0) (z 1) (z 2) (z 3) (z 4) := by
  simp only [h252LaurentRelation4, mul_add, mul_one]
  rw [h252TorusD_mul_inverse z t hu 3]
  simp only [h252TorusD_mul_pair z t hu]
  simp [h252TorusDVector, h252TorusD, h252TorusCofactor, h252TorusF4]
  ring

def h252LaurentRelation5 {R : Type*} [CommRing R]
    (z t : Fin 5 → R) : R :=
  1 + z 4 + t 4 + z 0 * t 4 + z 4 * t 0 + z 1 * t 3 + z 3 * t 1 + z 0 * t 3 + z 3 * t 0 + z 1 * t 2 + z 2 * t 1

theorem h252LaurentRelation5_cleared {R : Type*} [CommRing R]
    (z t : Fin 5 → R) (hu : ∀ j, z j * t j = 1) :
    h252TorusDVector z * h252LaurentRelation5 z t =
      h252TorusF5 (z 0) (z 1) (z 2) (z 3) (z 4) := by
  simp only [h252LaurentRelation5, mul_add, mul_one]
  rw [h252TorusD_mul_inverse z t hu 4]
  simp only [h252TorusD_mul_pair z t hu]
  simp [h252TorusDVector, h252TorusD, h252TorusCofactor, h252TorusF5]
  ring

end

end Biunimodular.F11
