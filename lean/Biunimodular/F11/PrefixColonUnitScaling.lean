/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IdealListUnitScaling

set_option autoImplicit false
namespace Biunimodular.F11

theorem prefix_colon_map_unit_mul {R : Type*} [CommRing R] (rs : List R) (u : Rˣ)
    (h : ∀ i (hi : i < rs.length) (x : R),
      rs[i] * x ∈ Ideal.ofList (rs.take i) → x ∈ Ideal.ofList (rs.take i)) :
    ∀ i (hi : i < (rs.map (fun p => (u : R) * p)).length) (x : R),
      (rs.map (fun p => (u : R) * p))[i] * x ∈
        Ideal.ofList ((rs.map (fun p => (u : R) * p)).take i) →
      x ∈ Ideal.ofList ((rs.map (fun p => (u : R) * p)).take i) := by
  intro i hi x hx
  have hi' : i < rs.length := by simpa only [List.length_map] using hi
  rw [← List.map_take, ideal_ofList_map_unit_mul] at hx ⊢
  apply h i hi' x
  have hh := (Ideal.ofList (rs.take i)).mul_mem_left (↑u⁻¹ : R) hx
  simpa [List.getElem_map, ← mul_assoc] using hh

end Biunimodular.F11
