/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RegularSequenceFromColon

set_option autoImplicit false
namespace Biunimodular.F11

theorem ideal_ofList_map_unit_mul {R : Type*} [CommRing R]
    (rs : List R) (u : Rˣ) :
    Ideal.ofList (rs.map (fun r => (u : R) * r)) = Ideal.ofList rs := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span hs)
  · apply Ideal.span_le.mpr
    intro r hr
    have hm : (u : R) * r ∈ Ideal.ofList (rs.map (fun r => (u : R) * r)) :=
      Ideal.subset_span (List.mem_map.mpr ⟨r, hr, rfl⟩)
    have h := Ideal.mul_mem_left _ (↑u⁻¹ : R) hm
    simpa [← mul_assoc] using h

theorem ideal_span_range_list_map {R : Type*} [CommRing R]
    {A : Type*} (rs : List A) (f : A → R) :
    Ideal.span (Set.range (fun a : {a // a ∈ rs} => f a.val)) =
      Ideal.ofList (rs.map f) := by
  congr 1
  ext r
  simp only [Set.mem_range, List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨⟨a, ha⟩, h⟩

end Biunimodular.F11
