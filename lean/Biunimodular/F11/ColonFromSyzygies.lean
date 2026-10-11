/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RegularSequenceFromColon
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
namespace Biunimodular.F11

/-- A finite generating set for all relations of an extended ideal suffices
for its colon condition, if every last component belongs to the old ideal.
The hypothesis covers every relation, not just the exported columns. -/
theorem colon_of_syzygy_generators {R : Type*} [CommRing R] {n m : ℕ}
    (g : Fin n → R) (p : R) (s : Fin m → Fin (n + 1) → R)
    (hgenerate : ∀ v : Fin (n + 1) → R,
      (∑ i, v i * (Fin.snoc g p : Fin (n + 1) → R) i) = 0 →
      ∃ c : Fin m → R, ∀ i, v i = ∑ j, c j * s j i)
    (hlast : ∀ j, s j (Fin.last n) ∈ Ideal.span (Set.range g))
    (x : R) (hx : p * x ∈ Ideal.span (Set.range g)) :
    x ∈ Ideal.span (Set.range g) := by
  classical
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
  let v : Fin (n + 1) → R := Fin.snoc (fun i => -a i) x
  have hv : (∑ i, v i * (Fin.snoc g p : Fin (n + 1) → R) i) = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [v, Fin.snoc_castSucc, Fin.snoc_last, neg_mul,
      Finset.sum_neg_distrib, ha]
    ring
  obtain ⟨c, hc⟩ := hgenerate v hv
  have heq : x = ∑ j, c j * s j (Fin.last n) := by
    simpa [v] using hc (Fin.last n)
  rw [heq]
  exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _ (hlast j))

end Biunimodular.F11
