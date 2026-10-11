/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.Multiset.Powerset

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial UniqueFactorizationMonoid

/-- Every monic divisor of a product of monic irreducibles is an exact
subproduct, including repeated irreducible factors. -/
theorem monic_divisor_eq_subproduct {K : Type*} [Field K]
    (s : Multiset K[X]) (hs : ∀ p ∈ s, p.Monic ∧ Irreducible p)
    (q : K[X]) (hq : q.Monic) (hd : q ∣ s.prod) :
    ∃ t : Multiset K[X], t ≤ s ∧ q = t.prod := by
  classical
  have hsn : s.prod ≠ 0 := Multiset.prod_ne_zero fun h ↦ (hs 0 h).1.ne_zero rfl
  have hf : normalizedFactors s.prod = s := by
    rw [normalizedFactors_prod_eq s (fun p hp ↦ (hs p hp).2)]
    calc
      s.map normalize = s.map (fun p ↦ p) := Multiset.map_congr rfl
        (fun p hp ↦ (hs p hp).1.normalize_eq_self)
      _ = s := Multiset.map_id' s
  refine ⟨normalizedFactors q, ?_, ?_⟩
  · rw [← hf]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hq.ne_zero hsn).mp hd
  · rw [prod_normalizedFactors_eq hq.ne_zero, hq.normalize_eq_self]

end Biunimodular.F11
