/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial

/-- A monic rational divisor of a monic integral polynomial is integral,
and reduction modulo any prime preserves its degree. -/
theorem monic_rational_divisor_lift (f : ℤ[X]) (hf : f.Monic)
    (q : ℚ[X]) (hq : q.Monic) (hd : q ∣ f.map (Int.castRingHom ℚ)) :
    ∃ g : ℤ[X], g.Monic ∧ g.map (Int.castRingHom ℚ) = q ∧
      g.natDegree = q.natDegree ∧ g ∣ f := by
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hf hd
  rw [hq.leadingCoeff, C_1, mul_one] at hg
  have hm : g.Monic := monic_of_injective (by exact Int.cast_injective) (hg.symm ▸ hq)
  refine ⟨g, hm, hg, ?_, ?_⟩
  · rw [← hg, hm.natDegree_map]
  · exact hf.dvd_of_fraction_map_dvd_fraction_map hm (hg.symm ▸ hd)

end Biunimodular.F11
