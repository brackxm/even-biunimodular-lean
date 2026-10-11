/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorF30Coprime
import Biunimodular.F11.FiniteFieldIrreducibilityIterCriterion

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-- Exact Rabin certificate for the degree-thirty A coordinate polynomial. -/
theorem aSectorG30mod2_irreducible : Irreducible aSectorG30mod2 := by
  have hfull : aSectorG30mod2 ∣ frobeniusIter 2 30 - X := by
    simpa only [g30r30] using g30Frob30
  have hc1 : IsCoprime aSectorG30mod2 (frobeniusIter 2 1 - X) := by
    apply isCoprime_of_dvd_sub g30copSmall1
    have hrel := g30Frob1
    convert hrel using 1
    all_goals ring
  have hc2 : IsCoprime aSectorG30mod2 (frobeniusIter 2 2 - X) := by
    apply isCoprime_of_dvd_sub g30copSmall2
    have hrel := g30Frob2
    convert hrel using 1
    all_goals ring
  have hc3 : IsCoprime aSectorG30mod2 (frobeniusIter 2 3 - X) := by
    apply isCoprime_of_dvd_sub g30copSmall3
    have hrel := g30Frob3
    convert hrel using 1
    all_goals ring
  have hc5 : IsCoprime aSectorG30mod2 (frobeniusIter 2 5 - X) := by
    apply isCoprime_of_dvd_sub g30copSmall5
    have hrel := g30Frob5
    convert hrel using 1
    all_goals ring
  have hc6 : IsCoprime aSectorG30mod2 (frobeniusIter 2 6 - X) := by
    apply isCoprime_of_dvd_sub g30copSmall6
    have hrel := g30Frob6
    convert hrel using 1
    all_goals ring
  have hc10 : IsCoprime aSectorG30mod2 (frobeniusIter 2 10 - X) := by
    apply isCoprime_of_dvd_sub g30copSmall10
    have hrel := g30Frob10
    convert hrel using 1
    all_goals ring
  have hc15 : IsCoprime aSectorG30mod2 (frobeniusIter 2 15 - X) := by
    apply isCoprime_of_dvd_sub g30copSmall15
    have hrel := g30Frob15
    convert hrel using 1
    all_goals ring
  apply irreducible_of_frobeniusIter_certificate
      (p := 2) (n := 30) (f := aSectorG30mod2)
  · exact g30mod2_monic
  · exact g30mod2_natDegree
  · norm_num
  · exact hfull
  · intro d hd hdpos hdlt
    have hset : Nat.divisors 30 =
        ({1, 2, 3, 5, 6, 10, 15, 30} : Finset ℕ) := by native_decide
    have hmem : d ∈ ({1, 2, 3, 5, 6, 10, 15, 30} : Finset ℕ) := by
      rw [← hset]
      exact Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h
    · simpa [h] using hc1
    · simpa [h] using hc2
    · simpa [h] using hc3
    · simpa [h] using hc5
    · simpa [h] using hc6
    · simpa [h] using hc10
    · simpa [h] using hc15
    · omega

end
end Biunimodular.F11
