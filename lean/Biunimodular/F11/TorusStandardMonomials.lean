/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusStandardMonomialData
import Mathlib.Data.Finsupp.Order

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

def torusReferenceStandardMonomials : Finset (Fin 7 →₀ ℕ) :=
  torusReferenceStandardFunctions.image Finsupp.equivFunOnFinite.symm

theorem torusReferenceStandardMonomials_card :
    torusReferenceStandardMonomials.card = 252 := by
  rw [torusReferenceStandardMonomials,
    Finset.card_image_of_injective _ Finsupp.equivFunOnFinite.symm.injective]
  exact torusReferenceStandardFunctions_card

/-- The pure powers bound every exponent avoiding the reference leading ideal.
The finite box therefore captures all standard monomials, not just those
enumerated up to a chosen degree. -/
theorem torusReferenceStandardMonomials_cover (e : Fin 7 →₀ ℕ)
    (he : ∀ l ∈ torusReferenceLeadingExponents,
      ¬ Finsupp.equivFunOnFinite.symm l ≤ e) :
    e ∈ torusReferenceStandardMonomials := by
  have hb : ∀ i, e i < torusReferencePureBounds i := by
    intro i
    by_contra hn
    have hle : torusReferencePureBounds i ≤ e i := Nat.le_of_not_gt hn
    apply he _ (torusReferencePurePowers i)
    intro j
    change (if i = j then torusReferencePureBounds i else 0) ≤ e j
    by_cases hij : i = j
    · subst j
      simpa using hle
    · simp [hij]
  apply Finset.mem_image.mpr
  refine ⟨fun i => e i, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (hb i)), ?_⟩
    intro l hl hle
    apply he l hl
    intro i
    simpa using hle i
  · ext i
    simp

end
end Biunimodular.F11
