/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusStandardMonomials
import Biunimodular.F11.QuotientStandardMonomialSpan

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- An arbitrary collection of ideal members whose leading monomials divide
the reference leading monomials supplies the verified 252-element spanning
set. Neither equality of leading ideals nor a complete Groebner basis is
assumed. -/
theorem torusReferenceSpanningBound
    {K ι : Type*} [Field K]
    (m : MonomialOrder (Fin 7)) (I : Ideal (MvPolynomial (Fin 7) K))
    (b : ι → MvPolynomial (Fin 7) K)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hI : ∀ i, b i ∈ I)
    (hc : ∀ l ∈ torusReferenceLeadingExponents,
      ∃ i, m.degree (b i) ≤ Finsupp.equivFunOnFinite.symm l) :
    FiniteDimensional K (MvPolynomial (Fin 7) K ⧸ I) ∧
      Module.finrank K (MvPolynomial (Fin 7) K ⧸ I) ≤ 252 := by
  have hS : ∀ e, (∀ i, ¬ m.degree (b i) ≤ e) →
      e ∈ torusReferenceStandardMonomials := by
    intro e he
    apply torusReferenceStandardMonomials_cover e
    intro l hl hle
    obtain ⟨i, hi⟩ := hc l hl
    exact he i (hi.trans hle)
  exact ⟨quotient_finiteDimensional_of_standard_monomials m I b
    torusReferenceStandardMonomials hb hI hS, by
      simpa only [torusReferenceStandardMonomials_card] using
        quotient_finrank_le_standard_monomials m I b torusReferenceStandardMonomials hb hI hS⟩

end
end Biunimodular.F11
