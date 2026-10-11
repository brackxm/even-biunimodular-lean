/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FiniteFieldIrreducibilityCriterion

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-- The finite-field irreducibility criterion in recursive Frobenius form.
This keeps large exponents symbolic in concrete degree-thirty certificates. -/
theorem irreducible_of_frobeniusIter_certificate
    {p n : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
    (hfmonic : f.Monic)
    (hdeg : f.natDegree = n)
    (hn : 0 < n)
    (hfull : f ∣ frobeniusIter p n - X)
    (hproper : ∀ d : ℕ, d ∣ n → 0 < d → d < n →
      IsCoprime f (frobeniusIter p d - X)) :
    Irreducible f := by
  apply irreducible_of_frobenius_certificate hfmonic hdeg hn
  · simpa only [frobeniusIter_eq_X_pow] using hfull
  · intro d hd hdpos hdlt
    simpa only [frobeniusIter_eq_X_pow] using hproper d hd hdpos hdlt

end Biunimodular.F11
