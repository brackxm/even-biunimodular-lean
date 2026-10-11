/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PolynomialGaloisGroup

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-- Every root of an irreducible degree-`n` polynomial over a finite field
is fixed by the `card(F)^n` power map in any extension field. -/
theorem irreducible_root_pow_card_pow
    {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (q : F[X]) (hq : Irreducible q) (x : q.rootSet K) :
    (x : K) ^ (Nat.card F) ^ q.natDegree = x := by
  have hdvd : q ∣ X ^ (Nat.card F) ^ q.natDegree - X :=
    (hq.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mp (dvd_refl _)
  have hzero : aeval x.1 q = 0 := (Polynomial.mem_rootSet.mp x.2).2
  have h := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hzero
  exact sub_eq_zero.mp (by simpa using h)

end Biunimodular.F11
