/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PolynomialRelationTransfer

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The relation vector associated with one exact S-polynomial reduction. -/
def criticalRelationVector (i j : Fin n) (u v : R) (d : Fin n → R) : Fin n → R := by
  classical
  exact fun k => (if k = i then u else 0) - (if k = j then v else 0) - d k

theorem criticalRelationVector_sum (i j : Fin n) (u v : R) (d g : Fin n → R) :
    (∑ k, criticalRelationVector i j u v d k * g k) =
      u * g i - v * g j - ∑ k, d k * g k := by
  classical
  simp [criticalRelationVector, sub_mul, Finset.sum_sub_distrib,
    ite_mul, Finset.sum_ite_eq']

theorem criticalRelationVector_label (i j : Fin n) (u v : R) (d labels : Fin n → R) :
    relationLabelMap labels (criticalRelationVector i j u v d) =
      u * labels i - v * labels j - ∑ k, d k * labels k := by
  simpa [relationLabelMap, mul_comm] using criticalRelationVector_sum i j u v d labels

end
end Biunimodular.F11
