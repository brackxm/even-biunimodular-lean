/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.SchreyerDescent
import Mathlib.RingTheory.Ideal.Basic

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

variable {R : Type*} [CommRing R] {n b : ℕ}

/-- A row of labels evaluated on a polynomial relation. -/
def relationLabelMap (labels : Fin b → R) : (Fin b → R) →ₗ[R] R where
  toFun w := ∑ k, labels k * w k
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c w := by simp [smul_eq_mul, Finset.mul_sum, mul_left_comm]

/-- A finite generating family of relations controls every relation's label
modulo the preceding original ideal. -/
theorem relation_labels_mem_of_span {ι : Type*}
    (labels : Fin b → R) (s : ι → Fin b → R) (I : Ideal R)
    (hs : ∀ j, relationLabelMap labels (s j) ∈ I)
    {w : Fin b → R} (hw : w ∈ Submodule.span R (Set.range s)) :
    relationLabelMap labels w ∈ I := by
  have hspan : Submodule.span R (Set.range s) ≤
      Submodule.comap (relationLabelMap labels) I := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hs j
  exact hspan hw

/-- Lift completeness from a computed basis back to the original generators.
The last row of `1 - M*N` and all basis-relation labels must belong to the
preceding original ideal; these are separate exact finite certificates. -/
theorem original_relation_last_mem_of_basis
    (f : Fin (n + 1) → R) (g : Fin b → R)
    (M : Fin (n + 1) → Fin b → R) (N : Fin b → Fin (n + 1) → R)
    (I : Ideal R)
    (hreverse : ∀ j, (∑ k, N k j * g k) = f j)
    (hresidual : ∀ j, (if j = Fin.last n then 1 else 0) -
      (∑ k, M (Fin.last n) k * N k j) ∈ I)
    (hlabels : ∀ w : Fin b → R, (∑ k, w k * g k) = 0 →
      relationLabelMap (M (Fin.last n)) w ∈ I)
    (v : Fin (n + 1) → R) (hv : (∑ j, v j * f j) = 0) :
    v (Fin.last n) ∈ I := by
  classical
  let w : Fin b → R := fun k => ∑ j, N k j * v j
  have hw : (∑ k, w k * g k) = 0 := by
    simp only [w, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_right_comm, ← Finset.sum_mul, hreverse, mul_comm (f _) (v _)]
    exact hv
  have hl := hlabels w hw
  have hr : (∑ j, v j * ((if j = Fin.last n then 1 else 0) -
      ∑ k, M (Fin.last n) k * N k j)) ∈ I :=
    I.sum_mem (fun j _ => I.mul_mem_left (v j) (hresidual j))
  have heq : (∑ j, v j * ((if j = Fin.last n then 1 else 0) -
      ∑ k, M (Fin.last n) k * N k j)) =
      v (Fin.last n) - relationLabelMap (M (Fin.last n)) w := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, relationLabelMap, w,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hr
  simpa using I.add_mem hr hl

end
end Biunimodular.F11
