/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.SchreyerCriticalBounds
import Biunimodular.F11.ColonFromSyzygies

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

variable {σ K : Type*} [Field K] {n b : ℕ}

/-- Complete critical-pair certificates control the last component of every
relation of the original prefix. All ideal memberships are in the original
polynomial ring, rather than its radical or a selected affine chart. -/
theorem original_relation_last_mem_of_critical_pairs {ι : Type*}
    (m : MonomialOrder σ)
    (f : Fin (n + 1) → MvPolynomial σ K) (g : Fin b → MvPolynomial σ K)
    (M : Fin (n + 1) → Fin b → MvPolynomial σ K)
    (N : Fin b → Fin (n + 1) → MvPolynomial σ K)
    (s : ι → Fin b → MvPolynomial σ K) (I : Ideal (MvPolynomial σ K))
    (hg : ∀ k, g k ≠ 0)
    (hs : ∀ r, (∑ k, s r k * g k) = 0)
    (hcover : ∀ i j : Fin b, i < j → ∃ r,
      s r j * g j ≠ 0 ∧
      m.degree (s r j * g j) = m.degree (g i) ⊔ m.degree (g j) ∧
      ∀ k, schreyerKey m g (s r) k ≤ schreyerKey m g (s r) j)
    (hreverse : ∀ j, (∑ k, N k j * g k) = f j)
    (hresidual : ∀ j, (if j = Fin.last n then 1 else 0) -
      (∑ k, M (Fin.last n) k * N k j) ∈ I)
    (hlast : ∀ r, relationLabelMap (M (Fin.last n)) (s r) ∈ I)
    (v : Fin (n + 1) → MvPolynomial σ K) (hv : (∑ j, v j * f j) = 0) :
    v (Fin.last n) ∈ I := by
  have hcomplete := schreyer_relations_generate_of_critical_pairs m g s hg hs hcover
  apply original_relation_last_mem_of_basis f g M N I hreverse hresidual ?_ v hv
  intro w hw
  have hmem : w ∈ LinearMap.ker (polynomialRelationMap g) := hw
  rw [hcomplete] at hmem
  exact relation_labels_mem_of_span (M (Fin.last n)) s I hlast hmem

/-- The universal last-component condition is precisely the prefix-colon
obligation used by the regular-sequence criterion. -/
theorem colon_of_relation_last_mem {R : Type*} [CommRing R]
    (f : Fin n → R) (p : R)
    (h : ∀ v : Fin (n + 1) → R,
      (∑ j, v j * (Fin.snoc f p : Fin (n + 1) → R) j) = 0 →
      v (Fin.last n) ∈ Ideal.span (Set.range f))
    (x : R) (hx : p * x ∈ Ideal.span (Set.range f)) :
    x ∈ Ideal.span (Set.range f) := by
  classical
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
  let v : Fin (n + 1) → R := Fin.snoc (fun j => -a j) x
  have hv : (∑ j, v j * (Fin.snoc f p : Fin (n + 1) → R) j) = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [v, Fin.snoc_castSucc, Fin.snoc_last, neg_mul, Finset.sum_neg_distrib, ha]
    ring
  simpa only [v, Fin.snoc_last] using h v hv

end
end Biunimodular.F11
