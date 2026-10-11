/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.DegreeEight875GroupBridge
import Biunimodular.F11.DegreeEightS8FiniteBridge

set_option autoImplicit false

namespace Biunimodular.F11

private theorem s8_conjugated_generation
    (a b c p : Equiv.Perm (Fin 8))
    (ha : p * a * p⁻¹ = s8CanonicalEight)
    (hb : b.IsCycle ∧ b.support.card = 7)
    (hc : c.IsCycle ∧ c.support.card = 5)
    (hfix : (p * b * p⁻¹) 7 = 7) :
    Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 8))) = ⊤ := by
  let bb := p * b * p⁻¹
  let cc := p * c * p⁻¹
  have hbb7 : bb.support.card = 7 := by
    simpa [bb] using (Equiv.Perm.card_support_conj (σ := p) (τ := b)).trans hb.2
  have hcc5 : cc.support.card = 5 := by
    simpa [cc] using (Equiv.Perm.card_support_conj (σ := p) (τ := c)).trans hc.2
  have hbborder : bb ^ 7 = 1 := by
    have hcycle : bb.IsCycle := hb.1.conj
    rw [← hbb7, ← hcycle.orderOf]
    exact pow_orderOf_eq_one bb
  have hccorder : cc ^ 5 = 1 := by
    have hcycle : cc.IsCycle := hc.1.conj
    rw [← hcc5, ← hcycle.orderOf]
    exact pow_orderOf_eq_one cc
  have hnorm := s8_normalized_generation bb cc hbb7 hbborder hfix hcc5 hccorder
  let H := Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 8)))
  let K := H.map (MulAut.conj p).toMonoidHom
  have haK : s8CanonicalEight ∈ K := by
    rw [← ha]
    exact ⟨a, Subgroup.subset_closure (by simp), rfl⟩
  have hbK : bb ∈ K := ⟨b, Subgroup.subset_closure (by simp), rfl⟩
  have hcK : cc ∈ K := ⟨c, Subgroup.subset_closure (by simp), rfl⟩
  have hKtop : K = ⊤ := by
    apply top_unique
    rw [← hnorm]
    apply (Subgroup.closure_le _).2
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact haK
    · exact hbK
    · exact hcK
  apply (Subgroup.map_injective (f := (MulAut.conj p).toMonoidHom)
    (MulAut.conj p).injective)
  simpa [H, K] using hKtop

private theorem s8_canonical_cycle : s8CanonicalEight.IsCycle := by
  unfold s8CanonicalEight
  change (List.formPerm ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 8))).IsCycle
  exact List.isCycle_formPerm (by decide) (by decide)

private theorem s8_canonical_support : s8CanonicalEight.support.card = 8 := by
  native_decide

/-- Every 8-cycle together with a 7-cycle admits coordinates in which the
first is canonical and the second fixes 7. -/
private theorem s8_simultaneous_normalization
    (a b : Equiv.Perm (Fin 8))
    (ha : a.IsCycle ∧ a.support.card = 8)
    (hb : b.IsCycle ∧ b.support.card = 7) :
    ∃ p : Equiv.Perm (Fin 8),
      p * a * p⁻¹ = s8CanonicalEight ∧ (p * b * p⁻¹) 7 = 7 := by
  have htype : a.cycleType = s8CanonicalEight.cycleType := by
    rw [ha.1.cycleType, s8_canonical_cycle.cycleType, ha.2, s8_canonical_support]
  obtain ⟨t, ht⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr htype)
  obtain ⟨x, hbx⟩ : ∃ x : Fin 8, b x = x := by
    by_contra hh
    push Not at hh
    have hall : b.support = Finset.univ := by
      ext y
      simp [Equiv.Perm.mem_support, hh y]
    have : b.support.card = 8 := by simp [hall]
    omega
  obtain ⟨k, -, hk⟩ := s8_eight_point_transitive (t x) 7
  refine ⟨s8CanonicalEight ^ k * t, ?_, ?_⟩
  · rw [mul_inv_rev]
    calc
      (s8CanonicalEight ^ k * t) * a * (t⁻¹ * (s8CanonicalEight ^ k)⁻¹) =
          s8CanonicalEight ^ k * (t * a * t⁻¹) * (s8CanonicalEight ^ k)⁻¹ := by group
      _ = s8CanonicalEight ^ k * s8CanonicalEight * (s8CanonicalEight ^ k)⁻¹ := by
        rw [ht]
      _ = s8CanonicalEight := by rw [pow_mul_comm']; group
  · have hpx : (s8CanonicalEight ^ k * t) x = 7 := by
      simpa [Equiv.Perm.mul_apply] using hk
    rw [← hpx]
    simp [Equiv.Perm.mul_apply, hbx]

/-- Exact finite 8/7/5 generation, without a parameter. -/
theorem degreeEight875Generation : DegreeEight875GenerationLemma := by
  intro a b c ha hb hc
  obtain ⟨p, hpa, hpb⟩ := s8_simultaneous_normalization a b ha hb
  exact s8_conjugated_generation a b c p hpa hb hc hpb

end Biunimodular.F11
