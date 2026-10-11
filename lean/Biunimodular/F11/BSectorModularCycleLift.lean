/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorArithmeticFrobenius
import Biunimodular.F11.FiniteFieldFrobeniusTransport

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-- Any polynomial identified with the monic B reduction has the same
root set as the integer polynomial in a residue field. -/
theorem bMonic_modp_rootSet_eq
    (p : ℕ) (K : Type*) [Field K] [CharP K p]
    [Algebra (ZMod p) K]
    (q : (ZMod p)[X])
    (hq : q = invariantBMonicTransform.map (Int.castRingHom (ZMod p))) :
    q.rootSet K = invariantBMonicTransform.rootSet K := by
  let : IsScalarTower ℤ (ZMod p) K := inferInstance
  have hcomp : (algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)) =
      algebraMap ℤ K := by
    ext n
    simp
  subst q
  calc
    (invariantBMonicTransform.map (Int.castRingHom (ZMod p))).rootSet K =
        (invariantBMonicTransform.map (Int.castRingHom (ZMod p)) |>.map
          (algebraMap (ZMod p) K)).rootSet K :=
      (Polynomial.rootSet_map K K _).symm
    _ = (invariantBMonicTransform.map (algebraMap ℤ K)).rootSet K := by
      rw [Polynomial.map_map, hcomp]
    _ = invariantBMonicTransform.rootSet K :=
      Polynomial.rootSet_map K K invariantBMonicTransform

/-- Transport a residue-field cycle and its support size through reduction
to the actual arithmetic Frobenius action on integral roots. -/
theorem bMonic_lift_residue_cycle
    (p : ℕ) (Q : Ideal BIntegers) [Q.IsPrime]
    [Algebra (ZMod p) (BIntegers ⧸ Q)]
    [DecidableEq (invariantBMonicTransform.rootSet BIntegers)]
    [DecidableEq (invariantBMonicTransform.rootSet (BIntegers ⧸ Q))]
    (q : (ZMod p)[X]) [DecidableEq (q.rootSet (BIntegers ⧸ Q))]
    (hunder : Q.under ℤ = bBasePrimeIdeal p)
    (hsep : (invariantBMonicTransform.map
      (Int.castRingHom (ZMod p))).Separable)
    (σ : BOriginalQ.Gal) (hσ : IsArithFrobAt ℤ σ Q)
    (hset : q.rootSet (BIntegers ⧸ Q) =
      invariantBMonicTransform.rootSet (BIntegers ⧸ Q))
    (g : Equiv.Perm (q.rootSet (BIntegers ⧸ Q)))
    (hgpow : ∀ x, (g x).1 = (x.1 : BIntegers ⧸ Q) ^ p)
    (hgcycle : g.IsCycle) (m : ℕ) (hgsupport : g.support.card = m) :
    (MulAction.toPermHom BOriginalQ.Gal
      (invariantBMonicTransform.rootSet BIntegers) σ).IsCycle ∧
    (MulAction.toPermHom BOriginalQ.Gal
      (invariantBMonicTransform.rootSet BIntegers) σ).support.card = m := by
  let K := BIntegers ⧸ Q
  let e : q.rootSet K ≃ invariantBMonicTransform.rootSet K :=
    { toFun := fun x => ⟨x.1, by rw [← hset]; exact x.2⟩
      invFun := fun x => ⟨x.1, by rw [hset]; exact x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  let g' : Equiv.Perm (invariantBMonicTransform.rootSet K) := e.permCongrHom g
  have he (y : q.rootSet K) : ((e y : invariantBMonicTransform.rootSet K) : K) =
      (y : K) := rfl
  have he' (y : invariantBMonicTransform.rootSet K) : ((e.symm y : q.rootSet K) : K) =
      (y : K) := by
    have h := he (e.symm y)
    rw [e.apply_symm_apply] at h
    exact h.symm
  have hg'pow (x : invariantBMonicTransform.rootSet K) :
      (g' x).1 = (x.1 : K) ^ p := by
    have h := hgpow (e.symm x)
    rw [he' x] at h
    change ((e (g (e.symm x)) : invariantBMonicTransform.rootSet K) : K) = _
    rw [he]
    exact h
  have hg'cycle : g'.IsCycle := by
    apply isCycle_of_equivariant_equiv e.symm g' g
    · intro x
      simp only [g', Equiv.permCongrHom_coe, Equiv.permCongr_apply,
        Equiv.symm_apply_apply]
    · exact hgcycle
  have hg'support : g'.support.card = m := by
    have heq := support_card_eq_of_equivariant_equiv e g g' (by
      intro x
      simp only [g', Equiv.permCongrHom_coe, Equiv.permCongr_apply,
        Equiv.symm_apply_apply])
    exact heq.symm.trans hgsupport
  exact ⟨bMonic_arithFrob_cycle_transfer p Q hunder hsep σ hσ g' hg'pow hg'cycle,
    (bMonic_arithFrob_support_transfer p Q hunder hsep σ hσ g' hg'pow).trans hg'support⟩

end Biunimodular.F11
