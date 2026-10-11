/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorArithmeticFrobenius
import Biunimodular.F11.FiniteFieldFrobeniusTransport
import Biunimodular.F11.BSectorFiniteFieldCycles

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Biunimodular.F11

open Polynomial

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private noncomputable instance :
    DecidableEq (invariantBMonicTransform.rootSet BIntegers) := Classical.decEq _

private theorem b5_natDegree : invariantB5.natDegree = 8 := by
  norm_num [invariantB5]
  compute_degree <;> norm_num

/-- The modular polynomial's root set agrees with the reduction of the
integral monic transform in every field of characteristic five. -/
theorem bMonic_mod5_rootSet_eq (K : Type*) [Field K] [CharP K 5]
    [Algebra (ZMod 5) K] :
    invariantB5.rootSet K = invariantBMonicTransform.rootSet K := by
  let : IsScalarTower ℤ (ZMod 5) K := inferInstance
  have hcomp : (algebraMap (ZMod 5) K).comp (Int.castRingHom (ZMod 5)) =
      algebraMap ℤ K := by
    ext n
    simp
  have hpoly : invariantB5.map (algebraMap (ZMod 5) K) =
      invariantBMonicTransform.map (algebraMap ℤ K) := by
    rw [← invariantBMonicTransform_mod5, Polynomial.map_map, hcomp]
  calc
    invariantB5.rootSet K =
        (invariantB5.map (algebraMap (ZMod 5) K)).rootSet K :=
      (Polynomial.rootSet_map K K invariantB5).symm
    _ = (invariantBMonicTransform.map (algebraMap ℤ K)).rootSet K := by rw [hpoly]
    _ = invariantBMonicTransform.rootSet K :=
      Polynomial.rootSet_map K K invariantBMonicTransform

/-- The monic B transform has a full eight-cycle arithmetic Frobenius on
its integral roots at a prime above five. -/
theorem exists_bMonic_eight_cycle :
    ∃ σ : BOriginalQ.Gal,
      (MulAction.toPermHom BOriginalQ.Gal
        (invariantBMonicTransform.rootSet BIntegers) σ).IsCycle ∧
      (MulAction.toPermHom BOriginalQ.Gal
        (invariantBMonicTransform.rootSet BIntegers) σ).support.card = 8 := by
  classical
  obtain ⟨Q, hmax, hQ, hunder, σ, hσ⟩ :=
    exists_bMonic_arithFrob_at_prime 5 (by decide)
  let : Q.IsMaximal := hmax
  let : Q.IsPrime := hQ
  let : Field (BIntegers ⧸ Q) := Ideal.Quotient.field Q
  let : CharP (BIntegers ⧸ Q) 5 := bResidue_charP 5 Q hunder
  let : Algebra (ZMod 5) (BIntegers ⧸ Q) := ZMod.algebra _ 5
  let : IsScalarTower ℤ (ZMod 5) (BIntegers ⧸ Q) := inferInstance
  let K := BIntegers ⧸ Q
  have hcomp : (algebraMap (ZMod 5) K).comp (Int.castRingHom (ZMod 5)) =
      algebraMap ℤ K := by
    ext n
    simp
  have hpoly : invariantB5.map (algebraMap (ZMod 5) K) =
      invariantBMonicTransform.map (algebraMap ℤ K) := by
    rw [← invariantBMonicTransform_mod5, Polynomial.map_map, hcomp]
  have hsplit : (invariantB5.map (algebraMap (ZMod 5) K)).Splits := by
    rw [hpoly]
    have hs := bMonicInteger_splits.map (Ideal.Quotient.mk Q)
    have hcompInt : (Ideal.Quotient.mk Q).comp (algebraMap ℤ BIntegers) =
        algebraMap ℤ K := by
      ext n
      rfl
    simpa only [Polynomial.map_map, hcompInt] using hs
  let : Fact ((invariantB5.map (algebraMap (ZMod 5) K)).Splits) := ⟨hsplit⟩
  have hset : invariantB5.rootSet K = invariantBMonicTransform.rootSet K :=
    bMonic_mod5_rootSet_eq K
  let e : invariantB5.rootSet K ≃ invariantBMonicTransform.rootSet K :=
    { toFun := fun x => ⟨x.1, by
        rw [← hset]
        exact x.2⟩
      invFun := fun x => ⟨x.1, by
        rw [hset]
        exact x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  let g : Equiv.Perm (invariantBMonicTransform.rootSet K) :=
    e.permCongrHom (finiteFieldFrobPermIn invariantB5 K)
  have he (y : invariantB5.rootSet K) : ((e y : invariantBMonicTransform.rootSet K) : K) =
      (y : K) := rfl
  have he' (y : invariantBMonicTransform.rootSet K) : ((e.symm y : invariantB5.rootSet K) : K) =
      (y : K) := by
    have h := he (e.symm y)
    rw [e.apply_symm_apply] at h
    exact h.symm
  have hgpow (x : invariantBMonicTransform.rootSet K) :
      (g x).1 = (x.1 : K) ^ 5 := by
    have h := finiteFieldFrobPermIn_apply invariantB5 K (e.symm x)
    rw [he' x, ZMod.card] at h
    change ((e (finiteFieldFrobPermIn invariantB5 K (e.symm x)) :
      invariantBMonicTransform.rootSet K) : K) = _
    rw [he]
    exact h
  have hgcycle : g.IsCycle := by
    apply isCycle_of_equivariant_equiv e.symm g
      (finiteFieldFrobPermIn invariantB5 K)
    · intro x
      simp only [g, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
        Equiv.symm_apply_apply]
    · exact finiteFieldFrobPermIn_isCycle invariantB5 K B_mod5_cycle8
        (by rw [b5_natDegree]; decide)
  have hgsupport : g.support.card = 8 := by
    have heq := support_card_eq_of_equivariant_equiv e
      (finiteFieldFrobPermIn invariantB5 K) g (by
        intro y
        simp only [g, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
          Equiv.symm_apply_apply])
    rw [finiteFieldFrobPermIn_support_card invariantB5 K B_mod5_cycle8
      (by rw [b5_natDegree]; decide), b5_natDegree] at heq
    exact heq.symm
  refine ⟨σ, bMonic_arithFrob_cycle_transfer 5 Q hunder
    bMonic_mod5_separable σ hσ g hgpow hgcycle, ?_⟩
  exact (bMonic_arithFrob_support_transfer 5 Q hunder
    bMonic_mod5_separable σ hσ g hgpow).trans hgsupport

end Biunimodular.F11
