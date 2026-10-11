/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.GroupTheory.Perm.Cycle.Basic

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-- An arithmetic Frobenius acts on the reduction of every polynomial root
by the residue-field Frobenius power. This is the rootwise bridge from the
characteristic-zero Galois action to the modular cycle computations. -/
theorem arithFrob_root_reduction
    {R S G : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (p : R[X]) (Q : Ideal S) (σ : G)
    (hσ : IsArithFrobAt R σ Q) (x : p.rootSet S) :
    Ideal.Quotient.mk Q ((σ • x).1) =
      (Ideal.Quotient.mk Q x.1) ^ Nat.card (R ⧸ Q.under R) := by
  simpa only [Polynomial.rootSet.coe_smul, MulSemiringAction.toAlgHom_apply] using
    hσ.mk_apply x.1

/-- Reducing an integral root of a monic polynomial modulo a prime ideal
produces a root of the reduced polynomial. -/
theorem monic_root_reduction_mem
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (p : R[X]) (hp : p.Monic) (Q : Ideal S) [Q.IsPrime]
    (x : p.rootSet S) :
    Ideal.Quotient.mk Q x.1 ∈ p.rootSet (S ⧸ Q) := by
  rw [hp.mem_rootSet]
  rw [← Ideal.Quotient.mkₐ_eq_mk (R₁ := R) Q]
  rw [aeval_algHom_apply]
  rw [(hp.mem_rootSet).mp x.2]
  exact map_zero _

/-- Reduction of the root set of a monic polynomial at a prime ideal. -/
noncomputable def monicRootReduction
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (p : R[X]) (hp : p.Monic) (Q : Ideal S) [Q.IsPrime] :
    p.rootSet S → p.rootSet (S ⧸ Q) :=
  fun x => ⟨Ideal.Quotient.mk Q x.1, monic_root_reduction_mem p hp Q x⟩

/-- The exact arithmetic condition needed for reduction to distinguish the
original roots is that no difference of distinct roots lies in the prime. -/
theorem monicRootReduction_injective_iff
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (p : R[X]) (hp : p.Monic) (Q : Ideal S) [Q.IsPrime] :
    Function.Injective (monicRootReduction p hp Q) ↔
      ∀ x y : p.rootSet S, x ≠ y → x.1 - y.1 ∉ Q := by
  constructor
  · intro hinj x y hxy hmem
    apply hxy
    apply hinj
    apply Subtype.ext
    exact Ideal.Quotient.eq.mpr hmem
  · intro hsep x y hxy
    by_contra hne
    exact hsep x y hne (Ideal.Quotient.eq.mp (Subtype.ext_iff.mp hxy))

/-- If a monic polynomial splits before reduction and its reduction is
separable, distinct roots remain distinct modulo the prime. -/
theorem monicRootReduction_injective_of_separable
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (p : R[X]) (hp : p.Monic) (Q : Ideal S) [Q.IsPrime]
    (hsplit : (p.map (algebraMap R S)).Splits)
    (hsep : (p.map (algebraMap R (S ⧸ Q))).Separable) :
    Function.Injective (monicRootReduction p hp Q) := by
  classical
  let pS : S[X] := p.map (algebraMap R S)
  have hroots : pS.roots.card = pS.natDegree :=
    hsplit.natDegree_eq_card_roots.symm
  have hmap : pS.roots.map (Ideal.Quotient.mk Q) =
      (pS.map (Ideal.Quotient.mk Q)).roots :=
    (hp.map (algebraMap R S)).roots_map_of_card_eq_natDegree
      (Ideal.Quotient.mk Q) hroots
  have hcomp : (Ideal.Quotient.mk Q).comp (algebraMap R S) =
      algebraMap R (S ⧸ Q) := by
    ext r
    rfl
  have hsep' : (pS.map (Ideal.Quotient.mk Q)).Separable := by
    simpa only [pS, map_map, hcomp] using hsep
  have hnd : (pS.roots.map (Ideal.Quotient.mk Q)).Nodup := by
    rw [hmap]
    exact Polynomial.nodup_roots hsep'
  intro x y hxy
  apply Subtype.ext
  apply Multiset.inj_on_of_nodup_map hnd
  · simpa [pS, rootSet_def, aroots_def] using x.property
  · simpa [pS, rootSet_def, aroots_def] using y.property
  · exact Subtype.ext_iff.mp hxy

/-- If reduction separates the roots and both root sets have the same
cardinality, it identifies the characteristic-zero and residue root sets. -/
noncomputable def monicRootReductionEquiv
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (p : R[X]) (hp : p.Monic) (Q : Ideal S) [Q.IsPrime]
    (hinj : Function.Injective (monicRootReduction p hp Q))
    (hcard : Fintype.card (p.rootSet S) = Fintype.card (p.rootSet (S ⧸ Q))) :
    p.rootSet S ≃ p.rootSet (S ⧸ Q) := by
  apply Equiv.ofBijective (monicRootReduction p hp Q)
  refine ⟨hinj, ?_⟩
  by_contra hsurj
  have hlt := Fintype.card_lt_of_injective_not_surjective
    (monicRootReduction p hp Q) hinj hsurj
  omega

/-- The reduction map intertwines an arithmetic Frobenius element with
raising to the cardinality of the base residue field. -/
theorem monicRootReduction_arithFrob
    {R S G : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (p : R[X]) (hp : p.Monic) (Q : Ideal S) [Q.IsPrime]
    (σ : G) (hσ : IsArithFrobAt R σ Q) (x : p.rootSet S) :
    (monicRootReduction p hp Q (σ • x)).1 =
      (monicRootReduction p hp Q x).1 ^ Nat.card (R ⧸ Q.under R) :=
  arithFrob_root_reduction p Q σ hσ x

/-- A bijection that intertwines two permutations transfers the property of
being a single cycle. -/
theorem isCycle_of_equivariant_equiv
    {α β : Type*} (e : α ≃ β) (f : Equiv.Perm α) (g : Equiv.Perm β)
    (he : ∀ x, e (f x) = g (e x)) (hg : g.IsCycle) : f.IsCycle := by
  have hconj : e.permCongrHom f = g := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      e.symm_apply_apply] using he x
  obtain ⟨y, hy, hall⟩ := hg
  let x : α := e.symm y
  have hx : f x ≠ x := by
    intro hfx
    apply hy
    have := he x
    simpa [x, hfx] using this.symm
  refine ⟨x, hx, ?_⟩
  intro z hz
  have hez : g (e z) ≠ e z := by
    intro hgz
    apply hz
    apply e.injective
    simpa [hgz] using he z
  obtain ⟨i, hi⟩ := hall hez
  refine ⟨i, ?_⟩
  apply e.injective
  have hpow := congrArg (fun k : Equiv.Perm β => k ^ i) hconj
  rw [← map_zpow] at hpow
  have happ := congrArg (fun k : Equiv.Perm β => k (e x)) hpow
  have hi' : (g ^ i) (e x) = e z := by simpa [x] using hi
  simpa only [Equiv.permCongrHom_coe, Equiv.permCongr_apply,
    e.symm_apply_apply, e.apply_symm_apply] using happ.trans hi'

/-- An equivariant bijection also preserves the number of moved roots. -/
theorem support_card_eq_of_equivariant_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (f : Equiv.Perm α) (g : Equiv.Perm β)
    (he : ∀ x, e (f x) = g (e x)) :
    f.support.card = g.support.card := by
  have hs : g.support = f.support.map e.toEmbedding := by
    ext y
    constructor
    · intro hy
      let x := e.symm y
      apply Finset.mem_map.mpr
      refine ⟨x, ?_, e.apply_symm_apply y⟩
      apply Equiv.Perm.mem_support.mpr
      intro hfx
      apply (Equiv.Perm.mem_support.mp hy)
      simpa [x, hfx] using (he x).symm
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      apply Equiv.Perm.mem_support.mpr
      intro hgx
      apply Equiv.Perm.mem_support.mp hx
      apply e.injective
      calc
        e (f x) = g (e x) := he x
        _ = e x := hgx
  rw [hs, Finset.card_map]

/-- A Frobenius cycle on the reduced roots lifts to the original root action,
provided the reductions are distinct and exhaust the residue roots. -/
theorem arithFrob_root_cycle_of_reduction
    {R S G : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (p : R[X]) (hp : p.Monic) (Q : Ideal S) [Q.IsPrime]
    (σ : G) (hσ : IsArithFrobAt R σ Q)
    (hinj : Function.Injective (monicRootReduction p hp Q))
    (hcard : Fintype.card (p.rootSet S) = Fintype.card (p.rootSet (S ⧸ Q)))
    (τ : Equiv.Perm (p.rootSet (S ⧸ Q)))
    (hτ : ∀ y, (τ y).1 = y.1 ^ Nat.card (R ⧸ Q.under R))
    (hcycle : τ.IsCycle) :
    (MulAction.toPermHom G (p.rootSet S) σ).IsCycle := by
  let e := monicRootReductionEquiv p hp Q hinj hcard
  apply isCycle_of_equivariant_equiv e
    (MulAction.toPermHom G (p.rootSet S) σ) τ
  · intro x
    apply Subtype.ext
    change (monicRootReduction p hp Q (σ • x)).1 =
      (τ (monicRootReduction p hp Q x)).1
    rw [monicRootReduction_arithFrob p hp Q σ hσ x, hτ]
  · exact hcycle

/-- The same lift preserves the exact support size of the reduced cycle. -/
theorem arithFrob_root_support_card_of_reduction
    {R S G : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (p : R[X]) (hp : p.Monic) (Q : Ideal S) [Q.IsPrime]
    [DecidableEq (p.rootSet S)] [DecidableEq (p.rootSet (S ⧸ Q))]
    (σ : G) (hσ : IsArithFrobAt R σ Q)
    (hinj : Function.Injective (monicRootReduction p hp Q))
    (hcard : Fintype.card (p.rootSet S) = Fintype.card (p.rootSet (S ⧸ Q)))
    (τ : Equiv.Perm (p.rootSet (S ⧸ Q)))
    (hτ : ∀ y, (τ y).1 = y.1 ^ Nat.card (R ⧸ Q.under R)) :
    (MulAction.toPermHom G (p.rootSet S) σ).support.card = τ.support.card := by
  let e := monicRootReductionEquiv p hp Q hinj hcard
  apply support_card_eq_of_equivariant_equiv e
    (MulAction.toPermHom G (p.rootSet S) σ) τ
  intro x
  apply Subtype.ext
  change (monicRootReduction p hp Q (σ • x)).1 =
    (τ (monicRootReduction p hp Q x)).1
  rw [monicRootReduction_arithFrob p hp Q σ hσ x, hτ]

end Biunimodular.F11
