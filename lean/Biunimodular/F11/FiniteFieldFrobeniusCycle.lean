/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic

set_option autoImplicit false
-- The proof selects a local root action instance to match `galActionHom`.

namespace Biunimodular.F11

open Polynomial

private theorem isCycle_of_transitive_powers
    {G α : Type*} [Group G] [MulAction G α] [Nontrivial α]
    (htrans : MulAction.IsPretransitive G α)
    (g : G) (hpow : ∀ h : G, ∃ n : ℕ, g ^ n = h) :
    (MulAction.toPermHom G α g).IsCycle := by
  let f := MulAction.toPermHom G α g
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  obtain ⟨h, hh⟩ := htrans.exists_smul_eq x y
  obtain ⟨n, hn⟩ := hpow h
  have hmap : f ^ n = MulAction.toPermHom G α h := by
    rw [← map_pow]
    exact congrArg (MulAction.toPermHom G α) hn
  have hfx : f x ≠ x := by
    intro heq
    have hfixed (m : ℕ) : (f ^ m) x = x := by
      induction m with
      | zero => simp
      | succ m ih => simpa [pow_succ, Equiv.Perm.mul_apply, heq] using ih
    have hxy' : x = y := by
      calc
        x = (f ^ n) x := (hfixed n).symm
        _ = y := by rw [hmap]; exact hh
    exact hxy hxy'
  refine ⟨x, hfx, ?_⟩
  intro z _
  obtain ⟨h, hh⟩ := htrans.exists_smul_eq x z
  obtain ⟨n, hn⟩ := hpow h
  have hmap : f ^ n = MulAction.toPermHom G α h := by
    rw [← map_pow]
    exact congrArg (MulAction.toPermHom G α) hn
  exact ⟨(n : ℤ), by rw [zpow_natCast, hmap]; exact hh⟩

private theorem support_eq_univ_of_transitive_powers
    {G α : Type*} [Group G] [MulAction G α] [Nontrivial α]
    [Fintype α] [DecidableEq α]
    (htrans : MulAction.IsPretransitive G α)
    (g : G) (hpow : ∀ h : G, ∃ n : ℕ, g ^ n = h) :
    (MulAction.toPermHom G α g).support = Finset.univ := by
  let f := MulAction.toPermHom G α g
  have hnonfix (x : α) : f x ≠ x := by
    intro heq
    obtain ⟨y, hxy⟩ := exists_ne x
    obtain ⟨h, hh⟩ := htrans.exists_smul_eq x y
    obtain ⟨n, hn⟩ := hpow h
    have hmap : f ^ n = MulAction.toPermHom G α h := by
      rw [← map_pow]
      exact congrArg (MulAction.toPermHom G α) hn
    have hfixed (m : ℕ) : (f ^ m) x = x := by
      induction m with
      | zero => simp
      | succ m ih => simpa [pow_succ, Equiv.Perm.mul_apply, heq] using ih
    have : x = y := by
      calc
        x = (f ^ n) x := (hfixed n).symm
        _ = y := by rw [hmap]; exact hh
    exact hxy this.symm
  ext x
  simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
  exact hnonfix x

variable {F : Type*} [Field F] [Fintype F]

/-- Arithmetic Frobenius acting on the roots of `p` in its finite-field
splitting field. -/
noncomputable def finiteFieldFrobPerm (p : F[X]) :
    Equiv.Perm (p.rootSet p.SplittingField) := by
  letI : MulAction p.Gal (p.rootSet p.SplittingField) :=
    Polynomial.Gal.galActionAux p
  letI : SMul p.Gal (p.rootSet p.SplittingField) :=
    (Polynomial.Gal.galActionAux p).toSMul
  exact MulAction.toPermHom _ _
    (FiniteField.frobeniusAlgEquivOfAlgebraic F p.SplittingField)

/-- An irreducible polynomial of degree at least two over a finite field has
one Frobenius orbit on its roots. -/
theorem finiteFieldFrobPerm_isCycle (p : F[X]) (hp : Irreducible p)
    (hdeg : 2 ≤ p.natDegree) : (finiteFieldFrobPerm p).IsCycle := by
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨SplittingField.splits p⟩
  let : MulAction p.Gal (p.rootSet p.SplittingField) :=
    Polynomial.Gal.galActionAux p
  let : SMul p.Gal (p.rootSet p.SplittingField) :=
    (Polynomial.Gal.galActionAux p).toSMul
  have hcard : Fintype.card (p.rootSet p.SplittingField) = p.natDegree :=
    Polynomial.card_rootSet_eq_natDegree
      (PerfectField.separable_of_irreducible hp) (SplittingField.splits p)
  have : Nontrivial (p.rootSet p.SplittingField) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let g : p.Gal :=
    FiniteField.frobeniusAlgEquivOfAlgebraic F p.SplittingField
  have hpow : ∀ h : p.Gal, ∃ n : ℕ, g ^ n = h := by
    intro h
    obtain ⟨n, hn⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F p.SplittingField).2 h
    exact ⟨n, hn⟩
  have htrans : MulAction.IsPretransitive p.Gal (p.rootSet p.SplittingField) := by
    refine ⟨fun x y => ?_⟩
    have hx := minpoly.eq_of_irreducible hp (mem_rootSet.mp x.2).2
    have hy := minpoly.eq_of_irreducible hp (mem_rootSet.mp y.2).2
    obtain ⟨g, hg⟩ :=
      (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
    exact ⟨g, Subtype.ext hg⟩
  exact isCycle_of_transitive_powers htrans g hpow

/-- The Frobenius cycle moves every root, so its support has the polynomial's
degree. -/
theorem finiteFieldFrobPerm_support_card (p : F[X])
    [DecidableEq (p.rootSet p.SplittingField)] (hp : Irreducible p)
    (hdeg : 2 ≤ p.natDegree) :
    (finiteFieldFrobPerm p).support.card = p.natDegree := by
  classical
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨SplittingField.splits p⟩
  let : MulAction p.Gal (p.rootSet p.SplittingField) :=
    Polynomial.Gal.galActionAux p
  let : SMul p.Gal (p.rootSet p.SplittingField) :=
    (Polynomial.Gal.galActionAux p).toSMul
  have hcard : Fintype.card (p.rootSet p.SplittingField) = p.natDegree :=
    Polynomial.card_rootSet_eq_natDegree
      (PerfectField.separable_of_irreducible hp) (SplittingField.splits p)
  have : Nontrivial (p.rootSet p.SplittingField) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let g : p.Gal :=
    FiniteField.frobeniusAlgEquivOfAlgebraic F p.SplittingField
  have hpow : ∀ h : p.Gal, ∃ n : ℕ, g ^ n = h := by
    intro h
    obtain ⟨n, hn⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F p.SplittingField).2 h
    exact ⟨n, hn⟩
  have htrans : MulAction.IsPretransitive p.Gal (p.rootSet p.SplittingField) := by
    refine ⟨fun x y => ?_⟩
    have hx := minpoly.eq_of_irreducible hp (mem_rootSet.mp x.2).2
    have hy := minpoly.eq_of_irreducible hp (mem_rootSet.mp y.2).2
    obtain ⟨g, hg⟩ :=
      (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
    exact ⟨g, Subtype.ext hg⟩
  have hfull := support_eq_univ_of_transitive_powers htrans g hpow
  change ((MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) g).support.card =
    p.natDegree)
  rw [hfull, Finset.card_univ]
  exact hcard

end Biunimodular.F11
