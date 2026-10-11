/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- Total degree followed by complementary exponents, from x back to z1.
Lexicographic comparison gives Singular's `dp` order on z1,...,z5,w,x. -/
def torusGrevlexEncoding : (Fin 7 →₀ ℕ) →+ (Fin 8 →₀ ℕ) where
  toFun d := Finsupp.equivFunOnFinite.symm
    (Fin.cons (∑ j : Fin 7, d j)
      (fun i : Fin 7 => ∑ j ∈ Finset.univ.erase i.rev, d j))
  map_zero' := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_add' a b := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [Finset.sum_add_distrib]

@[simp] theorem torusGrevlexEncoding_zero (d : Fin 7 →₀ ℕ) :
    torusGrevlexEncoding d 0 = ∑ j : Fin 7, d j := by
  simp [torusGrevlexEncoding]

@[simp] theorem torusGrevlexEncoding_succ (d : Fin 7 →₀ ℕ) (i : Fin 7) :
    torusGrevlexEncoding d i.succ = ∑ j ∈ Finset.univ.erase i.rev, d j := by
  simp [torusGrevlexEncoding]

theorem torusGrevlexEncoding_injective : Function.Injective torusGrevlexEncoding := by
  intro a b h
  have hsum := congrArg (fun d : Fin 8 →₀ ℕ => d 0) h
  simp only [torusGrevlexEncoding_zero] at hsum
  ext i
  have hexcept := congrArg (fun d : Fin 8 →₀ ℕ => d i.rev.succ) h
  simp only [torusGrevlexEncoding_succ, Fin.rev_rev] at hexcept
  have ha := Finset.sum_erase_add (Finset.univ : Finset (Fin 7)) (fun j => a j)
    (Finset.mem_univ i)
  have hb := Finset.sum_erase_add (Finset.univ : Finset (Fin 7)) (fun j => b j)
    (Finset.mem_univ i)
  omega

theorem torusGrevlexEncoding_monotone : Monotone torusGrevlexEncoding := by
  intro a b hab i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [torusGrevlexEncoding_zero]
    exact Finset.sum_le_sum (fun j _ => hab j)
  · simp only [torusGrevlexEncoding_succ]
    exact Finset.sum_le_sum (fun j _ => hab j)

def torusGrevlexEmbedding : (Fin 7 →₀ ℕ) →+
    (MonomialOrder.lex : MonomialOrder (Fin 8)).syn :=
  (MonomialOrder.lex : MonomialOrder (Fin 8)).toSyn.toAddMonoidHom.comp torusGrevlexEncoding

theorem torusGrevlexEmbedding_injective :
    Function.Injective torusGrevlexEmbedding :=
  (MonomialOrder.lex : MonomialOrder (Fin 8)).toSyn.injective.comp
    torusGrevlexEncoding_injective

def torusGrevlexEquiv : (Fin 7 →₀ ℕ) ≃+
    AddMonoidHom.mrange torusGrevlexEmbedding :=
  AddEquiv.ofBijective torusGrevlexEmbedding.mrangeRestrict
    ⟨fun a b h => torusGrevlexEmbedding_injective (congrArg Subtype.val h), by
      rintro ⟨x, a, rfl⟩
      exact ⟨a, rfl⟩⟩

def torusGrevlexOrder : MonomialOrder (Fin 7) where
  syn := AddMonoidHom.mrange torusGrevlexEmbedding
  toSyn := torusGrevlexEquiv
  toSyn_monotone := by
    intro a b hab
    change torusGrevlexEmbedding a ≤ torusGrevlexEmbedding b
    exact (MonomialOrder.lex : MonomialOrder (Fin 8)).toSyn_monotone
      (torusGrevlexEncoding_monotone hab)

end
end Biunimodular.F11
