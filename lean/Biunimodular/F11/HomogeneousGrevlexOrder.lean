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

/-- An additive encoding of graded reverse lexicographic order on
`(x5,...,x0)`: first record total degree, then its complements to the
exponents of `(x0,...,x5)`. Lexicographic comparison of this encoding is
well founded, so no new well-foundedness axiom is needed. -/
def homogeneousGrevlexEncoding : (Fin 6 →₀ ℕ) →+ (Fin 7 →₀ ℕ) where
  toFun d := Finsupp.equivFunOnFinite.symm
    (Fin.cons (∑ j : Fin 6, d j)
      (fun i : Fin 6 => ∑ j ∈ Finset.univ.erase i, d j))
  map_zero' := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_add' a b := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [Finset.sum_add_distrib]

@[simp] theorem homogeneousGrevlexEncoding_zero (d : Fin 6 →₀ ℕ) :
    homogeneousGrevlexEncoding d 0 = ∑ j : Fin 6, d j := by
  simp [homogeneousGrevlexEncoding]

@[simp] theorem homogeneousGrevlexEncoding_succ (d : Fin 6 →₀ ℕ) (i : Fin 6) :
    homogeneousGrevlexEncoding d i.succ = ∑ j ∈ Finset.univ.erase i, d j := by
  simp [homogeneousGrevlexEncoding]

theorem homogeneousGrevlexEncoding_injective : Function.Injective homogeneousGrevlexEncoding := by
  intro a b h
  have hsum := congrArg (fun d : Fin 7 →₀ ℕ => d 0) h
  simp only [homogeneousGrevlexEncoding_zero] at hsum
  ext i
  have hexcept := congrArg (fun d : Fin 7 →₀ ℕ => d i.succ) h
  simp only [homogeneousGrevlexEncoding_succ] at hexcept
  have ha := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) (fun j => a j)
    (Finset.mem_univ i)
  have hb := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) (fun j => b j)
    (Finset.mem_univ i)
  omega

theorem homogeneousGrevlexEncoding_monotone : Monotone homogeneousGrevlexEncoding := by
  intro a b hab i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [homogeneousGrevlexEncoding_zero]
    exact Finset.sum_le_sum (fun j _ => hab j)
  · simp only [homogeneousGrevlexEncoding_succ]
    exact Finset.sum_le_sum (fun j _ => hab j)

def homogeneousGrevlexEmbedding : (Fin 6 →₀ ℕ) →+
    (MonomialOrder.lex : MonomialOrder (Fin 7)).syn :=
  (MonomialOrder.lex : MonomialOrder (Fin 7)).toSyn.toAddMonoidHom.comp homogeneousGrevlexEncoding

theorem homogeneousGrevlexEmbedding_injective :
    Function.Injective homogeneousGrevlexEmbedding :=
  (MonomialOrder.lex : MonomialOrder (Fin 7)).toSyn.injective.comp
    homogeneousGrevlexEncoding_injective

def homogeneousGrevlexEquiv : (Fin 6 →₀ ℕ) ≃+
    AddMonoidHom.mrange homogeneousGrevlexEmbedding :=
  AddEquiv.ofBijective homogeneousGrevlexEmbedding.mrangeRestrict
    ⟨fun a b h => homogeneousGrevlexEmbedding_injective (congrArg Subtype.val h), by
      rintro ⟨x, a, rfl⟩
      exact ⟨a, rfl⟩⟩

/-- The precise monomial order used by the capped Singular `dp` export. -/
def homogeneousGrevlexOrder : MonomialOrder (Fin 6) where
  syn := AddMonoidHom.mrange homogeneousGrevlexEmbedding
  toSyn := homogeneousGrevlexEquiv
  toSyn_monotone := by
    intro a b hab
    change homogeneousGrevlexEmbedding a ≤ homogeneousGrevlexEmbedding b
    exact (MonomialOrder.lex : MonomialOrder (Fin 7)).toSyn_monotone
      (homogeneousGrevlexEncoding_monotone hab)

end
end Biunimodular.F11
