/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorRealRelativeGalois
import Biunimodular.F11.ASectorGaloisDilationExponents11
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11

open scoped IntermediateField

noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

/-- The canonical conductor-77 Galois automorphism with exponent `62 = 6³`. -/
def conductor77Sigma62 :
    Conductor77Cyclotomic ≃ₐ[ℚ] Conductor77Cyclotomic :=
  (IsCyclotomicExtension.Rat.galEquivZMod 77 Conductor77Cyclotomic).symm
    (ZMod.unitOfCoprime 62 (by norm_num))

theorem conductor77Sigma62_zeta :
    conductor77Sigma62 zeta77 = zeta77 ^ 62 := by
  have hζ : zeta77 ^ 77 = 1 :=
    (IsCyclotomicExtension.zeta_spec 77 ℚ
      Conductor77Cyclotomic).pow_eq_one
  have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
    77 Conductor77Cyclotomic conductor77Sigma62 hζ
  have he :
      (IsCyclotomicExtension.Rat.galEquivZMod 77 Conductor77Cyclotomic
        conductor77Sigma62).val.val = 62 := by
    simp only [conductor77Sigma62, MulEquiv.apply_symm_apply,
      ZMod.coe_unitOfCoprime]
    native_decide
  simpa only [he] using h

/-- The exponent-62 automorphism fixes the ten-term Gaussian period. -/
theorem conductor77Sigma62_periodEta :
    conductor77Sigma62 periodEta77 = periodEta77 := by
  have hζ : zeta77 ^ 77 = 1 :=
    (IsCyclotomicExtension.zeta_spec 77 ℚ
      Conductor77Cyclotomic).pow_eq_one
  have hp (n : ℕ) : (zeta77 ^ 62) ^ n =
      zeta77 ^ ((62 * n) % 77) := by
    rw [← pow_mul, pow_eq_pow_mod _ hζ]
  have hη : periodEta77 =
      zeta77 ^ 1 + zeta77 ^ 6 + zeta77 ^ 13 +
      zeta77 ^ 15 + zeta77 ^ 36 + zeta77 ^ 41 +
      zeta77 ^ 62 + zeta77 ^ 64 + zeta77 ^ 71 +
      zeta77 ^ 76 := by
    simp [periodEta77, conductor77PeriodPolynomial]
  rw [hη]
  simp only [map_add, map_pow, conductor77Sigma62_zeta]
  simp only [hp]
  norm_num
  ring

/-- The exponent-62 automorphism fixes the entire period sextic field. -/
theorem conductor77Sigma62_fixes_periodField
    (x : conductor77PeriodField) :
    conductor77Sigma62 (x : Conductor77Cyclotomic) = x := by
  let incl : conductor77PeriodField →ₐ[ℚ] Conductor77Cyclotomic :=
    IsScalarTower.toAlgHom ℚ conductor77PeriodField Conductor77Cyclotomic
  have hhom : conductor77Sigma62.toAlgHom.comp incl = incl := by
    change (conductor77Sigma62.toAlgHom.comp incl :
      ℚ⟮periodEta77⟯ →ₐ[ℚ] Conductor77Cyclotomic) = incl
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact conductor77Sigma62_periodEta
  exact congrArg (fun f : conductor77PeriodField →ₐ[ℚ]
    Conductor77Cyclotomic => f x) hhom

/-- The maximal-real field as an intermediate field in the full
conductor-77 cyclotomic extension. -/
def conductor77RealIntermediate :
    IntermediateField ℚ Conductor77Cyclotomic :=
  (NumberField.maximalRealSubfield Conductor77Cyclotomic).toIntermediateField
    (by intro q; exact SubfieldClass.ratCast_mem _ q)

local instance : IsAbelianGalois ℚ Conductor77Cyclotomic :=
  conductor77_isAbelianGalois

local instance : NumberField.IsCMField Conductor77Cyclotomic :=
  conductor77_isCMField

local instance : Normal ℚ conductor77RealIntermediate := by
  infer_instance

/-- Restriction of the exponent-62 automorphism to the maximal real field. -/
def conductor77Sigma62Real :
    Conductor77MaxReal ≃ₐ[ℚ] Conductor77MaxReal :=
  conductor77Sigma62.restrictNormal conductor77RealIntermediate

theorem conductor77Sigma62Real_periodEta :
    conductor77Sigma62Real periodEta77Real = periodEta77Real := by
  apply Subtype.ext
  have h := AlgEquiv.restrictNormal_apply
    conductor77RealIntermediate conductor77Sigma62 periodEta77Real
  change (conductor77Sigma62.restrictNormal conductor77RealIntermediate
    periodEta77Real).1 = periodEta77
  exact h.trans conductor77Sigma62_periodEta

theorem conductor77Sigma62Real_fixes_periodField
    (x : conductor77RealPeriodField) :
    conductor77Sigma62Real (x : Conductor77MaxReal) = x := by
  let incl : conductor77RealPeriodField →ₐ[ℚ] Conductor77MaxReal :=
    IsScalarTower.toAlgHom ℚ conductor77RealPeriodField Conductor77MaxReal
  have hhom : conductor77Sigma62Real.toAlgHom.comp incl = incl := by
    change (conductor77Sigma62Real.toAlgHom.comp incl :
      ℚ⟮periodEta77Real⟯ →ₐ[ℚ] Conductor77MaxReal) = incl
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact conductor77Sigma62Real_periodEta
  exact congrArg (fun f : conductor77RealPeriodField →ₐ[ℚ]
    Conductor77MaxReal => f x) hhom

/-- The explicitly selected relative Galois element over the period sextic. -/
def conductor77Sigma62Relative :
    Conductor77MaxReal ≃ₐ[conductor77RealPeriodField]
      Conductor77MaxReal :=
  AlgEquiv.ofRingEquiv (f := conductor77Sigma62Real.toRingEquiv)
    conductor77Sigma62Real_fixes_periodField

/-- The selected relative automorphism has order dividing five. -/
theorem conductor77Sigma62Relative_pow_five :
    conductor77Sigma62Relative ^ 5 = 1 := by
  simpa only [conductor77_real_relative_galois_card] using
    (pow_card_eq_one' (x := conductor77Sigma62Relative))

/-- The exponent-62 automorphism does not square to the identity in the
full cyclotomic field. -/
theorem conductor77Sigma62_sq_ne_one : conductor77Sigma62 ^ 2 ≠ 1 := by
  intro h
  have hunit := congrArg
    (IsCyclotomicExtension.Rat.galEquivZMod 77 Conductor77Cyclotomic) h
  have he :
      (IsCyclotomicExtension.Rat.galEquivZMod 77 Conductor77Cyclotomic
        conductor77Sigma62) = ZMod.unitOfCoprime 62 (by norm_num) := by
    exact (IsCyclotomicExtension.Rat.galEquivZMod 77
      Conductor77Cyclotomic).apply_symm_apply _
  rw [map_pow, map_one, he] at hunit
  have hne :
      (ZMod.unitOfCoprime 62 (by norm_num) : (ZMod 77)ˣ) ^ 2 ≠ 1 := by
    native_decide
  exact hne hunit

/-- The exponent-62 map acts nontrivially on the maximal real field. -/
theorem conductor77Sigma62Real_ne_one : conductor77Sigma62Real ≠ 1 := by
  intro hreal
  have hfix (x : Conductor77MaxReal) :
      conductor77Sigma62 (x : Conductor77Cyclotomic) = x := by
    have hx := congrArg (fun f : Conductor77MaxReal ≃ₐ[ℚ]
      Conductor77MaxReal => f x) hreal
    simp only [AlgEquiv.one_apply] at hx
    have hr := AlgEquiv.restrictNormal_apply
      conductor77RealIntermediate conductor77Sigma62 x
    exact hr.symm.trans (congrArg Subtype.val hx)
  let τ : Conductor77Cyclotomic ≃ₐ[Conductor77MaxReal]
      Conductor77Cyclotomic :=
    AlgEquiv.ofRingEquiv (f := conductor77Sigma62.toRingEquiv) hfix
  have hcard : Nat.card
      (Conductor77Cyclotomic ≃ₐ[Conductor77MaxReal]
        Conductor77Cyclotomic) = 2 := by
    let _ : IsGalois Conductor77MaxReal Conductor77Cyclotomic :=
      IsGalois.tower_top_of_isGalois ℚ Conductor77MaxReal Conductor77Cyclotomic
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hτ : τ ^ 2 = 1 := by
    simpa only [hcard] using (pow_card_eq_one' (x := τ))
  apply conductor77Sigma62_sq_ne_one
  ext x
  have hx := congrArg (fun f : Conductor77Cyclotomic ≃ₐ[Conductor77MaxReal]
    Conductor77Cyclotomic => f x) hτ
  change (conductor77Sigma62 ^ 2) x = x at hx
  simpa only [AlgEquiv.one_apply] using hx

/-- Exponent `62` is a generator of the order-five relative Galois group. -/
theorem conductor77Sigma62Relative_orderOf :
    orderOf conductor77Sigma62Relative = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · exact conductor77Sigma62Relative_pow_five
  · intro hrel
    apply conductor77Sigma62Real_ne_one
    ext x
    have hx := congrArg (fun f : Conductor77MaxReal ≃ₐ[conductor77RealPeriodField]
      Conductor77MaxReal => f x) hrel
    change conductor77Sigma62Real x = x at hx
    exact congrArg Subtype.val hx

/-- On the explicit degree-thirty coordinate the Galois map substitutes
`ζ₇₇ ↦ ζ₇₇⁶²` in its exact cyclotomic expression. -/
theorem conductor77Sigma62_aSectorX77 :
    conductor77Sigma62 aSectorX77 =
      aSectorX77Pair (zeta77 ^ 62) := by
  simp [aSectorX77, aSectorX77Pair, map_sum, map_add, map_mul,
    map_pow, map_intCast, map_ofNat, conductor77Sigma62_zeta]

theorem conductor77Sigma62Relative_aSectorX77Real :
    ((conductor77Sigma62Relative aSectorX77Real) :
      Conductor77Cyclotomic) = aSectorX77Pair (zeta77 ^ 62) := by
  have hr := AlgEquiv.restrictNormal_apply
    conductor77RealIntermediate conductor77Sigma62 aSectorX77Real
  change ((conductor77Sigma62Real aSectorX77Real) :
    Conductor77Cyclotomic) = conductor77Sigma62 aSectorX77 at hr
  exact hr.trans conductor77Sigma62_aSectorX77

/-- The explicit degree-thirty coordinate detects every relative Galois
automorphism. -/
theorem aSectorX77Real_relative_action_faithful
    (g h : Conductor77MaxReal ≃ₐ[conductor77RealPeriodField]
      Conductor77MaxReal)
    (hx : g aSectorX77Real = h aSectorX77Real) : g = h := by
  have hhom : (g.restrictScalars ℚ).toAlgHom =
      (h.restrictScalars ℚ).toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top aSectorX77Real_generates_maxReal
    intro x hxmem
    have heq : x = aSectorX77Real := Set.mem_singleton_iff.mp hxmem
    subst x
    exact hx
  ext x
  have hh := congrArg (fun f : Conductor77MaxReal →ₐ[ℚ]
    Conductor77MaxReal => f x) hhom
  change g x = h x at hh
  exact congrArg Subtype.val hh

/-- The five conjugates of the explicit real coordinate under exponent `62`
are pairwise distinct. -/
theorem aSectorX77Real_relative_five_distinct :
    Function.Injective (fun i : Fin 5 =>
      (conductor77Sigma62Relative ^ i.val) aSectorX77Real) := by
  intro i j hij
  have hequiv : conductor77Sigma62Relative ^ i.val =
      conductor77Sigma62Relative ^ j.val :=
    aSectorX77Real_relative_action_faithful _ _ hij
  apply Fin.ext
  exact pow_injOn_Iio_orderOf
    (by simp [conductor77Sigma62Relative_orderOf, i.isLt])
    (by simp [conductor77Sigma62Relative_orderOf, j.isLt])
    hequiv

/-- The canonical relative `C₅` identification sends its additive generator
to the explicit exponent-62 automorphism. -/
noncomputable def conductor77RelativeGalEquivZMod5 :
    Multiplicative (ZMod 5) ≃*
      (Conductor77MaxReal ≃ₐ[conductor77RealPeriodField]
        Conductor77MaxReal) := by
  have hz : Subgroup.zpowers conductor77Sigma62Relative = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top
      (Subgroup.zpowers conductor77Sigma62Relative)).mp
    simpa only [Nat.card_zpowers, conductor77Sigma62Relative_orderOf] using
      conductor77_real_relative_galois_card.symm
  exact zmodMulEquivOfGenerator
    (g := conductor77Sigma62Relative)
    (fun x => hz.ge (Subgroup.mem_top x))
    conductor77_real_relative_galois_card

@[simp] theorem conductor77RelativeGalEquivZMod5_generator :
    conductor77RelativeGalEquivZMod5
      (Multiplicative.ofAdd (1 : ZMod 5)) =
        conductor77Sigma62Relative := by
  exact zmodMulEquivOfGenerator_apply_ofAdd_one _ _

end
end Biunimodular.F11
