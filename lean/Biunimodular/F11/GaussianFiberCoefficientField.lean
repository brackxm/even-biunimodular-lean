/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.AdjoinRootMonicMap
import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

def gaussianFiberIntegerPolynomial : Polynomial ℤ := cyclotomic 11 ℤ
def gaussianFiberRationalPolynomial : Polynomial ℚ :=
  gaussianFiberIntegerPolynomial.map (Int.castRingHom ℚ)

instance gaussianFiberPrimeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩
instance gaussianFiberPrimeGreaterThanOne : Fact (1 < 6007) := ⟨by decide⟩

theorem gaussianFiberIntegerPolynomial_explicit :
    gaussianFiberIntegerPolynomial =
      integerCoefficientEval (X : Polynomial ℤ) [1,1,1,1,1,1,1,1,1,1,1] := by
  rw [gaussianFiberIntegerPolynomial, cyclotomic_prime]
  simp [Finset.sum_range_succ, integerCoefficientEval]
  ring

theorem gaussianFiberRationalPolynomial_irreducible :
    Irreducible gaussianFiberRationalPolynomial := by
  simpa only [gaussianFiberRationalPolynomial, gaussianFiberIntegerPolynomial,
    map_cyclotomic_int] using (cyclotomic.irreducible_rat (by decide : 0 < 11))

instance gaussianFiberIrreducibleFact : Fact (Irreducible gaussianFiberRationalPolynomial) :=
  ⟨gaussianFiberRationalPolynomial_irreducible⟩

abbrev GaussianFiberIntegralRing := AdjoinRoot gaussianFiberIntegerPolynomial
abbrev GaussianFiberCoefficientField := AdjoinRoot gaussianFiberRationalPolynomial

def gaussianFiberIntegralEmbedding : GaussianFiberIntegralRing →+* GaussianFiberCoefficientField :=
  AdjoinRoot.map (Int.castRingHom ℚ) gaussianFiberIntegerPolynomial
    gaussianFiberRationalPolynomial dvd_rfl

theorem gaussianFiberIntegralEmbedding_injective :
    Function.Injective gaussianFiberIntegralEmbedding := by
  exact adjoinRoot_monic_map_injective (Int.castRingHom ℚ)
    (Int.cast_injective) gaussianFiberIntegerPolynomial (cyclotomic.monic 11 ℤ)

theorem gaussianFiber_modular_root :
    integerCoefficientEval (3088 : ZMod 6007) [1,1,1,1,1,1,1,1,1,1,1] = 0 := by
  native_decide

theorem gaussianFiberIntegerPolynomial_modular_root :
    gaussianFiberIntegerPolynomial.eval₂ (Int.castRingHom (ZMod 6007)) 3088 = 0 := by
  rw [gaussianFiberIntegerPolynomial_explicit]
  change (eval₂RingHom (Int.castRingHom (ZMod 6007)) 3088)
    (integerCoefficientEval X [1,1,1,1,1,1,1,1,1,1,1]) = 0
  rw [integerCoefficientEval_map]
  simpa using gaussianFiber_modular_root

def gaussianFiberModularReduction : GaussianFiberIntegralRing →+* ZMod 6007 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 6007)) 3088
    gaussianFiberIntegerPolynomial_modular_root

theorem gaussianFiberModularReduction_root :
    gaussianFiberModularReduction (AdjoinRoot.root gaussianFiberIntegerPolynomial) = 3088 := by
  exact AdjoinRoot.lift_root _

theorem gaussianFiberIntegralEmbedding_root :
    gaussianFiberIntegralEmbedding (AdjoinRoot.root gaussianFiberIntegerPolynomial) =
      AdjoinRoot.root gaussianFiberRationalPolynomial := by
  exact AdjoinRoot.map_root _ _ _ _

theorem gaussianFiberRationalPolynomial_explicit :
    gaussianFiberRationalPolynomial =
      integerCoefficientEval (X : Polynomial ℚ) [1,1,1,1,1,1,1,1,1,1,1] := by
  rw [gaussianFiberRationalPolynomial, gaussianFiberIntegerPolynomial,
    map_cyclotomic_int, cyclotomic_prime]
  simp [Finset.sum_range_succ, integerCoefficientEval]
  ring

def gaussianFiberRationalRootHom
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a [1,1,1,1,1,1,1,1,1,1,1] = 0) :
    GaussianFiberCoefficientField →+* R :=
  AdjoinRoot.lift (algebraMap ℚ R) a (by
    rw [gaussianFiberRationalPolynomial_explicit]
    change (eval₂RingHom (algebraMap ℚ R) a)
      (integerCoefficientEval X [1,1,1,1,1,1,1,1,1,1,1]) = 0
    rw [integerCoefficientEval_map]
    simpa using h)

theorem gaussianFiberRationalRootHom_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a [1,1,1,1,1,1,1,1,1,1,1] = 0) :
    gaussianFiberRationalRootHom a h (AdjoinRoot.root gaussianFiberRationalPolynomial) = a := by
  exact AdjoinRoot.lift_root _

end
end Biunimodular.F11
