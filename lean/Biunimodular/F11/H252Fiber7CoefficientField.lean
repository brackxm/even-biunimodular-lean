/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.AdjoinRootMonicMap
import Biunimodular.F11.H252Fiber7CoefficientIrreducibility

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
noncomputable section
open Polynomial

instance h252Fiber7PrimeGreaterThanOne : Fact (1 < 353) := ⟨by decide⟩
instance h252Fiber7IrreducibleFact : Fact (Irreducible h252Fiber7PolynomialQ) := ⟨h252Fiber7Polynomial_irreducible_Q⟩

abbrev H252Fiber7IntegralRing := AdjoinRoot h252Fiber7PolynomialZ
abbrev H252Fiber7CoefficientField := AdjoinRoot h252Fiber7PolynomialQ

def h252Fiber7IntegralEmbedding : H252Fiber7IntegralRing →+* H252Fiber7CoefficientField :=
  AdjoinRoot.map (Int.castRingHom ℚ) h252Fiber7PolynomialZ
    h252Fiber7PolynomialQ dvd_rfl

theorem h252Fiber7IntegralEmbedding_injective :
    Function.Injective h252Fiber7IntegralEmbedding := by
  exact adjoinRoot_monic_map_injective (Int.castRingHom ℚ)
    (Int.cast_injective) h252Fiber7PolynomialZ h252Fiber7Polynomial_monic

theorem h252Fiber7_modular_root :
    integerCoefficientEval (140 : ZMod 353) h252Fiber7MonicCoeffs = 0 := by
  native_decide

theorem h252Fiber7PolynomialZ_modular_root :
    h252Fiber7PolynomialZ.eval₂ (Int.castRingHom (ZMod 353)) 140 = 0 := by
  change (eval₂RingHom (Int.castRingHom (ZMod 353)) 140)
    (integerCoefficientEval X h252Fiber7MonicCoeffs) = 0
  rw [integerCoefficientEval_map]
  simpa using h252Fiber7_modular_root

def h252Fiber7ModularReduction : H252Fiber7IntegralRing →+* ZMod 353 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 353)) 140
    h252Fiber7PolynomialZ_modular_root

theorem h252Fiber7ModularReduction_root :
    h252Fiber7ModularReduction (AdjoinRoot.root h252Fiber7PolynomialZ) = 140 := by
  exact AdjoinRoot.lift_root _

theorem h252Fiber7IntegralEmbedding_root :
    h252Fiber7IntegralEmbedding (AdjoinRoot.root h252Fiber7PolynomialZ) =
      AdjoinRoot.root h252Fiber7PolynomialQ := by
  exact AdjoinRoot.map_root _ _ _ _

theorem h252Fiber7PolynomialQ_explicit :
    h252Fiber7PolynomialQ = integerCoefficientEval (X : Polynomial ℚ) h252Fiber7MonicCoeffs := by
  change (Polynomial.mapRingHom (Int.castRingHom ℚ))
    (integerCoefficientEval X h252Fiber7MonicCoeffs) = _
  rw [integerCoefficientEval_map]
  simp only [coe_mapRingHom, map_X]

def h252Fiber7RationalRootHom
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252Fiber7MonicCoeffs = 0) :
    H252Fiber7CoefficientField →+* R :=
  AdjoinRoot.lift (algebraMap ℚ R) a (by
    rw [h252Fiber7PolynomialQ_explicit]
    change (eval₂RingHom (algebraMap ℚ R) a)
      (integerCoefficientEval X h252Fiber7MonicCoeffs) = 0
    rw [integerCoefficientEval_map]
    simpa using h)

theorem h252Fiber7RationalRootHom_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252Fiber7MonicCoeffs = 0) :
    h252Fiber7RationalRootHom a h (AdjoinRoot.root h252Fiber7PolynomialQ) = a := by
  exact AdjoinRoot.lift_root _

def h252Fiber7OriginalRootHom
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ7 = 0) : H252Fiber7CoefficientField →+* R :=
  h252Fiber7RationalRootHom ((h252Fiber7RootScale : R)*a) (by
    rw [h252Fiber7MonicTransform_eval, h, mul_zero])

theorem h252Fiber7OriginalRootHom_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ7 = 0) :
    h252Fiber7OriginalRootHom a h (AdjoinRoot.root h252Fiber7PolynomialQ) =
      (h252Fiber7RootScale : R)*a := by
  exact h252Fiber7RationalRootHom_root _ _

end
end Biunimodular.F11
