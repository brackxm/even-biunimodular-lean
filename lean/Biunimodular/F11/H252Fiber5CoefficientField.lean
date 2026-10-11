/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.AdjoinRootMonicMap
import Biunimodular.F11.H252Fiber5CoefficientIrreducibility

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

instance h252Fiber5PrimeGreaterThanOne : Fact (1 < 109) := ⟨by decide⟩
instance h252Fiber5IrreducibleFact : Fact (Irreducible h252Fiber5PolynomialQ) := ⟨h252Fiber5Polynomial_irreducible_Q⟩

abbrev H252Fiber5IntegralRing := AdjoinRoot h252Fiber5PolynomialZ
abbrev H252Fiber5CoefficientField := AdjoinRoot h252Fiber5PolynomialQ

def h252Fiber5IntegralEmbedding : H252Fiber5IntegralRing →+* H252Fiber5CoefficientField :=
  AdjoinRoot.map (Int.castRingHom ℚ) h252Fiber5PolynomialZ
    h252Fiber5PolynomialQ dvd_rfl

theorem h252Fiber5IntegralEmbedding_injective :
    Function.Injective h252Fiber5IntegralEmbedding := by
  exact adjoinRoot_monic_map_injective (Int.castRingHom ℚ)
    (Int.cast_injective) h252Fiber5PolynomialZ h252Fiber5Polynomial_monic

theorem h252Fiber5_modular_root :
    integerCoefficientEval (6 : ZMod 109) h252FiberCRTQ5 = 0 := by
  native_decide

theorem h252Fiber5PolynomialZ_modular_root :
    h252Fiber5PolynomialZ.eval₂ (Int.castRingHom (ZMod 109)) 6 = 0 := by
  change (eval₂RingHom (Int.castRingHom (ZMod 109)) 6)
    (integerCoefficientEval X h252FiberCRTQ5) = 0
  rw [integerCoefficientEval_map]
  simpa using h252Fiber5_modular_root

def h252Fiber5ModularReduction : H252Fiber5IntegralRing →+* ZMod 109 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 109)) 6
    h252Fiber5PolynomialZ_modular_root

theorem h252Fiber5ModularReduction_root :
    h252Fiber5ModularReduction (AdjoinRoot.root h252Fiber5PolynomialZ) = 6 := by
  exact AdjoinRoot.lift_root _

theorem h252Fiber5IntegralEmbedding_root :
    h252Fiber5IntegralEmbedding (AdjoinRoot.root h252Fiber5PolynomialZ) =
      AdjoinRoot.root h252Fiber5PolynomialQ := by
  exact AdjoinRoot.map_root _ _ _ _

theorem h252Fiber5PolynomialQ_explicit :
    h252Fiber5PolynomialQ = integerCoefficientEval (X : Polynomial ℚ) h252FiberCRTQ5 := by
  change (Polynomial.mapRingHom (Int.castRingHom ℚ))
    (integerCoefficientEval X h252FiberCRTQ5) = _
  rw [integerCoefficientEval_map]
  simp only [coe_mapRingHom, map_X]

def h252Fiber5RationalRootHom
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ5 = 0) :
    H252Fiber5CoefficientField →+* R :=
  AdjoinRoot.lift (algebraMap ℚ R) a (by
    rw [h252Fiber5PolynomialQ_explicit]
    change (eval₂RingHom (algebraMap ℚ R) a)
      (integerCoefficientEval X h252FiberCRTQ5) = 0
    rw [integerCoefficientEval_map]
    simpa using h)

theorem h252Fiber5RationalRootHom_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ5 = 0) :
    h252Fiber5RationalRootHom a h (AdjoinRoot.root h252Fiber5PolynomialQ) = a := by
  exact AdjoinRoot.lift_root _

end
end Biunimodular.F11
