/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.AdjoinRootMonicMap
import Biunimodular.F11.H252Fiber4CoefficientIrreducibility

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

instance h252Fiber4PrimeGreaterThanOne : Fact (1 < 109) := ⟨by decide⟩
instance h252Fiber4IrreducibleFact : Fact (Irreducible h252Fiber4PolynomialQ) := ⟨h252Fiber4Polynomial_irreducible_Q⟩

abbrev H252Fiber4IntegralRing := AdjoinRoot h252Fiber4PolynomialZ
abbrev H252Fiber4CoefficientField := AdjoinRoot h252Fiber4PolynomialQ

def h252Fiber4IntegralEmbedding : H252Fiber4IntegralRing →+* H252Fiber4CoefficientField :=
  AdjoinRoot.map (Int.castRingHom ℚ) h252Fiber4PolynomialZ
    h252Fiber4PolynomialQ dvd_rfl

theorem h252Fiber4IntegralEmbedding_injective :
    Function.Injective h252Fiber4IntegralEmbedding := by
  exact adjoinRoot_monic_map_injective (Int.castRingHom ℚ)
    (Int.cast_injective) h252Fiber4PolynomialZ h252Fiber4Polynomial_monic

theorem h252Fiber4_modular_root :
    integerCoefficientEval (2 : ZMod 109) h252FiberCRTQ4 = 0 := by
  native_decide

theorem h252Fiber4PolynomialZ_modular_root :
    h252Fiber4PolynomialZ.eval₂ (Int.castRingHom (ZMod 109)) 2 = 0 := by
  change (eval₂RingHom (Int.castRingHom (ZMod 109)) 2)
    (integerCoefficientEval X h252FiberCRTQ4) = 0
  rw [integerCoefficientEval_map]
  simpa using h252Fiber4_modular_root

def h252Fiber4ModularReduction : H252Fiber4IntegralRing →+* ZMod 109 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 109)) 2
    h252Fiber4PolynomialZ_modular_root

theorem h252Fiber4ModularReduction_root :
    h252Fiber4ModularReduction (AdjoinRoot.root h252Fiber4PolynomialZ) = 2 := by
  exact AdjoinRoot.lift_root _

theorem h252Fiber4IntegralEmbedding_root :
    h252Fiber4IntegralEmbedding (AdjoinRoot.root h252Fiber4PolynomialZ) =
      AdjoinRoot.root h252Fiber4PolynomialQ := by
  exact AdjoinRoot.map_root _ _ _ _

theorem h252Fiber4PolynomialQ_explicit :
    h252Fiber4PolynomialQ = integerCoefficientEval (X : Polynomial ℚ) h252FiberCRTQ4 := by
  change (Polynomial.mapRingHom (Int.castRingHom ℚ))
    (integerCoefficientEval X h252FiberCRTQ4) = _
  rw [integerCoefficientEval_map]
  simp only [coe_mapRingHom, map_X]

def h252Fiber4RationalRootHom
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ4 = 0) :
    H252Fiber4CoefficientField →+* R :=
  AdjoinRoot.lift (algebraMap ℚ R) a (by
    rw [h252Fiber4PolynomialQ_explicit]
    change (eval₂RingHom (algebraMap ℚ R) a)
      (integerCoefficientEval X h252FiberCRTQ4) = 0
    rw [integerCoefficientEval_map]
    simpa using h)

theorem h252Fiber4RationalRootHom_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ4 = 0) :
    h252Fiber4RationalRootHom a h (AdjoinRoot.root h252Fiber4PolynomialQ) = a := by
  exact AdjoinRoot.lift_root _

end
end Biunimodular.F11
