/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.AdjoinRootMonicMap
import Biunimodular.F11.H252Fiber3CoefficientIrreducibility

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

instance h252Fiber3PrimeGreaterThanOne : Fact (1 < 103) := ⟨by decide⟩
instance h252Fiber3IrreducibleFact : Fact (Irreducible h252Fiber3PolynomialQ) := ⟨h252Fiber3Polynomial_irreducible_Q⟩

abbrev H252Fiber3IntegralRing := AdjoinRoot h252Fiber3PolynomialZ
abbrev H252Fiber3CoefficientField := AdjoinRoot h252Fiber3PolynomialQ

def h252Fiber3IntegralEmbedding : H252Fiber3IntegralRing →+* H252Fiber3CoefficientField :=
  AdjoinRoot.map (Int.castRingHom ℚ) h252Fiber3PolynomialZ
    h252Fiber3PolynomialQ dvd_rfl

theorem h252Fiber3IntegralEmbedding_injective :
    Function.Injective h252Fiber3IntegralEmbedding := by
  exact adjoinRoot_monic_map_injective (Int.castRingHom ℚ)
    (Int.cast_injective) h252Fiber3PolynomialZ h252Fiber3Polynomial_monic

theorem h252Fiber3_modular_root :
    integerCoefficientEval (6 : ZMod 103) h252FiberCRTQ3 = 0 := by
  native_decide

theorem h252Fiber3PolynomialZ_modular_root :
    h252Fiber3PolynomialZ.eval₂ (Int.castRingHom (ZMod 103)) 6 = 0 := by
  change (eval₂RingHom (Int.castRingHom (ZMod 103)) 6)
    (integerCoefficientEval X h252FiberCRTQ3) = 0
  rw [integerCoefficientEval_map]
  simpa using h252Fiber3_modular_root

def h252Fiber3ModularReduction : H252Fiber3IntegralRing →+* ZMod 103 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 103)) 6
    h252Fiber3PolynomialZ_modular_root

theorem h252Fiber3ModularReduction_root :
    h252Fiber3ModularReduction (AdjoinRoot.root h252Fiber3PolynomialZ) = 6 := by
  exact AdjoinRoot.lift_root _

theorem h252Fiber3IntegralEmbedding_root :
    h252Fiber3IntegralEmbedding (AdjoinRoot.root h252Fiber3PolynomialZ) =
      AdjoinRoot.root h252Fiber3PolynomialQ := by
  exact AdjoinRoot.map_root _ _ _ _

theorem h252Fiber3PolynomialQ_explicit :
    h252Fiber3PolynomialQ = integerCoefficientEval (X : Polynomial ℚ) h252FiberCRTQ3 := by
  change (Polynomial.mapRingHom (Int.castRingHom ℚ))
    (integerCoefficientEval X h252FiberCRTQ3) = _
  rw [integerCoefficientEval_map]
  simp only [coe_mapRingHom, map_X]

def h252Fiber3RationalRootHom
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ3 = 0) :
    H252Fiber3CoefficientField →+* R :=
  AdjoinRoot.lift (algebraMap ℚ R) a (by
    rw [h252Fiber3PolynomialQ_explicit]
    change (eval₂RingHom (algebraMap ℚ R) a)
      (integerCoefficientEval X h252FiberCRTQ3) = 0
    rw [integerCoefficientEval_map]
    simpa using h)

theorem h252Fiber3RationalRootHom_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ3 = 0) :
    h252Fiber3RationalRootHom a h (AdjoinRoot.root h252Fiber3PolynomialQ) = a := by
  exact AdjoinRoot.lift_root _

end
end Biunimodular.F11
