/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.AdjoinRootMonicMap
import Biunimodular.F11.H252Fiber6CoefficientIrreducibility

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
noncomputable section
open Polynomial

instance h252Fiber6PrimeGreaterThanOne : Fact (1 < 307) := ⟨by decide⟩
instance h252Fiber6IrreducibleFact : Fact (Irreducible h252Fiber6PolynomialQ) := ⟨h252Fiber6Polynomial_irreducible_Q⟩

abbrev H252Fiber6IntegralRing := AdjoinRoot h252Fiber6PolynomialZ
abbrev H252Fiber6CoefficientField := AdjoinRoot h252Fiber6PolynomialQ

def h252Fiber6IntegralEmbedding : H252Fiber6IntegralRing →+* H252Fiber6CoefficientField :=
  AdjoinRoot.map (Int.castRingHom ℚ) h252Fiber6PolynomialZ
    h252Fiber6PolynomialQ dvd_rfl

theorem h252Fiber6IntegralEmbedding_injective :
    Function.Injective h252Fiber6IntegralEmbedding := by
  exact adjoinRoot_monic_map_injective (Int.castRingHom ℚ)
    (Int.cast_injective) h252Fiber6PolynomialZ h252Fiber6Polynomial_monic

theorem h252Fiber6_modular_root :
    integerCoefficientEval (29 : ZMod 307) h252FiberCRTQ6 = 0 := by
  native_decide

theorem h252Fiber6PolynomialZ_modular_root :
    h252Fiber6PolynomialZ.eval₂ (Int.castRingHom (ZMod 307)) 29 = 0 := by
  change (eval₂RingHom (Int.castRingHom (ZMod 307)) 29)
    (integerCoefficientEval X h252FiberCRTQ6) = 0
  rw [integerCoefficientEval_map]
  simpa using h252Fiber6_modular_root

def h252Fiber6ModularReduction : H252Fiber6IntegralRing →+* ZMod 307 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 307)) 29
    h252Fiber6PolynomialZ_modular_root

theorem h252Fiber6ModularReduction_root :
    h252Fiber6ModularReduction (AdjoinRoot.root h252Fiber6PolynomialZ) = 29 := by
  exact AdjoinRoot.lift_root _

theorem h252Fiber6IntegralEmbedding_root :
    h252Fiber6IntegralEmbedding (AdjoinRoot.root h252Fiber6PolynomialZ) =
      AdjoinRoot.root h252Fiber6PolynomialQ := by
  exact AdjoinRoot.map_root _ _ _ _

theorem h252Fiber6PolynomialQ_explicit :
    h252Fiber6PolynomialQ = integerCoefficientEval (X : Polynomial ℚ) h252FiberCRTQ6 := by
  change (Polynomial.mapRingHom (Int.castRingHom ℚ))
    (integerCoefficientEval X h252FiberCRTQ6) = _
  rw [integerCoefficientEval_map]
  simp only [coe_mapRingHom, map_X]

def h252Fiber6RationalRootHom
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ6 = 0) :
    H252Fiber6CoefficientField →+* R :=
  AdjoinRoot.lift (algebraMap ℚ R) a (by
    rw [h252Fiber6PolynomialQ_explicit]
    change (eval₂RingHom (algebraMap ℚ R) a)
      (integerCoefficientEval X h252FiberCRTQ6) = 0
    rw [integerCoefficientEval_map]
    simpa using h)

theorem h252Fiber6RationalRootHom_root
    {R : Type*} [CommRing R] [Algebra ℚ R] (a : R)
    (h : integerCoefficientEval a h252FiberCRTQ6 = 0) :
    h252Fiber6RationalRootHom a h (AdjoinRoot.root h252Fiber6PolynomialQ) = a := by
  exact AdjoinRoot.lift_root _

end
end Biunimodular.F11
