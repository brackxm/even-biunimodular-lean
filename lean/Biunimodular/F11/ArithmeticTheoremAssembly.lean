/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.InvariantIrreducibilityInterface
import Biunimodular.F11.ArithmeticCyclotomicModel
import Biunimodular.F11.ASectorFieldGeneration
import Biunimodular.F11.ASectorPeriodARealization
import Biunimodular.F11.ASectorInvariantConjugacy11
import Biunimodular.F11.ASectorRealTower
import Biunimodular.F11.ASectorF30CharacteristicZero
import Biunimodular.F11.ASectorX77RealCoordinate
import Biunimodular.F11.ASectorRealRelativeGalois
import Biunimodular.F11.ASectorGaloisGenerator77
import Biunimodular.F11.ASectorCyclotomicCoordinateOrbit77
import Biunimodular.F11.BSectorS8Assembly
import Biunimodular.F11.BSectorConcreteGaloisAction

set_option autoImplicit false

namespace Biunimodular.F11

open scoped IntermediateField

/-!
# Arithmetic at prime 11

The concrete A-sector cyclotomic model and the B-sector Galois cycle
certificates give `arithmeticTheoremConcrete` without additional hypotheses.
The reusable assembly functions accept the same certificates explicitly.
-/

/-- Arithmetic of the invariant factors and the A-sector squared-coordinate
model. The degree-thirty polynomial `aSectorG30` governs `4 * k²` for physical
A-sector solutions; the concrete model realizes it in `Conductor77MaxReal`. -/
structure ArithmeticTheoremCertificate where
  aPolynomialIrreducible :
    Irreducible (invariantA.map (Int.castRingHom ℚ))
  bPolynomialIrreducible :
    Irreducible (invariantB.map (Int.castRingHom ℚ))
  aInvariantPeriodField :
    ℚ⟮periodInvariantU77⟯ = conductor77PeriodField
  aQuotientRootsConjugatePeriod :
    ∀ r : FixedSliceAQuotientRoot,
      IsConjRoot ℚ (r : ℂ) periodInvariantU77Complex
  aQuotientRootFieldsArePeriodField :
    ∀ r : FixedSliceAQuotientRoot,
      Nonempty (ℚ⟮(r : ℂ)⟯ ≃ₐ[ℚ] conductor77PeriodField)
  aRealRelativeDegree :
    Module.finrank conductor77RealPeriodField Conductor77MaxReal = 5
  aRealRelativeCyclic :
    IsCyclic (Conductor77MaxReal ≃ₐ[conductor77RealPeriodField]
      Conductor77MaxReal)
  aExplicitRelativeGeneratorOrder :
    orderOf conductor77Sigma62Relative = 5
  aCanonicalC5Generator :
    conductor77RelativeGalEquivZMod5
      (Multiplicative.ofAdd (1 : ZMod 5)) =
        conductor77Sigma62Relative
  aExplicitSquaredCoordinateConjugatesDistinct :
    Function.Injective (fun i : Fin 5 =>
      (conductor77Sigma62Relative ^ i.val) aSectorX77Real)
  aGaloisDilationExponentRows :
    ∀ row ∈ aSectorPhaseExponents,
      row.map relativeGaloisExponentStep77 =
        dilateASectorExponentRow11 row
  aGaloisDilationSquaredCoordinateRows :
    ∀ row ∈ aSectorPhaseExponents,
      (row.map aSectorX77AtExponent).map conductor77Sigma62 =
        (dilateASectorExponentRow11 row).map aSectorX77AtExponent
  aSquaredCoordinatePolynomialIrreducible :
    Irreducible (aSectorG30.map (Int.castRingHom ℚ))
  aCyclotomicModel : ASectorCyclotomicModel
  aSquaredCoordinateGeneratesMaxReal :
    Algebra.adjoin ℚ ({aCyclotomicModel.squaredCoordinate} : Set Conductor77MaxReal) = ⊤
  bGaloisS8 : BSectorGaloisS8Certificate

/-- Numerical degree identities in the arithmetic theorem. -/
theorem arithmetic_degree_data :
    (1 : ℕ) + 6 + 8 = 15 ∧
    6 * 5 = 30 ∧
    Nat.totient 77 / 2 = 30 := by
  native_decide

/-- Both invariant-factor irreducibility statements are now unconditional. -/
theorem arithmetic_A_irreducible :
    Irreducible (invariantA.map (Int.castRingHom ℚ)) :=
  invariantA_irreducible_over_Q

theorem arithmetic_B_irreducible :
    Irreducible (invariantB.map (Int.castRingHom ℚ)) :=
  invariantB_irreducible_over_Q

/-- Final arithmetic assembly. -/
def assemble_arithmetic_theorem
    (hAmodel : ASectorCyclotomicModel)
    (hBS8 : BSectorGaloisS8Certificate) :
    ArithmeticTheoremCertificate where
  aPolynomialIrreducible := arithmetic_A_irreducible
  bPolynomialIrreducible := arithmetic_B_irreducible
  aInvariantPeriodField := periodInvariantU77_generates_periodField
  aQuotientRootsConjugatePeriod :=
    fixedSliceAQuotientRoot_conj_periodInvariant
  aQuotientRootFieldsArePeriodField := fun r =>
    ⟨fixedSliceAQuotientRoot_fieldEquivConductor77Period r⟩
  aRealRelativeDegree := conductor77_real_relative_finrank
  aRealRelativeCyclic := conductor77_real_relative_galois_cyclic
  aExplicitRelativeGeneratorOrder := conductor77Sigma62Relative_orderOf
  aCanonicalC5Generator := conductor77RelativeGalEquivZMod5_generator
  aExplicitSquaredCoordinateConjugatesDistinct :=
    aSectorX77Real_relative_five_distinct
  aGaloisDilationExponentRows := aSectorPhaseExponents_galois_dilation
  aGaloisDilationSquaredCoordinateRows :=
    aSectorCyclotomicCoordinateRows_galois_dilation
  aSquaredCoordinatePolynomialIrreducible := aSectorG30_irreducible_over_Q
  aCyclotomicModel := hAmodel
  aSquaredCoordinateGeneratesMaxReal := hAmodel.coordinate_generates_from_degree
  bGaloisS8 := hBS8

/-- Arithmetic assembly using cycle witnesses in the actual Galois group of
the degree-eight polynomial. -/
noncomputable def assemble_arithmetic_theorem_from_b_cycles
    (hAmodel : ASectorCyclotomicModel)
    (hBcycles : BSectorGaloisCycleWitnesses) : ArithmeticTheoremCertificate :=
  assemble_arithmetic_theorem hAmodel
    (assemble_bSector_S8_from_cycle_witnesses hBcycles)

/-- Compatibility entry point accepting an A-sector model explicitly. -/
noncomputable def assemble_arithmetic_theorem_from_A_model
    (hAmodel : ASectorCyclotomicModel) : ArithmeticTheoremCertificate :=
  assemble_arithmetic_theorem hAmodel bConcreteS8Certificate

/-- Both arithmetic sectors are supplied by concrete Lean-checked models,
including exact certificates verified with native execution. -/
noncomputable def arithmeticTheoremConcrete : ArithmeticTheoremCertificate :=
  assemble_arithmetic_theorem aSectorConcreteCyclotomicModel
    bConcreteS8Certificate

/-- The exact numerical content is unconditional. -/
theorem arithmetic_theorem_numeric_summary :
    Nat.totient 77 / 2 = 30 ∧ 6 * 5 = 30 ∧ 1 + 6 + 8 = 15 := by
  native_decide

end Biunimodular.F11
