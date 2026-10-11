/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Biunimodular.F11.ArithmeticCyclotomicModel

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Degree-forces-generation lemmas for the conductor-77 A-sector

This file removes a redundant semantic assumption from the A-side. Once an
explicit element of the maximal real conductor-77 field is known to generate a
30-dimensional simple extension over `ℚ`, equality with the whole maximal real
subfield follows formally from dimensions.
-/

open Polynomial

local instance conductor77_neZero_rat_generation : NeZero (77 : ℚ) := ⟨by norm_num⟩

local instance conductor77_cyclotomic_generation :
    IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

local instance conductor77_cm_generation :
    NumberField.IsCMField Conductor77Cyclotomic :=
  conductor77_isCMField

/-- The full conductor-77 cyclotomic field has degree `φ(77)=60` over `ℚ`. -/
theorem conductor77_cyclotomic_finrank :
    Module.finrank ℚ Conductor77Cyclotomic = 60 := by
  rw [IsCyclotomicExtension.finrank Conductor77Cyclotomic
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 77))]
  native_decide

/-- The maximal real subfield has degree 30. This is just the tower law plus
that a CM field is quadratic over its maximal real subfield. -/
theorem conductor77_maxReal_finrank :
    Module.finrank ℚ Conductor77MaxReal = 30 := by
  have hquad : Module.finrank Conductor77MaxReal Conductor77Cyclotomic = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have htower := Module.finrank_mul_finrank ℚ Conductor77MaxReal Conductor77Cyclotomic
  rw [hquad, conductor77_cyclotomic_finrank] at htower
  omega

/-- In a finite extension, a subalgebra with the full ambient degree is the top
subalgebra. -/
theorem subalgebra_eq_top_of_finrank_eq_ambient
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (E : Subalgebra K L)
    (h : Module.finrank K E = Module.finrank K L) : E = ⊤ := by
  apply Subalgebra.eq_of_le_of_finrank_eq le_top
  calc
    Module.finrank K E = Module.finrank K L := h
    _ = Module.finrank K (⊤ : Subalgebra K L) :=
      (LinearEquiv.finrank_eq
        (Subalgebra.topEquiv (R := K) (A := L)).toLinearEquiv).symm

/-- A degree-30 element in the maximal real conductor-77 field generates that
entire field. -/
theorem conductor77_coordinate_generates_maxReal
    (x : Conductor77MaxReal)
    (hx : Module.finrank ℚ (Algebra.adjoin ℚ ({x} : Set Conductor77MaxReal)) = 30) :
    Algebra.adjoin ℚ ({x} : Set Conductor77MaxReal) = ⊤ := by
  apply subalgebra_eq_top_of_finrank_eq_ambient
  rw [hx, conductor77_maxReal_finrank]

/-- Hence the generation field in `ASectorCyclotomicModel` is derivable from
its degree statement; it does not need to be supplied as independent data. -/
theorem ASectorCyclotomicModel.coordinate_generates_from_degree
    (h : ASectorCyclotomicModel) :
    Algebra.adjoin ℚ ({h.squaredCoordinate} : Set Conductor77MaxReal) = ⊤ := by
  exact conductor77_coordinate_generates_maxReal h.squaredCoordinate h.coordinate_finrank

end Biunimodular.F11
