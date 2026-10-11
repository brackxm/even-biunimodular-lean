/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Concrete cyclotomic model for the conductor-77 arithmetic

We use mathlib's canonical `CyclotomicField 77 ℚ` and its canonical maximal real
subfield. The A-sector model identifies the
period field and squared-coordinate generator inside these concrete types.
-/

/-- The canonical conductor-77 cyclotomic field over `ℚ`. -/
abbrev Conductor77Cyclotomic := CyclotomicField 77 ℚ

/-- The canonical maximal real subfield, as a field type. -/
abbrev Conductor77MaxReal :=
  ↥(NumberField.maximalRealSubfield Conductor77Cyclotomic)

local instance conductor77_neZero_rat : NeZero (77 : ℚ) := ⟨by norm_num⟩

local instance conductor77_cyclotomic :
    IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

example : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  conductor77_cyclotomic

/-- The full conductor-77 cyclotomic field is abelian Galois. -/
theorem conductor77_isAbelianGalois :
    IsAbelianGalois ℚ Conductor77Cyclotomic := by
  exact IsCyclotomicExtension.isAbelianGalois {77} ℚ Conductor77Cyclotomic

/-- Cyclotomic fields of this conductor are CM fields in current mathlib. -/
theorem conductor77_isCMField :
    NumberField.IsCMField Conductor77Cyclotomic := by
  exact IsCyclotomicExtension.Rat.isCMField Conductor77Cyclotomic (S := {77})
    ⟨77, by simp only [Set.mem_singleton_iff], by norm_num⟩

/-- The expected maximal-real degree is the elementary totient calculation. -/
theorem conductor77_expected_real_degree : Nat.totient 77 / 2 = 30 := by
  native_decide

/-- Concrete semantic interface for the project-specific A-sector
identification inside mathlib's canonical conductor-77 field. -/
structure ASectorCyclotomicModel where
  periodField : IntermediateField ℚ Conductor77Cyclotomic
  period_finrank : Module.finrank ℚ periodField = 6
  period_is_abelian : IsAbelianGalois ℚ periodField
  squaredCoordinate : Conductor77MaxReal
  coordinate_finrank :
    Module.finrank ℚ (Algebra.adjoin ℚ ({squaredCoordinate} : Set Conductor77MaxReal)) = 30

end Biunimodular.F11
