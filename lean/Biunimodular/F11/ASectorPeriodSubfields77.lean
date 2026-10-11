/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodSubfieldValues77
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

set_option autoImplicit false

namespace Biunimodular.F11
open scoped IntermediateField
noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

local instance : IsAbelianGalois ℚ conductor77PeriodField :=
  conductor77PeriodField_isAbelianGalois

local instance : Normal ℚ conductor77PeriodField := by infer_instance

/-- The cyclotomic automorphism indexing the m-th Gaussian-period coset. -/
def conductor77PeriodAutomorphism (m : Fin 6) :
    Conductor77Cyclotomic ≃ₐ[ℚ] Conductor77Cyclotomic :=
  (IsCyclotomicExtension.Rat.galEquivZMod 77 Conductor77Cyclotomic).symm
    (ZMod.unitOfCoprime (3 ^ m.1) (by fin_cases m <;> norm_num))

theorem conductor77PeriodAutomorphism_zeta (m : Fin 6) :
    conductor77PeriodAutomorphism m zeta77 = zeta77 ^ (3 ^ m.1) := by
  have hζ : zeta77 ^ 77 = 1 :=
    (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic).pow_eq_one
  have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
    77 Conductor77Cyclotomic (conductor77PeriodAutomorphism m) hζ
  have he : (IsCyclotomicExtension.Rat.galEquivZMod 77 Conductor77Cyclotomic
      (conductor77PeriodAutomorphism m)).val.val = (3 ^ m.1) % 77 := by
    simp only [conductor77PeriodAutomorphism, MulEquiv.apply_symm_apply,
      ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  rw [he] at h
  exact h.trans (pow_eq_pow_mod _ hζ).symm

/-- The six literal period polynomials are actual Galois conjugates of the
chosen period, rather than just a list of finite residue cosets. -/
theorem conductor77PeriodAutomorphism_periodEta (m : Fin 6) :
    conductor77PeriodAutomorphism m periodEta77 = periodOrbit77 m := by
  have hζ : zeta77 ^ 77 = 1 :=
    (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic).pow_eq_one
  have hp (k : ℕ) : (zeta77 ^ (3 ^ m.1)) ^ k = zeta77 ^ ((3 ^ m.1 * k) % 77) := by
    rw [← pow_mul, pow_eq_pow_mod _ hζ]
  have hη : periodEta77 =
      zeta77 ^ 1 + zeta77 ^ 6 + zeta77 ^ 13 + zeta77 ^ 15 + zeta77 ^ 36 +
      zeta77 ^ 41 + zeta77 ^ 62 + zeta77 ^ 64 + zeta77 ^ 71 + zeta77 ^ 76 := by
    simp [periodEta77, conductor77PeriodPolynomial]
  rw [hη]
  simp only [map_add, map_pow, conductor77PeriodAutomorphism_zeta, hp]
  fin_cases m <;>
    norm_num [periodOrbit77, conductor77PeriodOrbitValue, conductor77PeriodOrbitPolynomials] <;>
    ring

theorem periodOrbit77_mem_periodField (m : Fin 6) : periodOrbit77 m ∈ conductor77PeriodField := by
  let η : conductor77PeriodField :=
    ⟨periodEta77, IntermediateField.mem_adjoin_simple_self ℚ periodEta77⟩
  let η' := (conductor77PeriodAutomorphism m).restrictNormal conductor77PeriodField η
  have he : (η' : Conductor77Cyclotomic) = periodOrbit77 m := by
    change algebraMap conductor77PeriodField Conductor77Cyclotomic η' = _
    rw [AlgEquiv.restrictNormal_commutes]
    exact conductor77PeriodAutomorphism_periodEta m
  rw [← he]
  exact η'.property

theorem periodQuadraticGenerator77_mem_periodField :
    periodQuadraticGenerator77 ∈ conductor77PeriodField := by
  unfold periodQuadraticGenerator77
  exact conductor77PeriodField.sub_mem
    (conductor77PeriodField.mul_mem (conductor77PeriodField.natCast_mem 2)
      (conductor77PeriodField.add_mem
        (conductor77PeriodField.add_mem (periodOrbit77_mem_periodField 0)
          (periodOrbit77_mem_periodField 2)) (periodOrbit77_mem_periodField 4)))
    conductor77PeriodField.one_mem

theorem periodCubicGenerator77_mem_periodField :
    periodCubicGenerator77 ∈ conductor77PeriodField :=
  conductor77PeriodField.add_mem (periodOrbit77_mem_periodField 0) (periodOrbit77_mem_periodField 3)

/-- The explicit candidate quadratic field inside the conductor-77 extension. -/
def conductor77QuadraticSubfield : IntermediateField ℚ Conductor77Cyclotomic :=
  ℚ⟮periodQuadraticGenerator77⟯

/-- The explicit candidate cubic field inside the conductor-77 extension. -/
def conductor77CubicSubfield : IntermediateField ℚ Conductor77Cyclotomic :=
  ℚ⟮periodCubicGenerator77⟯

theorem conductor77QuadraticSubfield_le_periodField :
    conductor77QuadraticSubfield ≤ conductor77PeriodField :=
  IntermediateField.adjoin_simple_le_iff.mpr periodQuadraticGenerator77_mem_periodField

theorem conductor77CubicSubfield_le_periodField :
    conductor77CubicSubfield ≤ conductor77PeriodField :=
  IntermediateField.adjoin_simple_le_iff.mpr periodCubicGenerator77_mem_periodField

end
end Biunimodular.F11
