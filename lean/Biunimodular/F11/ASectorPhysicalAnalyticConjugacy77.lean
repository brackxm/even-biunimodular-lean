/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorAnalyticEmbedding77
import Biunimodular.F11.ASectorPhysicalOrbitCoordinate11

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

/-- Any real embedding of the maximal-real conductor-77 field sends its
explicit generator to one of the analytic cyclotomic coordinates.
The exponent is located in an explicit row by subsequent lemmas. -/
theorem conductor77_realEmbedding_generator_is_analyticCoordinate
    (φ : Conductor77MaxReal →ₐ[ℚ] ℝ) :
    ∃ i : ℕ, i < 77 ∧ i.Coprime 77 ∧
      φ aSectorX77Real = analyticASectorCoordinate (3 * i) := by
  let ιC : Conductor77MaxReal →+* ℂ :=
    (IsScalarTower.toAlgHom ℚ ℝ ℂ).toRingHom.comp φ.toRingHom
  let : Algebra Conductor77MaxReal ℂ := ιC.toAlgebra
  let ψ : Conductor77Cyclotomic →ₐ[Conductor77MaxReal] ℂ :=
    IsAlgClosed.lift
  have hζ : (ψ zeta77) ^ 77 = 1 := by
    have h : zeta77 ^ 77 = 1 := (IsCyclotomicExtension.zeta_spec 77 ℚ
      Conductor77Cyclotomic).pow_eq_one
    simpa only [map_pow, map_one] using congrArg ψ h
  obtain ⟨i, hi, hpow⟩ :=
    analyticZeta77_primitive.eq_pow_of_pow_eq_one hζ
  have hψprimitive : IsPrimitiveRoot (ψ zeta77) 77 :=
    (IsCyclotomicExtension.zeta_spec 77 ℚ
      Conductor77Cyclotomic).map_of_injective ψ.injective
  have hicoprime : i.Coprime 77 :=
    (analyticZeta77_primitive.pow_iff_coprime (by norm_num) i).mp
      (hpow.symm ▸ hψprimitive)
  have hζ77 : analyticZeta77 ^ 77 = 1 :=
    analyticZeta77_primitive.pow_eq_one
  have hexp : analyticZeta77 ^ (26 * (3 * i)) =
      analyticZeta77 ^ i := by
    calc
      analyticZeta77 ^ (26 * (3 * i)) =
          analyticZeta77 ^ (77 * i + i) := by congr 1; omega
      _ = (analyticZeta77 ^ 77) ^ i * analyticZeta77 ^ i := by
        rw [pow_add, pow_mul]
      _ = analyticZeta77 ^ i := by rw [hζ77]; simp
  have hcoord : ψ aSectorX77 = aSectorX77Pair (ψ zeta77) := by
    simp [aSectorX77, aSectorX77Pair, map_sum, map_add,
      map_mul, map_pow, map_intCast, map_ofNat, map_neg]
  have hbase : ψ aSectorX77 =
      ((φ aSectorX77Real : ℝ) : ℂ) := by
    have h := ψ.commutes aSectorX77Real
    have hval : (algebraMap Conductor77MaxReal Conductor77Cyclotomic)
        aSectorX77Real = aSectorX77 := rfl
    have hcomp : (algebraMap Conductor77MaxReal ℂ)
        aSectorX77Real = ((φ aSectorX77Real : ℝ) : ℂ) := rfl
    rw [hval, hcomp] at h
    exact h
  have hanalytic : (analyticASectorCoordinate (3 * i) : ℂ) =
      aSectorX77Pair (analyticZeta77 ^ (26 * (3 * i))) := by
    rw [analyticASectorCoordinate_complex,
      conductor77AnalyticEmbedding_coordinate]
  refine ⟨i, hi, hicoprime, ?_⟩
  apply Complex.ofReal_injective
  calc
    ((φ aSectorX77Real : ℝ) : ℂ) = ψ aSectorX77 := hbase.symm
    _ = aSectorX77Pair (ψ zeta77) := hcoord
    _ = aSectorX77Pair (analyticZeta77 ^ i) := by rw [hpow]
    _ = (analyticASectorCoordinate (3 * i) : ℂ) := by
      rw [hanalytic, hexp]

/-- Every physical A-sector squared imaginary coordinate is one of the
explicit analytic conductor-77 coordinates. -/
theorem everyASectorPhase_coordinate_is_analyticCoordinate
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∀ y ∈ [s.1.b, s.1.d, s.1.f, s.1.h, s.1.k],
      ∃ i : ℕ, i < 77 ∧ i.Coprime 77 ∧
        4 * y ^ 2 = analyticASectorCoordinate (3 * i) := by
  intro y hy
  let hmin := everyASectorPhase_all_G30_minpoly11 s hA y hy
  let φ := aSectorCoordinateEmbedding11 y hmin
  obtain ⟨i, hi, hcoprime, hφ⟩ :=
    conductor77_realEmbedding_generator_is_analyticCoordinate φ
  exact ⟨i, hi, hcoprime,
    (aSectorCoordinateEmbedding11_generator y hmin).symm.trans hφ⟩

/-- One representative of each primitive conductor-77 exponent modulo sign. -/
def aSectorCanonicalAnalyticExponents77 : List ℕ :=
  (List.range 77).filter (fun e => e.Coprime 77 ∧ e ≤ 38)

theorem aSectorCanonicalAnalyticExponents77_card :
    aSectorCanonicalAnalyticExponents77.Nodup ∧
      aSectorCanonicalAnalyticExponents77.length = 30 := by
  native_decide

theorem aSectorCanonicalAnalyticExponents77_coprime :
    ∀ e ∈ aSectorCanonicalAnalyticExponents77,
      (26 * e).Coprime 77 := by
  native_decide

/-- Every member of the canonical thirty-coordinate list has the same
irreducible degree-thirty polynomial as the physical A coordinates. -/
theorem aSectorCanonicalAnalyticExponents77_minpoly :
    ∀ e ∈ aSectorCanonicalAnalyticExponents77,
      minpoly ℚ (analyticASectorCoordinate e) =
        aSectorG30.map (Int.castRingHom ℚ) := by
  intro e he
  exact analyticASectorCoordinate_minpoly e
    (aSectorCanonicalAnalyticExponents77_coprime e he)

private theorem aSectorCanonicalAnalyticExponent_certificate :
    ∀ i : Fin 77, i.val.Coprime 77 →
      let e := canonicalSignedExponent77 (3 * i.val)
      e ∈ aSectorCanonicalAnalyticExponents77 ∧
        ((26 * (3 * i.val)) % 77 = (26 * e) % 77 ∨
          (26 * (3 * i.val)) % 77 + (26 * e) % 77 = 77) := by
  native_decide

/-- Every physical A-sector squared coordinate equals one of thirty
explicit real analytic cyclotomic coordinates. -/
theorem everyASectorPhase_coordinate_in_analyticThirty
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∀ y ∈ [s.1.b, s.1.d, s.1.f, s.1.h, s.1.k],
      ∃ e ∈ aSectorCanonicalAnalyticExponents77,
        4 * y ^ 2 = analyticASectorCoordinate e := by
  intro y hy
  obtain ⟨i, hi, hcoprime, hvalue⟩ :=
    everyASectorPhase_coordinate_is_analyticCoordinate s hA y hy
  let e := canonicalSignedExponent77 (3 * i)
  have hcert := aSectorCanonicalAnalyticExponent_certificate
    ⟨i, hi⟩ hcoprime
  change e ∈ aSectorCanonicalAnalyticExponents77 ∧
    ((26 * (3 * i)) % 77 = (26 * e) % 77 ∨
      (26 * (3 * i)) % 77 + (26 * e) % 77 = 77) at hcert
  have hfield := aSectorX77AtExponent_eq_of_signed_mod hcert.2
  have hcomplex := congrArg conductor77AnalyticEmbedding hfield
  have hanalytic : analyticASectorCoordinate (3 * i) =
      analyticASectorCoordinate e := by
    apply Complex.ofReal_injective
    simpa only [analyticASectorCoordinate_complex] using hcomplex
  exact ⟨e, hcert.1, hvalue.trans hanalytic⟩

end

end Biunimodular.F11
