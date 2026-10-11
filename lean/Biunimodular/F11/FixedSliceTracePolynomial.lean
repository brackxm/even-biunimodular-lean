/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceQuotientPolynomial

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# The degree-32 affine trace polynomial for the F11 fixed slice

After normalizing a fixed-slice vector by `h 0 = 1`, put

`t = (even11Fourier h) 0 = 1 + 2 * (h 1 + ... + h 5)`.

Eliminating the other five affine coordinates gives the polynomial below.
The reciprocal involution `t ↦ 11 / t` is the normalized Fourier action,
while the quotient coordinate is

`u = (11 + t²)² / (44 t²)`.

The exact factorization proved here is the purely univariate part of the
fixed-slice quotient calculation.  It reduces the P16 root obligation to the
single geometric assertion that every concrete affine trace is a root of
`fixedSliceTraceP32`.
-/

/-- The exact degree-32 polynomial of the unnormalised affine trace. -/
def fixedSliceTraceP32 : ℤ[X] :=
  529 * X^32
  - 14168 * X^31
  - 75725408 * X^30
  + 1255667336 * X^29
  + 481294566808 * X^28
  - 16225375729816 * X^27
  - 38002290126240 * X^26
  + 5484332590545864 * X^25
  + 52949083028517852 * X^24
  - 531352022854218808 * X^23
  + 5066000323498505248 * X^22
  - 34362949415247660504 * X^21
  + 177284232507719372200 * X^20
  - 865289626214374411512 * X^19
  + 3603501569180218724832 * X^18
  - 13532845755707680453656 * X^17
  + 48295539216411563873126 * X^16
  - 148861303312784484990216 * X^15
  + 436023689870806465704672 * X^14
  - 1151700492491332341722472 * X^13
  + 2595618448145519328380200 * X^12
  - 5534187366275050971829704 * X^11
  + 8974728599097335455652128 * X^10
  - 10354547730556069982912168 * X^9
  + 11350106187969177843243612 * X^8
  + 12931769368553668448400024 * X^7
  - 985681534814676771630240 * X^6
  - 4629289055764976323637576 * X^5
  + 1510508526031868326476568 * X^4
  + 43349041989264687337816 * X^3
  - 28756711086023026687328 * X^2
  - 59183252064280943368 * X
  + 24307407097829673169

/-- The trace polynomial over the rationals, used to form its intrinsic
complex root space. -/
def fixedSliceTraceP32Q : ℚ[X] :=
  fixedSliceTraceP32.map (Int.castRingHom ℚ)

theorem fixedSliceTraceP32Q_map_complex :
    fixedSliceTraceP32Q.map (algebraMap ℚ ℂ) =
      fixedSliceTraceP32.map (Int.castRingHom ℂ) := by
  rw [fixedSliceTraceP32Q, Polynomial.map_map]
  congr 1

theorem fixedSliceTraceP32Q_ne_zero : fixedSliceTraceP32Q ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : ℚ[X] ↦ p.coeff 0) hzero
  norm_num [fixedSliceTraceP32Q, fixedSliceTraceP32] at hcoeff

theorem fixedSliceTraceP32Q_natDegree :
    fixedSliceTraceP32Q.natDegree = 32 := by
  rw [fixedSliceTraceP32Q,
    Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))]
  norm_num [fixedSliceTraceP32]
  compute_degree <;> norm_num

/-- The intrinsic complex root space of the degree-32 trace eliminant. -/
abbrev FixedSliceTraceRoot := fixedSliceTraceP32Q.rootSet ℂ

/-- Without needing squarefreeness, the distinct trace-root space has at most
the degree of the eliminant. -/
theorem fixedSliceTraceRoot_card_le :
    Fintype.card FixedSliceTraceRoot ≤ 32 := by
  classical
  change Fintype.card (fixedSliceTraceP32Q.rootSet ℂ) ≤ 32
  have hcard :
      Fintype.card (fixedSliceTraceP32Q.rootSet ℂ) =
        (fixedSliceTraceP32Q.aroots ℂ).toFinset.card := by
    simp_rw [Polynomial.rootSet_def, Finset.coe_sort_coe,
      Fintype.card_coe]
  rw [hcard]
  calc
    (fixedSliceTraceP32Q.aroots ℂ).toFinset.card ≤
        (fixedSliceTraceP32Q.aroots ℂ).card :=
      Multiset.toFinset_card_le _
    _ = fixedSliceTraceP32Q.natDegree := by
      rw [← (IsAlgClosed.splits
        (fixedSliceTraceP32Q.map (algebraMap ℚ ℂ))).natDegree_eq_card_roots,
        Polynomial.natDegree_map]
    _ = 32 := fixedSliceTraceP32Q_natDegree

/-- The numerator of `u` before dividing by `44 t²`. -/
def fixedSliceTraceUNum : ℤ[X] := (11 + X ^ 2) ^ 2

/-- The denominator of `u`. -/
def fixedSliceTraceUDen : ℤ[X] := 44 * X ^ 2

/-- P16 evaluated at the rational trace expression, with its denominator
cleared to degree sixteen. -/
def fixedSliceTraceP16Cleared : ℤ[X] :=
  let n := fixedSliceTraceUNum
  let d := fixedSliceTraceUDen
  279841 * n^16
  - 1827652680 * n^15 * d
  + 3257049783088 * n^14 * d^2
  - 902834250825536 * n^13 * d^3
  + 80058287930181376 * n^12 * d^4
  - 2412533038010350592 * n^11 * d^5
  + 43751724749749010432 * n^10 * d^6
  - 331763738335657476096 * n^9 * d^7
  + 1548092135954010603520 * n^8 * d^8
  - 2774179840098089828352 * n^7 * d^9
  + 2176046167971809198080 * n^6 * d^10
  - 768292372028118269952 * n^5 * d^11
  + 117488117139862716416 * n^4 * d^12
  - 7393390199918559232 * n^3 * d^13
  + 163497433005817856 * n^2 * d^14
  - 966105648594944 * n * d^15

/-- The P16 numerator pulled back along the trace coordinate factors as the
two sign-conjugate trace polynomials. -/
theorem fixedSliceTraceP16Cleared_factor :
    fixedSliceTraceP16Cleared =
      fixedSliceTraceP32 * fixedSliceTraceP32.comp (-X) := by
  norm_num [fixedSliceTraceP16Cleared, fixedSliceTraceUNum,
    fixedSliceTraceUDen, fixedSliceTraceP32]
  ring

/-- Evaluation of the cleared trace expression is the expected denominator
power times P16 evaluated at `u(t)`. -/
theorem fixedSliceTraceP16Cleared_eval (t : ℂ) (ht : t ≠ 0) :
    (fixedSliceTraceP16Cleared.map (Int.castRingHom ℂ)).eval t =
      (44 * t ^ 2) ^ 16 *
        (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).eval
          ((11 + t ^ 2) ^ 2 / (44 * t ^ 2)) := by
  simp [fixedSliceTraceP16Cleared, fixedSliceTraceUNum,
    fixedSliceTraceUDen, fixedSliceQuotientP16Q,
    fixedSliceQuotientP16]
  field_simp [ht]

/-- A trace root is nonzero; the constant coefficient of P32 is nonzero. -/
theorem fixedSliceTraceP32_root_ne_zero {t : ℂ}
    (ht : (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot t) :
    t ≠ 0 := by
  intro htzero
  rw [htzero, Polynomial.IsRoot] at ht
  norm_num [fixedSliceTraceP32] at ht

/-- The degree-32 trace eliminant is reciprocal under the Fourier action
`t ↦ 11 / t`. -/
theorem fixedSliceTraceP32_eval_reciprocal (t : ℂ) (ht : t ≠ 0) :
    t ^ 32 *
        (fixedSliceTraceP32.map (Int.castRingHom ℂ)).eval (11 / t) =
      11 ^ 16 *
        (fixedSliceTraceP32.map (Int.castRingHom ℂ)).eval t := by
  norm_num [fixedSliceTraceP32]
  field_simp [ht]
  ring

/-- Hence reciprocal Fourier partners of trace roots are trace roots. -/
theorem fixedSliceTraceP32_isRoot_reciprocal {t : ℂ}
    (ht : (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot t) :
    (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot (11 / t) := by
  have ht0 := fixedSliceTraceP32_root_ne_zero ht
  have hrec := fixedSliceTraceP32_eval_reciprocal t ht0
  rw [Polynomial.IsRoot] at ht ⊢
  rw [ht, mul_zero] at hrec
  exact (mul_eq_zero.mp hrec).resolve_left (pow_ne_zero 32 ht0)

/-- The exact univariate reduction: every P32 trace root gives a P16
quotient root under `u = (11 + t²)² / (44 t²)`. -/
theorem fixedSliceQuotientP16_isRoot_of_trace_isRoot {t : ℂ}
    (ht : (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot t) :
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
      ((11 + t ^ 2) ^ 2 / (44 * t ^ 2)) := by
  have ht0 := fixedSliceTraceP32_root_ne_zero ht
  have hclear :
      (fixedSliceTraceP16Cleared.map (Int.castRingHom ℂ)).eval t = 0 := by
    rw [fixedSliceTraceP16Cleared_factor, Polynomial.map_mul,
      Polynomial.eval_mul]
    rw [Polynomial.IsRoot] at ht
    simp [ht]
  rw [fixedSliceTraceP16Cleared_eval t ht0] at hclear
  exact (mul_eq_zero.mp hclear).resolve_left
    (pow_ne_zero 16 (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht0)))

/-- Every complex root of P16 is attained by the rational trace expression
on at least one root of the degree-32 trace polynomial. -/
theorem fixedSliceTraceU_surjective
    (u : ℂ)
    (hu : (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot u) :
    ∃ t : ℂ,
      (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot t ∧
        (11 + t ^ 2) ^ 2 / (44 * t ^ 2) = u := by
  let q : ℂ[X] := X ^ 2 + C (22 - 44 * u) * X + C 121
  have hqdeg : q.degree ≠ 0 := by
    let low : ℂ[X] := C (22 - 44 * u) * X + C 121
    have hlow : low.degree < 2 := by
      simp only [low]
      compute_degree; norm_num
    have hqdegree : q.degree = 2 := by
      rw [show q = X ^ 2 + low by simp [q, low]; ring,
        degree_add_eq_left_of_degree_lt]
      · simp
      · simpa using hlow
    rw [hqdegree]
    norm_num
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_root q hqdeg
  have hvEq : v ^ 2 + (22 - 44 * u) * v + 121 = 0 := by
    simpa [q, Polynomial.IsRoot] using hv
  have hv0 : v ≠ 0 := by
    intro hvzero
    rw [hvzero] at hvEq
    norm_num at hvEq
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq v
    (by norm_num : 0 < 2)
  have ht0 : t ≠ 0 := by
    intro htzero
    apply hv0
    rw [← ht, htzero]
    norm_num
  have huTrace : (11 + t ^ 2) ^ 2 / (44 * t ^ 2) = u := by
    rw [ht]
    field_simp [hv0]
    linear_combination hvEq
  have hclear :
      (fixedSliceTraceP16Cleared.map (Int.castRingHom ℂ)).eval t = 0 := by
    rw [fixedSliceTraceP16Cleared_eval t ht0, huTrace]
    rw [Polynomial.IsRoot] at hu
    simp [hu]
  rw [fixedSliceTraceP16Cleared_factor, Polynomial.map_mul,
    Polynomial.eval_mul] at hclear
  have hprod :
      (fixedSliceTraceP32.map (Int.castRingHom ℂ)).eval t *
        (fixedSliceTraceP32.map (Int.castRingHom ℂ)).eval (-t) = 0 := by
    have hcomp :
        (fixedSliceTraceP32.comp (-X)).map (Int.castRingHom ℂ) =
          (fixedSliceTraceP32.map (Int.castRingHom ℂ)).comp (-X) := by
      rw [Polynomial.map_comp]
      simp
    rw [hcomp, Polynomial.eval_comp] at hclear
    simpa using hclear
  rcases mul_eq_zero.mp hprod with htRoot | hnegRoot
  · exact ⟨t, htRoot, huTrace⟩
  · refine ⟨-t, hnegRoot, ?_⟩
    convert huTrace using 1
    all_goals ring

end

end Biunimodular.F11
