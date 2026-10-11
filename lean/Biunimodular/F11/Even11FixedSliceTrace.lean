/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceQuotientGeometry
import Biunimodular.F11.FixedSliceTracePolynomial

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

/-!
# The affine trace coordinate on the concrete F11 fixed slice

This file connects the exact degree-32 trace polynomial to the projective
fixed-slice model.  The multivariate elimination is expressed as a
pointwise trace-root certificate; the conversion from that certificate to the
P16 quotient-root statement is proved here.
-/

/-- The projectively invariant ratio `(even11Fourier h) 0 / h 0`. -/
def even11ProjectiveTrace : Even11ProjectiveSpace → ℂ :=
  Projectivization.lift
    (fun h : {h : Even6 ℂ // h ≠ 0} ↦ even11Fourier h.1 0 / h.1 0)
    (by
      intro a b c hab
      have hc : c ≠ 0 := by
        intro hc
        apply a.2
        rw [hab, hc, zero_smul]
      rw [hab]
      simp only [LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_div_mul_left _ _ hc)

@[simp] theorem even11ProjectiveTrace_mk
    (h : Even6 ℂ) (hnz : h ≠ 0) :
    even11ProjectiveTrace (Projectivization.mk ℂ h hnz) =
      even11Fourier h 0 / h 0 := by
  rfl

/-- The affine trace restricted to the concrete fixed slice. -/
def even11FixedSliceTrace (p : Even11FixedSlicePoint) : ℂ :=
  even11ProjectiveTrace p.1

/-- The affine trace never vanishes on the fixed slice. -/
theorem even11FixedSliceTrace_ne_zero (p : Even11FixedSlicePoint) :
    even11FixedSliceTrace p ≠ 0 := by
  rcases p with ⟨p, hp⟩
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveFixedSlice_mk] at hp
      change even11Fourier h 0 / h 0 ≠ 0
      have hpUn : FixedSliceEq even11Fourier h :=
        (even11_fixedSliceEq_normalized_iff h).mp hp
      have hcommon :=
        even11_fixedSlice_common_ne_zero_certified hnz hpUn
      have hp : h 0 * even11Fourier h 0 ≠ 0 := by
        simpa [fourierCoordProduct] using hcommon
      exact div_ne_zero (mul_ne_zero_iff.mp hp).2
        (mul_ne_zero_iff.mp hp).1

/-- The normalized Fourier involution sends the affine trace coordinate to
its reciprocal partner `11 / t`. -/
@[simp] theorem even11FixedSliceTrace_fourier
    (p : Even11FixedSlicePoint) :
    even11FixedSliceTrace (even11FixedSliceFourier p) =
      11 / even11FixedSliceTrace p := by
  rcases p with ⟨p, hp⟩
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveFixedSlice_mk] at hp
      change
        even11Fourier (even11FourierNormalized h) 0 /
            even11FourierNormalized h 0 =
          11 / (even11Fourier h 0 / h 0)
      have hpUn : FixedSliceEq even11Fourier h :=
        (even11_fixedSliceEq_normalized_iff h).mp hp
      have hcommon :=
        even11_fixedSlice_common_ne_zero_certified hnz hpUn
      have hprod : h 0 * even11Fourier h 0 ≠ 0 := by
        simpa [fourierCoordProduct] using hcommon
      have hh0 : h 0 ≠ 0 := (mul_ne_zero_iff.mp hprod).1
      have hF0 : even11Fourier h 0 ≠ 0 :=
        (mul_ne_zero_iff.mp hprod).2
      have hsR : Real.sqrt 11 ≠ 0 :=
        (Real.sqrt_pos.2 (by norm_num)).ne'
      have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by exact_mod_cast hsR
      simp only [even11FourierNormalized, LinearMap.smul_apply,
        Pi.smul_apply, smul_eq_mul, LinearMap.map_smul]
      rw [even11Fourier_sq]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp

/-- The projective quotient coordinate is the rational trace expression
`u = (11 + t²)² / (44 t²)`. -/
theorem even11FixedSliceU_eq_trace (p : Even11FixedSlicePoint) :
    even11FixedSliceU p =
      (11 + even11FixedSliceTrace p ^ 2) ^ 2 /
        (44 * even11FixedSliceTrace p ^ 2) := by
  rcases p with ⟨p, hp⟩
  induction p using Projectivization.ind with
  | h h hnz =>
      rw [even11ProjectiveFixedSlice_mk] at hp
      change fixedSliceUValue even11FourierNormalized h =
        (11 + (even11Fourier h 0 / h 0) ^ 2) ^ 2 /
          (44 * (even11Fourier h 0 / h 0) ^ 2)
      have hpUn : FixedSliceEq even11Fourier h :=
        (even11_fixedSliceEq_normalized_iff h).mp hp
      have hcommon :=
        even11_fixedSlice_common_ne_zero_certified hnz hpUn
      have hp : h 0 * even11Fourier h 0 ≠ 0 := by
        simpa [fourierCoordProduct] using hcommon
      have hh0 : h 0 ≠ 0 := (mul_ne_zero_iff.mp hp).1
      have hF0 : even11Fourier h 0 ≠ 0 := (mul_ne_zero_iff.mp hp).2
      have hsR : Real.sqrt 11 ≠ 0 :=
        (Real.sqrt_pos.2 (by norm_num)).ne'
      have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by exact_mod_cast hsR
      have hs2 : (Real.sqrt 11 : ℂ) ^ 2 = 11 := by
        exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11)
      simp only [fixedSliceUValue, fixedSliceQNum, fixedSliceQDen,
        even11FourierNormalized, LinearMap.smul_apply, Pi.smul_apply,
        smul_eq_mul]
      field_simp [hh0, hF0, hs]
      have hs4 : (Real.sqrt 11 : ℂ) ^ 4 = 121 := by
        calc
          (Real.sqrt 11 : ℂ) ^ 4 =
              ((Real.sqrt 11 : ℂ) ^ 2) ^ 2 := by ring
          _ = 121 := by rw [hs2]; norm_num
      ring_nf
      rw [hs2, hs4]
      ring

/-- The trace-root property used by the first field of
`Even11FixedSliceGeometryCertificate`: every concrete trace satisfies the
degree-32 eliminant. -/
structure Even11FixedSliceTraceRootCertificate where
  trace_isRoot : ∀ p : Even11FixedSlicePoint,
    (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot
      (even11FixedSliceTrace p)

/-- The concrete trace map into the roots of the degree-32 eliminant. -/
def even11FixedSliceTraceRootMap
    (hroot : ∀ p : Even11FixedSlicePoint,
      (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot
        (even11FixedSliceTrace p)) :
    Even11FixedSlicePoint → FixedSliceTraceRoot :=
  fun p ↦ ⟨even11FixedSliceTrace p, by
    rw [Polynomial.mem_rootSet]
    refine ⟨fixedSliceTraceP32Q_ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      fixedSliceTraceP32Q_map_complex]
    exact hroot p⟩

@[simp] theorem even11FixedSliceTraceRootMap_value
    (hroot : ∀ p : Even11FixedSlicePoint,
      (fixedSliceTraceP32.map (Int.castRingHom ℂ)).IsRoot
        (even11FixedSliceTrace p))
    (p : Even11FixedSlicePoint) :
    (even11FixedSliceTraceRootMap hroot p : ℂ) =
      even11FixedSliceTrace p := by
  rfl

/-- Exact shape-certificate interface for the affine elimination.  Unlike the
older quotient-level certificate, this asks only for the natural statement
verified by a lexicographic Gröbner basis: trace is a bijection from the
concrete fixed slice to the distinct roots of its degree-32 eliminant. -/
structure Even11FixedSliceTraceGeometryCertificate extends
    Even11FixedSliceTraceRootCertificate where
  trace_bijective : Function.Bijective
    (even11FixedSliceTraceRootMap trace_isRoot)

/-- The constructive half of the trace shape calculation.  For the intrinsic
cardinality argument it is enough to reconstruct one concrete fixed-slice
point above every root of `P32`; injectivity and polynomial necessity then
follow from the independent projective `≤ 32` bound and cardinal exhaustion. -/
structure Even11FixedSliceTraceSurjectivityCertificate where
  trace_surjective : ∀ t : FixedSliceTraceRoot,
    ∃ p : Even11FixedSlicePoint, even11FixedSliceTrace p = (t : ℂ)

/-- The trace eliminant implies the P16 root statement for every concrete
fixed-slice quotient point. -/
theorem Even11FixedSliceTraceRootCertificate.quotient_u_isRoot
    (C : Even11FixedSliceTraceRootCertificate)
    (y : Even11FixedSliceFourierQuotient) :
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
      (even11FixedSliceQuotientU y) := by
  refine Quotient.inductionOn' y ?_
  intro p
  rw [even11FixedSliceQuotientU_mk, even11FixedSliceU_eq_trace]
  exact fixedSliceQuotientP16_isRoot_of_trace_isRoot
    (C.trace_isRoot p)

/-- The exact trace-shape statement implies that the concrete quotient
invariant reaches every P16 root. -/
theorem Even11FixedSliceTraceGeometryCertificate.quotient_u_surjective
    (C : Even11FixedSliceTraceGeometryCertificate) :
    Function.Surjective
      (even11FixedSliceQuotientRootMap
        C.toEven11FixedSliceTraceRootCertificate.quotient_u_isRoot) := by
  intro r
  have hu :
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot (r : ℂ) := by
    rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map,
      ← Polynomial.aeval_def]
    exact (Polynomial.mem_rootSet.mp r.2).2
  obtain ⟨t, ht, htu⟩ := fixedSliceTraceU_surjective (r : ℂ) hu
  let tr : FixedSliceTraceRoot := ⟨t, by
    rw [Polynomial.mem_rootSet]
    refine ⟨fixedSliceTraceP32Q_ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      fixedSliceTraceP32Q_map_complex]
    exact ht⟩
  obtain ⟨p, hp⟩ := C.trace_bijective.2 tr
  have hpTrace : even11FixedSliceTrace p = t := by
    exact congrArg Subtype.val hp
  refine ⟨Quotient.mk'' p, ?_⟩
  apply Subtype.ext
  change even11FixedSliceQuotientU (Quotient.mk'' p) = (r : ℂ)
  rw [even11FixedSliceQuotientU_mk, even11FixedSliceU_eq_trace,
    hpTrace, htu]

/-- A trace-shape certificate constructs the requested concrete geometry
certificate.  Surjectivity is the univariate trace calculation above;
injectivity follows from the degree-32 bound and the already-proved free
two-sheet Fourier action. -/
theorem Even11FixedSliceTraceGeometryCertificate.toGeometryCertificate
    (C : Even11FixedSliceTraceGeometryCertificate) :
    Even11FixedSliceGeometryCertificate := by
  let traceEquiv : Even11FixedSlicePoint ≃ FixedSliceTraceRoot :=
    Equiv.ofBijective
      (even11FixedSliceTraceRootMap C.trace_isRoot) C.trace_bijective
  let : Finite Even11FixedSlicePoint :=
    Finite.of_equiv FixedSliceTraceRoot traceEquiv.symm
  let : Finite Even11FixedSliceFourierQuotient :=
    Finite.of_surjective Quotient.mk'' Quotient.mk''_surjective
  let hroot := C.toEven11FixedSliceTraceRootCertificate.quotient_u_isRoot
  have hsurj : Function.Surjective
      (even11FixedSliceQuotientRootMap hroot) :=
    C.quotient_u_surjective
  have hfixedLe : Nat.card Even11FixedSlicePoint ≤ 32 := by
    rw [Nat.card_congr traceEquiv]
    simpa only [Nat.card_eq_fintype_card] using fixedSliceTraceRoot_card_le
  have htwo : Nat.card Even11FixedSlicePoint =
      Nat.card Even11FixedSliceFourierQuotient * 2 := by
    calc
      Nat.card Even11FixedSlicePoint =
          Nat.card (Even11FixedSliceFourierQuotient × Bool) :=
        Nat.card_congr even11FixedSliceTwoSheeted
      _ = Nat.card Even11FixedSliceFourierQuotient * Nat.card Bool := by
        rw [Nat.card_prod]
      _ = Nat.card Even11FixedSliceFourierQuotient * 2 := by
        norm_num [Nat.card_eq_fintype_card]
  have hquotLe : Nat.card Even11FixedSliceFourierQuotient ≤ 16 := by
    omega
  have htarget : Nat.card FixedSliceQuotientRoot = 16 := by
    simpa only [Nat.card_eq_fintype_card] using
      fixedSliceQuotientRoot_card
  refine
    { quotient_u_isRoot := hroot
      quotient_u_bijective := ?_ }
  apply hsurj.bijective_of_nat_card_le
  calc
    Nat.card Even11FixedSliceFourierQuotient ≤ 16 := hquotLe
    _ = Nat.card FixedSliceQuotientRoot := htarget.symm

end

end Biunimodular.F11
