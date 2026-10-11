/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252TorusCertificateData11
import Biunimodular.F11.P150RootIsolation11

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Kernel-replayed H252 phase elimination

This module combines the semantic phase-to-torus reduction with the generated
integral ideal-membership certificate.  The circle lift is then transported
back from the unit phase coordinate to the real final coordinate `k`.
-/

private theorem h252KQ_eval_complex_eq_real11 (k : ℝ) :
    (h252KQ11.map (algebraMap ℚ ℂ)).eval (k : ℂ) =
      ((h252KR11.eval k : ℝ) : ℂ) := by
  have h := Polynomial.hom_eval₂ h252KQ11 (algebraMap ℚ ℝ)
    Complex.ofRealHom k
  have hhom : Complex.ofRealHom.comp (algebraMap ℚ ℝ) =
      algebraMap ℚ ℂ := by
    ext q
    simp
  rw [hhom] at h
  rw [h252KR11, Polynomial.eval_map, Polynomial.eval_map]
  exact h.symm

/-- Exact elimination of every physical phase solution to the
degree-252 real coordinate polynomial. -/
theorem h252PhaseEliminationCertificate11 :
    H252PhaseEliminationCertificate11 where
  phase_k_isRoot x hx := by
    let z1 := phaseC x.a x.b
    let z2 := phaseC x.c x.d
    let z3 := phaseC x.e x.f
    let z4 := phaseC x.g x.h
    let z5 := phaseC x.j x.k
    obtain ⟨w, h1, h2, h3, h4, h5, h6, hcoord⟩ :=
      phaseSolution_h252Torus11 x hx
    change h252TorusF1 z1 z2 z3 z4 z5 = 0 at h1
    change h252TorusF2 z1 z2 z3 z4 z5 = 0 at h2
    change h252TorusF3 z1 z2 z3 z4 z5 = 0 at h3
    change h252TorusF4 z1 z2 z3 z4 z5 = 0 at h4
    change h252TorusF5 z1 z2 z3 z4 z5 = 0 at h5
    change h252TorusS z1 z2 z3 z4 w z5 = 0 at h6
    change (z5 - w*z1*z2*z3*z4) / 2 = Complex.I * x.k at hcoord
    have hEliminant : h252TorusEliminantEval11 z5 = 0 :=
      h252TorusEliminant_zero11 z1 z2 z3 z4 w z5
        h1 h2 h3 h4 h5 h6
    have hCircle : h252CircleLiftEval11 z5 = 0 := by
      have hfactor := h252TorusEliminant_circleFactor11 z5
      rw [hEliminant, zero_mul] at hfactor
      exact (mul_eq_zero.mp hfactor.symm).resolve_left (by norm_num)
    have hunit : (w*z1*z2*z3*z4)*z5 = 1 := by
      have hs : w * h252TorusD z1 z2 z3 z4 z5 = 1 :=
        sub_eq_zero.mp (by simpa [h252TorusS] using h6)
      calc
        (w*z1*z2*z3*z4)*z5 =
            w * h252TorusD z1 z2 z3 z4 z5 := by
              simp only [h252TorusD]
              ring
        _ = 1 := hs
    have hrel : z5^2 - 1 = 2*z5*(Complex.I * (x.k : ℂ)) := by
      calc
        z5^2 - 1 = z5^2 - (w*z1*z2*z3*z4)*z5 := by rw [hunit]
        _ = 2*z5*((z5 - w*z1*z2*z3*z4) / 2) := by ring
        _ = 2*z5*(Complex.I * (x.k : ℂ)) := by rw [hcoord]
    have hz5norm : Complex.normSq z5 = 1 := by
      simpa [z5, phaseC, Complex.normSq, pow_two] using hx.1.2.2.2.2
    have hz5 : z5 ≠ 0 := fun hz => by simp [hz] at hz5norm
    have hsub := h252CircleLift_substitution11 z5
      (Complex.I * (x.k : ℂ)) hrel
    rw [hCircle] at hsub
    have hpow : (2*z5)^252 ≠ (0 : ℂ) :=
      pow_ne_zero 252 (mul_ne_zero (by norm_num) hz5)
    have hxzero : h252InXEval11 (Complex.I * (x.k : ℂ)) = 0 :=
      (mul_eq_zero.mp hsub.symm).resolve_left hpow
    have hcoordzero : h252CoordinateEval11 (x.k : ℂ) = 0 := by
      rw [← h252InXEval_I11 x.k]
      exact hxzero
    have hcomplex :
        (h252KQ11.map (algebraMap ℚ ℂ)).eval (x.k : ℂ) = 0 := by
      rw [← h252CoordinateEval_eq11]
      exact hcoordzero
    have hrealcast : ((h252KR11.eval x.k : ℝ) : ℂ) = 0 := by
      rw [← h252KQ_eval_complex_eq_real11]
      exact hcomplex
    rw [Polynomial.IsRoot]
    exact_mod_cast hrealcast

/-- The exact H252 elimination and the P150 isolation layer together supply
the coordinate root cover consumed by the finite phase scanner. -/
theorem p150KRootCoverCertificate11 : P150KRootCoverCertificate11 :=
  p150KRootCoverCertificate11_of_elimination
    h252PhaseEliminationCertificate11

end

end Biunimodular.F11
