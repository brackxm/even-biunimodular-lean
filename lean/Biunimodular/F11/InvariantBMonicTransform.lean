/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.NormNum.Prime
import Biunimodular.F11.InvariantPolynomialData
import Biunimodular.F11.InvariantFiniteFieldIrreducibility

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Closing the nonmonic B irreducibility transfer

Instead of needing a general nonmonic mod-p criterion, we use the standard
integral monicization obtained by scaling roots by the leading coefficient.
Because `279841 ≡ 1 (mod 5)`, its mod-5 reduction is exactly the already
certified irreducible polynomial `invariantB5`.
-/

/-- Integral monicization of the degree-eight B polynomial:
`a^7 B(X/a)` with `a = 279841`. -/
def invariantBMonicTransform : ℤ[X] :=
  X^8
  - 9805544 * X^7
  + 58892063839664 * X^6
  - 120272121205747211264 * X^5
  + 153071793297510106861779200 * X^4
  - 51409551051176097959642954080256 * X^3
  + 5543976116829310562474467878465892352 * X^2
  - 180895171613156646033914441762742478274560 * X
  + 1065723909882049873321613711522686691849076736

theorem invariantBMonicTransform_monic : invariantBMonicTransform.Monic := by
  let low : ℤ[X] :=
    - 9805544 * X^7
    + 58892063839664 * X^6
    - 120272121205747211264 * X^5
    + 153071793297510106861779200 * X^4
    - 51409551051176097959642954080256 * X^3
    + 5543976116829310562474467878465892352 * X^2
    - 180895171613156646033914441762742478274560 * X
    + 1065723909882049873321613711522686691849076736
  have hform : invariantBMonicTransform = X^8 + low := by
    simp only [invariantBMonicTransform, low]
    ring
  have hlow : low.degree < 8 := by
    simp only [low]
    compute_degree; norm_num
  rw [hform]
  exact monic_X_pow_add hlow

theorem invariantBMonicTransform_mod5 :
    invariantBMonicTransform.map (Int.castRingHom (ZMod 5)) = invariantB5 := by
  norm_num [invariantBMonicTransform, invariantB5]
  all_goals reduce_mod_char
  all_goals ring_nf

theorem invariantBMonicTransform_irreducible_over_Z :
    Irreducible invariantBMonicTransform := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply invariantBMonicTransform_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 5))
  rw [invariantBMonicTransform_mod5]
  exact invariantB5_irreducible

theorem invariantBMonicTransform_irreducible_over_Q :
    Irreducible (invariantBMonicTransform.map (Int.castRingHom ℚ)) := by
  exact (invariantBMonicTransform_monic.irreducible_iff_irreducible_map_fraction_map).1
    invariantBMonicTransform_irreducible_over_Z

/-- Scaling roots by a nonzero field element preserves irreducibility. -/
theorem irreducible_scaleRoots_iff_of_ne_zero
    {K : Type*} [Field K] (p : K[X]) {r : K} (hr : r ≠ 0) :
    Irreducible (p.scaleRoots r) ↔ Irreducible p := by
  have hunit : ∀ (q : K[X]) (s : K), s ≠ 0 →
      (IsUnit (q.scaleRoots s) ↔ IsUnit q) := by
    intro q s hs
    constructor
    · intro hu
      rcases Polynomial.isUnit_iff.mp hu with ⟨c, hc, hC⟩
      apply Polynomial.isUnit_iff.mpr
      refine ⟨c, hc, ?_⟩
      calc
        C c = (C c).scaleRoots s⁻¹ := by simp
        _ = (q.scaleRoots s).scaleRoots s⁻¹ := by rw [hC]
        _ = q.scaleRoots (s * s⁻¹) := by rw [Polynomial.scaleRoots_mul]
        _ = q := by rw [mul_inv_cancel₀ hs, Polynomial.scaleRoots_one]
    · intro hu
      rcases Polynomial.isUnit_iff.mp hu with ⟨c, hc, hC⟩
      apply Polynomial.isUnit_iff.mpr
      refine ⟨c, hc, ?_⟩
      simp [← hC]
  constructor
  · intro hp
    rw [irreducible_iff] at hp ⊢
    refine ⟨(not_congr (hunit p r hr)).mp hp.1, ?_⟩
    intro a b hab
    have hab' : p.scaleRoots r = a.scaleRoots r * b.scaleRoots r := by
      calc
        p.scaleRoots r = (a * b).scaleRoots r := by rw [← hab]
        _ = a.scaleRoots r * b.scaleRoots r := by
          rw [Polynomial.mul_scaleRoots_of_noZeroDivisors]
    rcases hp.2 hab' with ha | hb
    · exact Or.inl ((hunit a r hr).mp ha)
    · exact Or.inr ((hunit b r hr).mp hb)
  · intro hp
    rw [irreducible_iff] at hp ⊢
    refine ⟨(not_congr (hunit p r hr)).mpr hp.1, ?_⟩
    intro a b hab
    have hab' : p = a.scaleRoots r⁻¹ * b.scaleRoots r⁻¹ := by
      calc
        p = (p.scaleRoots r).scaleRoots r⁻¹ := by
          rw [← Polynomial.scaleRoots_mul, mul_inv_cancel₀ hr,
            Polynomial.scaleRoots_one]
        _ = (a * b).scaleRoots r⁻¹ := by rw [hab]
        _ = a.scaleRoots r⁻¹ * b.scaleRoots r⁻¹ := by
          rw [Polynomial.mul_scaleRoots_of_noZeroDivisors]
    rcases hp.2 hab' with ha | hb
    · exact Or.inl ((hunit a r⁻¹ (inv_ne_zero hr)).mp ha)
    · exact Or.inr ((hunit b r⁻¹ (inv_ne_zero hr)).mp hb)

/-- Exact rational identity relating the integral monic transform to the
root-scaled B polynomial. -/
theorem invariantBMonicTransform_over_Q :
    invariantBMonicTransform.map (Int.castRingHom ℚ) =
      (invariantB.map (Int.castRingHom ℚ)).scaleRoots (279841 : ℚ) *
        C ((279841 : ℚ)⁻¹) := by
  have hdeg : (invariantB.map (Int.castRingHom ℚ)).natDegree = 8 := by
    norm_num [invariantB]
    compute_degree <;> norm_num
  have hdegTransform :
      (invariantBMonicTransform.map (Int.castRingHom ℚ)).natDegree = 8 := by
    norm_num [invariantBMonicTransform]
    compute_degree <;> norm_num
  ext n
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_scaleRoots, hdeg]
  by_cases hn : n ≤ 8
  · interval_cases n <;>
      norm_num [invariantBMonicTransform, invariantB, Polynomial.coeff_X,
        Polynomial.coeff_X_pow]
  · have hgt : 8 < n := by omega
    have hleft :
        (invariantBMonicTransform.map (Int.castRingHom ℚ)).coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hdegTransform.symm ▸ hgt)
    have hright : (invariantB.map (Int.castRingHom ℚ)).coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.symm ▸ hgt)
    rw [hleft, hright]
    simp

/-- The B polynomial is irreducible over `ℚ`, with no remaining transfer
interface. -/
theorem invariantB_irreducible_over_Q_closed :
    Irreducible (invariantB.map (Int.castRingHom ℚ)) := by
  let q : ℚ[X] := (invariantB.map (Int.castRingHom ℚ)).scaleRoots (279841 : ℚ)
  have hnormalized : Irreducible (q * C ((279841 : ℚ)⁻¹)) := by
    rw [← invariantBMonicTransform_over_Q]
    exact invariantBMonicTransform_irreducible_over_Q
  have hunit : IsUnit (C ((279841 : ℚ)⁻¹)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  have hscale : Irreducible q := (irreducible_mul_isUnit hunit).mp hnormalized
  exact (irreducible_scaleRoots_iff_of_ne_zero
    (invariantB.map (Int.castRingHom ℚ)) (by norm_num : (279841 : ℚ) ≠ 0)).mp hscale

end

end Biunimodular.F11
