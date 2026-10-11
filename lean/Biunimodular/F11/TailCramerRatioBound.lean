/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.TailCramerPerturbation

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

private lemma abs_sub_cramer_div_le
    {Δ x N ε : ℝ}
    (hΔ : (1 / 1000000 : ℝ) ≤ |Δ|)
    (hε : |Δ * x - N| ≤ ε)
    (hεnum : ε ≤ (2112 / 100000000000000 : ℝ)) :
    |x - N / Δ| ≤ (3 / 100000 : ℝ) := by
  have hpos : 0 < |Δ| := lt_of_lt_of_le (by norm_num) hΔ
  have hne : Δ ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hpos
    linarith
  rw [show x - N / Δ = (Δ * x - N) / Δ by field_simp [hne], abs_div]
  apply (div_le_iff₀ hpos).2
  have hmul : (3 / 100000 : ℝ) * |Δ| ≥ (3 / 100000000000 : ℝ) := by
    nlinarith
  calc
    |Δ * x - N| ≤ ε := hε
    _ ≤ (2112 / 100000000000000 : ℝ) := hεnum
    _ ≤ (3 / 100000000000 : ℝ) := by norm_num
    _ ≤ (3 / 100000 : ℝ) * |Δ| := hmul

/-- With candidate radius at most `5e-15` and determinant margin `1e-6`,
every actual tail coordinate is within `3e-5` of the Cramer solution at the
fixed center. -/
theorem tail_close_to_center_cramer_ratio
    {δ a b c d e f A B C D E F g h j k : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 200000000000000 : ℝ))
    (hclose : close6 δ a b c d e f A B C D E F)
    (hu : unit6 a b c d e f) (hU : unit6 A B C D E F)
    (hg : |g| ≤ 1) (hh : |h| ≤ 1) (hj : |j| ≤ 1) (hk : |k| ≤ 1)
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) =
      tailRhs a b c d e f)
    (hdet : (1 / 1000000 : ℝ) ≤ |tailDetR A B C D E F|) :
    |g - tailCramerG A B C D E F / tailDetR A B C D E F| ≤ (3 / 100000 : ℝ) ∧
    |h - tailCramerH A B C D E F / tailDetR A B C D E F| ≤ (3 / 100000 : ℝ) ∧
    |j - tailCramerJ A B C D E F / tailDetR A B C D E F| ≤ (3 / 100000 : ℝ) ∧
    |k - tailCramerK A B C D E F / tailDetR A B C D E F| ≤ (3 / 100000 : ℝ) := by
  have herr := tail_cramer_error_le hδ hclose hu hU hg hh hj hk hsol
  have hε : 192 * (22 * δ) ≤ (2112 / 100000000000000 : ℝ) := by
    nlinarith
  exact ⟨
    abs_sub_cramer_div_le hdet herr.1 hε,
    abs_sub_cramer_div_le hdet herr.2.1 hε,
    abs_sub_cramer_div_le hdet herr.2.2.1 hε,
    abs_sub_cramer_div_le hdet herr.2.2.2 hε⟩

/-- If the actual tail coordinate is itself in a certified candidate box,
then the center Cramer ratio lies strictly inside the scanner's `10^-4`
window around that phase center.  The `3e-5 + 5e-15` margin is deliberately
far below `10^-4`. -/
lemma center_cramer_near_candidate
    {x cr center δ : ℝ}
    (hx : |x - cr| ≤ (3 / 100000 : ℝ))
    (hc : |x - center| ≤ δ)
    (hδ : δ ≤ (1 / 200000000000000 : ℝ)) :
    |cr - center| < (1 / 10000 : ℝ) := by
  have htri : |cr - center| ≤ |cr - x| + |x - center| := by
    calc
      |cr - center| = |(cr - x) + (x - center)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  rw [abs_sub_comm cr x] at htri
  nlinarith

end Biunimodular.F11
