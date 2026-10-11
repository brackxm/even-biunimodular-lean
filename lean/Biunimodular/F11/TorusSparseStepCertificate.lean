/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusSparseIdealMembership
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace Biunimodular.F11

/-- Each parent is a multiplier paired with an earlier basis index. -/
structure TorusSparseStep where
  scale : ℤ
  parents : List (List RurInverseTerm7 × ℕ)
  deriving Inhabited

def torusSparseStepProducts (basis : ℕ → List RurInverseTerm7) (s : TorusSparseStep) :
    List (List RurInverseTerm7 × List RurInverseTerm7) :=
  s.parents.map fun p => (p.1, basis p.2)

def torusSparseStepCheck (basis : ℕ → List RurInverseTerm7) (i : ℕ)
    (s : TorusSparseStep) : Prop :=
  s.scale ≠ 0 ∧ (∀ p ∈ s.parents, p.2 < i) ∧
    rurInverseSparseNormalize (rurInverseSparseSumProducts
      (torusSparseStepProducts basis s ++ [(rurInverseSparseScale (-1)
        (rurInverseSparseScale s.scale (basis i)), rurInverseSparseOne)])) = []

instance (basis : ℕ → List RurInverseTerm7) (i : ℕ) (s : TorusSparseStep) :
    Decidable (torusSparseStepCheck basis i s) := by
  unfold torusSparseStepCheck
  infer_instance

noncomputable section

theorem torusSparseStep_mem
    (I : Ideal (MvPolynomial (Fin 7) ℂ)) (basis : ℕ → List RurInverseTerm7)
    (i : ℕ) (s : TorusSparseStep)
    (h : torusSparseStepCheck basis i s)
    (hI : ∀ p ∈ s.parents, torusSparsePolynomial (basis p.2) ∈ I) :
    torusSparsePolynomial (basis i) ∈ I := by
  apply torusSparseIdealCertificate_scaled_sound I (torusSparseStepProducts basis s)
    (basis i) s.scale h.1 ?_ h.2.2
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hI q hq

/-- A block of exact checks extends any already proved membership prefix.
This allows large traces to be replayed without one Lean process per step. -/
theorem torusSparseStepBlock_mem
    (I : Ideal (MvPolynomial (Fin 7) ℂ)) (basis : ℕ → List RurInverseTerm7)
    (steps : ℕ → TorusSparseStep) (start stop : ℕ)
    (hbase : ∀ i, i < start → torusSparsePolynomial (basis i) ∈ I)
    (hcheck : ∀ i, start ≤ i → i < stop → torusSparseStepCheck basis i (steps i)) :
    ∀ i, i < stop → torusSparsePolynomial (basis i) ∈ I := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hs : start ≤ i
    · have hc := hcheck i hs hi
      apply torusSparseStep_mem I basis i (steps i) hc
      intro p hp
      have hpi := hc.2.1 p hp
      exact ih p.2 hpi (hpi.trans hi)
    · exact hbase i (by omega)

end
end Biunimodular.F11
