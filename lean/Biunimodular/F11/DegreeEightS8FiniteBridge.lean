/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Group.Subgroup.Basic

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Degree-eight 8/7/5 finite generation bridge

The B-sector does not need the general Jordan prime-cycle theorem for a
5-cycle. A finite calculation in `S_8`, combined with Mathlib's swap and
3-cycle cases of Jordan's theorem, proves the specialized statement:

* any subgroup of `S_8` containing an 8-cycle, a 7-cycle and a 5-cycle is all
  of `S_8`.

The checked word certificates in `DegreeEight875FiniteCertificates` reduce
this to 720 normalized seven-cycles. In 708 cases a word in the eight- and
seven-cycles is a swap. In the remaining 12 cases a commutator with any
five-cycle is a three-cycle.

The theorem below is proved in `DegreeEight875Normalization`.
-/

abbrev S8Perm := Equiv.Perm (Fin 8)

/-- Exact finite generation statement. -/
def DegreeEight875GenerationLemma : Prop :=
  ∀ a b c : S8Perm,
    (a.IsCycle ∧ a.support.card = 8) →
    (b.IsCycle ∧ b.support.card = 7) →
    (c.IsCycle ∧ c.support.card = 5) →
    Subgroup.closure ({a, b, c} : Set S8Perm) = ⊤

/-- Separate Galois-image input carrying the three cycle witnesses expected
from the Dedekind factorization patterns `8`, `1+7`, and `1+1+1+5`.
The construction of this input from the modular polynomial certificates is
outside the finite group-theory proof. -/
structure DegreeEightGaloisPermutationData where
  image : Subgroup S8Perm
  hasEightCycle : ∃ g : image, g.1.IsCycle ∧ g.1.support.card = 8
  hasSevenCycle : ∃ g : image, g.1.IsCycle ∧ g.1.support.card = 7
  hasFiveCycle : ∃ g : image, g.1.IsCycle ∧ g.1.support.card = 5

/-- The finite 8/7/5 generation lemma immediately identifies the concrete
Galois image with the full symmetric group. -/
theorem degreeEight_image_eq_top_of_875
    (h875 : DegreeEight875GenerationLemma)
    (h : DegreeEightGaloisPermutationData) : h.image = ⊤ := by
  rcases h.hasEightCycle with ⟨a, ha⟩
  rcases h.hasSevenCycle with ⟨b, hb⟩
  rcases h.hasFiveCycle with ⟨c, hc⟩
  have htop := h875 a.1 b.1 c.1 ha hb hc
  apply top_unique
  rw [← htop]
  exact (Subgroup.closure_le _).2 (by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact a.2
    · exact b.2
    · exact c.2)

end Biunimodular.F11
