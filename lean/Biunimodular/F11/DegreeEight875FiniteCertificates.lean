/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.DegreeEight875WordData

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Biunimodular.F11

/-!
# Finite replay certificates for degree-eight generation

These are exact decidable statements about permutations of `Fin 8`.  The
word lists are evaluated inside Lean; their entries are not trusted as
proofs.  The group-theoretic bridge from these computations to generation
is proved separately.
-/

/-- Every normalized 7-cycle outside the 12 exceptional cases gives a swap
as a word in the canonical 8-cycle and the 7-cycle. -/
theorem s8_swap_word_or_exception :
    ∀ b : Equiv.Perm (Fin 8),
      b.support.card = 7 → b ^ 7 = 1 → b 7 = 7 →
      b ∈ s8ExceptionalSeven ∨
        ∃ w ∈ s8SwapWords,
          (s8EvalWord s8CanonicalEight b w).support.card = 2 := by
  native_decide

/-- In every exceptional 8/7 case, adjoining any 5-cycle yields a
3-cycle as a commutator with an explicit word in the 8/7 generators. -/
theorem s8_exceptional_commutator_word :
    ∀ b : Equiv.Perm (Fin 8),
      b ∈ s8ExceptionalSeven →
      ∀ c : Equiv.Perm (Fin 8),
        c.support.card = 5 → c ^ 5 = 1 →
        ∃ w ∈ s8CommutatorWords,
          (c * s8EvalWord s8CanonicalEight b w * c⁻¹ *
            (s8EvalWord s8CanonicalEight b w)⁻¹).support.card = 3 := by
  native_decide

def s8Image (p : Equiv.Perm (Fin 8)) (S : Finset (Fin 8)) : Finset (Fin 8) :=
  S.image p

/-- The canonical 8-cycle and any normalized 7-cycle have no common
nontrivial block.  This finite statement is the computational core of
primitivity; the conversion from blocks to `IsPreprimitive` is separate. -/
theorem s8_no_common_nontrivial_block :
    ∀ b : Equiv.Perm (Fin 8),
      b.support.card = 7 → b ^ 7 = 1 → b 7 = 7 →
      ∀ S : Finset (Fin 8),
        1 < S.card → S.card < 8 →
        ¬ ((∀ n ∈ Finset.range 8,
              s8Image (s8CanonicalEight ^ n) S = S ∨
                Disjoint (s8Image (s8CanonicalEight ^ n) S) S) ∧
           (∀ n ∈ Finset.range 7,
              s8Image (b ^ n) S = S ∨ Disjoint (s8Image (b ^ n) S) S)) := by
  native_decide

end Biunimodular.F11
