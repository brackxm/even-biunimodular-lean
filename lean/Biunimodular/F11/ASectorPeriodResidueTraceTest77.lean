/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodOrderSaturation77

set_option autoImplicit false
namespace Biunimodular.F11

def periodResidueVector77 {p : ℕ} (a b c d e f : Fin p) : Fin 6 → ℤ :=
  ![(a.val : ℤ), (b.val : ℤ), (c.val : ℤ), (d.val : ℤ), (e.val : ℤ), (f.val : ℤ)]

/-- A computable trace obstruction for every nonzero residue class in the
trace-Gram kernel. Powers one through six suffice for the certificate. -/
def PeriodResidueTraceTest77 (p : ℤ) (v : Fin 6 → ℤ) : Prop :=
  (∃ i, v i ≠ 0) →
    (∀ j, p ∣ ∑ i : Fin 6, v i * periodOrderTraceGramData77 i j) →
      ∃ k : Fin 6, ¬ p ^ (k.val + 1) ∣
        Matrix.trace (periodIntegerMultiplicationMatrix77 v ^ (k.val + 1))

instance periodResidueTraceTest77_decidable (p : ℤ) (v : Fin 6 → ℤ) :
    Decidable (PeriodResidueTraceTest77 p v) := by
  unfold PeriodResidueTraceTest77
  infer_instance

end Biunimodular.F11
