/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodResidueTraceTest77

set_option autoImplicit false
namespace Biunimodular.F11

theorem periodResidueEleven77_trace_test : ∀ a b c d e f : Fin 11,
    PeriodResidueTraceTest77 11 (periodResidueVector77 a b c d e f) := by
  native_decide

end Biunimodular.F11
