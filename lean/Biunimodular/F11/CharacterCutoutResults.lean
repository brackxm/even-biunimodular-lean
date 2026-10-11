/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Conductor77CharacterCutout

set_option autoImplicit false
namespace Biunimodular.F11.Results
noncomputable section

/-- The actual sextic field is the fixed field of the primitive character
on the canonical conductor-77 cyclotomic Galois group. -/
theorem conductor77_character_cutout :
    conductor77PeriodField = IntermediateField.fixedField conductor77CyclotomicCharacter.ker :=
  conductor77PeriodField_eq_character_fixedField

end
end Biunimodular.F11.Results
