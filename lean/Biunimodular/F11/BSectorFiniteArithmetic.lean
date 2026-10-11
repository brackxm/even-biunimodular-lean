/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.InvariantPolynomialData
import Biunimodular.F11.InvariantFiniteFieldIrreducibility
import Biunimodular.F11.InvariantBMonicTransform
import Biunimodular.F11.BSectorFrobeniusCertificates

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# B-sector exact finite-arithmetic sidecar

This module preserves the exact characteristic-zero, mod-5, mod-37, mod-211,
and discriminant certificates used to replay the full finite arithmetic route.
It is deliberately separate from `BSectorS8Assembly`: the 8/7/5 group-theory assembly only needs concrete permutation data and the finite
generation lemma, while these heavier modular certificates remain available as
an independent exact verification layer.
-/

structure BSectorFiniteArithmetic : Prop where
  irreducibleOverQ :
    Irreducible (invariantB.map (Int.castRingHom ℚ))
  irreducibleMod5 : Irreducible invariantB5
  factor37 :
    invariantB.map (Int.castRingHom (ZMod 37)) = 10 * B37lin * B37seven
  irreducible7 : Irreducible B37seven
  factor211 :
    invariantB.map (Int.castRingHom (ZMod 211)) =
      55 * B211lin1 * B211lin2 * B211lin3 * B211five
  irreducible5 : Irreducible B211five
  discNotSquare : ¬ ∃ z : ℤ, z*z = invariantBDiscriminant

theorem bSectorFiniteArithmetic : BSectorFiniteArithmetic where
  irreducibleOverQ := invariantB_irreducible_over_Q_closed
  irreducibleMod5 := B_mod5_cycle8
  factor37 := invariantB_mod37_factor
  irreducible7 := B37seven_irreducible
  factor211 := invariantB_mod211_factor
  irreducible5 := B211five_irreducible
  discNotSquare := invariantB_discriminant_not_square

end Biunimodular.F11
