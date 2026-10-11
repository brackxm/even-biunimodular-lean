/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorX77Steps6
import Biunimodular.F11.ASectorF30CharacteristicZero

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-- The exact degree-thirty relation among the cyclotomic reductions. -/
theorem aSectorX77_linear_relation :
    -456153866030714364121126903 * aSectorXR0
      - 32954219911505547835456793594 * aSectorXR1
      + 83528158299559974015947521205 * aSectorXR2
      + 1316315013975085942280916680381 * aSectorXR3
      - 5828394446256998667721626184074 * aSectorXR4
      - 3840698481089467590597304360291 * aSectorXR5
      + 68266611991062799243367417279916 * aSectorXR6
      - 157299625302500222981526337520193 * aSectorXR7
      + 119291494077820597119400618426622 * aSectorXR8
      + 89714624882821009072497623516389 * aSectorXR9
      - 252755680873644008457161163519505 * aSectorXR10
      + 199314066267368103535534738244249 * aSectorXR11
      - 43617079462286217767567738891071 * aSectorXR12
      - 40161170956744531780094443253511 * aSectorXR13
      + 36316559791548833974912728696164 * aSectorXR14
      - 12138569497725711799922058991018 * aSectorXR15
      + 977562455936223920891761501484 * aSectorXR16
      + 626515722982729950680870481999 * aSectorXR17
      - 233393128793190084245498290704 * aSectorXR18
      + 32180113517667895948142129386 * aSectorXR19
      - 942383865956941122285175220 * aSectorXR20
      - 197888708481008060437814431 * aSectorXR21
      + 12857530584069173836477721 * aSectorXR22
      + 322210699153065066313739 * aSectorXR23
      + 2159659762203647843370 * aSectorXR24
      + 4329785713916463185 * aSectorXR25
      + 3709595988698677 * aSectorXR26
      + 1513968321019 * aSectorXR27
      + 306613923 * aSectorXR28
      + 29106 * aSectorXR29
      + aSectorXR30 = 0 := by
  simp only [aSectorXR0, aSectorXR1, aSectorXR2, aSectorXR3, aSectorXR4, aSectorXR5, aSectorXR6, aSectorXR7, aSectorXR8, aSectorXR9, aSectorXR10, aSectorXR11, aSectorXR12, aSectorXR13, aSectorXR14, aSectorXR15, aSectorXR16, aSectorXR17, aSectorXR18, aSectorXR19, aSectorXR20, aSectorXR21, aSectorXR22, aSectorXR23, aSectorXR24, aSectorXR25, aSectorXR26, aSectorXR27, aSectorXR28, aSectorXR29, aSectorXR30, aSectorXRed]
  ring

end
end Biunimodular.F11
