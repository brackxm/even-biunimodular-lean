/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusOriginalGeneratorsData
import Biunimodular.F11.H252RurInputData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def rurInverseGenerator8 := rurInverseSparseOfX h252RurHCoeffs

def rurInverseVariable1 : List RurInverseTerm7 := [⟨1, ⟨1, 0, 0, 0, 0, 0, 0⟩⟩]

def rurInverseVariable2 : List RurInverseTerm7 := [⟨1, ⟨0, 1, 0, 0, 0, 0, 0⟩⟩]

def rurInverseVariable3 : List RurInverseTerm7 := [⟨1, ⟨0, 0, 1, 0, 0, 0, 0⟩⟩]

def rurInverseVariable4 : List RurInverseTerm7 := [⟨1, ⟨0, 0, 0, 1, 0, 0, 0⟩⟩]

def rurInverseVariable5 : List RurInverseTerm7 := [⟨1, ⟨0, 0, 0, 0, 0, 1, 0⟩⟩]

def rurInverseVariable6 : List RurInverseTerm7 := [⟨1, ⟨0, 0, 0, 0, 1, 0, 0⟩⟩]


end Biunimodular.F11
