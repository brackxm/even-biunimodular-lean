/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber3LaurentRankInverse001
import Biunimodular.F11.H252Fiber3LaurentRankInverse002
import Biunimodular.F11.H252Fiber3LaurentRankInverse003
import Biunimodular.F11.H252Fiber3LaurentRankInverse004
import Biunimodular.F11.H252Fiber3LaurentRankInverse005
import Biunimodular.F11.H252Fiber3LaurentRankInverse006
import Biunimodular.F11.H252Fiber3LaurentRankInverse007
import Biunimodular.F11.H252Fiber3LaurentRankInverse008
import Biunimodular.F11.H252Fiber3LaurentRankInverse009
import Biunimodular.F11.H252Fiber3LaurentRankInverse010
import Biunimodular.F11.H252Fiber3LaurentRankInverse011
import Biunimodular.F11.H252Fiber3LaurentRankInverse012
import Biunimodular.F11.H252Fiber3LaurentRankInverse013
import Biunimodular.F11.H252Fiber3LaurentRankRows001
import Biunimodular.F11.H252Fiber3LaurentRankRows002
import Biunimodular.F11.H252Fiber3LaurentRankRows003
import Biunimodular.F11.H252Fiber3LaurentRankRows004
import Biunimodular.F11.H252Fiber3LaurentRankRows005
import Biunimodular.F11.H252Fiber3LaurentRankRows006
import Biunimodular.F11.H252Fiber3LaurentRankRows007
import Biunimodular.F11.H252Fiber3LaurentRankRows008
import Biunimodular.F11.H252Fiber3LaurentRankRows009
import Biunimodular.F11.H252Fiber3LaurentRankRows010
import Biunimodular.F11.H252Fiber3LaurentRankRows011
import Biunimodular.F11.H252Fiber3LaurentRankRows012
import Biunimodular.F11.H252Fiber3LaurentRankRows013

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

def h252Fiber3LaurentRankRows : Array TorusMacaulayRow := h252Fiber3LaurentRankRows001 ++ h252Fiber3LaurentRankRows002 ++ h252Fiber3LaurentRankRows003 ++ h252Fiber3LaurentRankRows004 ++ h252Fiber3LaurentRankRows005 ++ h252Fiber3LaurentRankRows006 ++ h252Fiber3LaurentRankRows007 ++ h252Fiber3LaurentRankRows008 ++ h252Fiber3LaurentRankRows009 ++ h252Fiber3LaurentRankRows010 ++ h252Fiber3LaurentRankRows011 ++ h252Fiber3LaurentRankRows012 ++ h252Fiber3LaurentRankRows013

def h252Fiber3LaurentRankInverseText : Array String := h252Fiber3LaurentRankInverseText001 ++ h252Fiber3LaurentRankInverseText002 ++ h252Fiber3LaurentRankInverseText003 ++ h252Fiber3LaurentRankInverseText004 ++ h252Fiber3LaurentRankInverseText005 ++ h252Fiber3LaurentRankInverseText006 ++ h252Fiber3LaurentRankInverseText007 ++ h252Fiber3LaurentRankInverseText008 ++ h252Fiber3LaurentRankInverseText009 ++ h252Fiber3LaurentRankInverseText010 ++ h252Fiber3LaurentRankInverseText011 ++ h252Fiber3LaurentRankInverseText012 ++ h252Fiber3LaurentRankInverseText013

def h252Fiber3LaurentRankInverse : Array (Array ℤ) := h252Fiber3LaurentRankInverseText.map torusMacaulayParseIntegerRow

end Biunimodular.F11
