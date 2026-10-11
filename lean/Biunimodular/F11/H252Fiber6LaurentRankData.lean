/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6LaurentRankInverse001
import Biunimodular.F11.H252Fiber6LaurentRankInverse002
import Biunimodular.F11.H252Fiber6LaurentRankInverse003
import Biunimodular.F11.H252Fiber6LaurentRankInverse004
import Biunimodular.F11.H252Fiber6LaurentRankInverse005
import Biunimodular.F11.H252Fiber6LaurentRankInverse006
import Biunimodular.F11.H252Fiber6LaurentRankInverse007
import Biunimodular.F11.H252Fiber6LaurentRankInverse008
import Biunimodular.F11.H252Fiber6LaurentRankInverse009
import Biunimodular.F11.H252Fiber6LaurentRankInverse010
import Biunimodular.F11.H252Fiber6LaurentRankInverse011
import Biunimodular.F11.H252Fiber6LaurentRankInverse012
import Biunimodular.F11.H252Fiber6LaurentRankInverse013
import Biunimodular.F11.H252Fiber6LaurentRankRows001
import Biunimodular.F11.H252Fiber6LaurentRankRows002
import Biunimodular.F11.H252Fiber6LaurentRankRows003
import Biunimodular.F11.H252Fiber6LaurentRankRows004
import Biunimodular.F11.H252Fiber6LaurentRankRows005
import Biunimodular.F11.H252Fiber6LaurentRankRows006
import Biunimodular.F11.H252Fiber6LaurentRankRows007
import Biunimodular.F11.H252Fiber6LaurentRankRows008
import Biunimodular.F11.H252Fiber6LaurentRankRows009
import Biunimodular.F11.H252Fiber6LaurentRankRows010
import Biunimodular.F11.H252Fiber6LaurentRankRows011
import Biunimodular.F11.H252Fiber6LaurentRankRows012
import Biunimodular.F11.H252Fiber6LaurentRankRows013

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

def h252Fiber6LaurentRankRows : Array TorusMacaulayRow := h252Fiber6LaurentRankRows001 ++ h252Fiber6LaurentRankRows002 ++ h252Fiber6LaurentRankRows003 ++ h252Fiber6LaurentRankRows004 ++ h252Fiber6LaurentRankRows005 ++ h252Fiber6LaurentRankRows006 ++ h252Fiber6LaurentRankRows007 ++ h252Fiber6LaurentRankRows008 ++ h252Fiber6LaurentRankRows009 ++ h252Fiber6LaurentRankRows010 ++ h252Fiber6LaurentRankRows011 ++ h252Fiber6LaurentRankRows012 ++ h252Fiber6LaurentRankRows013

def h252Fiber6LaurentRankInverseText : Array String := h252Fiber6LaurentRankInverseText001 ++ h252Fiber6LaurentRankInverseText002 ++ h252Fiber6LaurentRankInverseText003 ++ h252Fiber6LaurentRankInverseText004 ++ h252Fiber6LaurentRankInverseText005 ++ h252Fiber6LaurentRankInverseText006 ++ h252Fiber6LaurentRankInverseText007 ++ h252Fiber6LaurentRankInverseText008 ++ h252Fiber6LaurentRankInverseText009 ++ h252Fiber6LaurentRankInverseText010 ++ h252Fiber6LaurentRankInverseText011 ++ h252Fiber6LaurentRankInverseText012 ++ h252Fiber6LaurentRankInverseText013

def h252Fiber6LaurentRankInverse : Array (Array ℤ) := h252Fiber6LaurentRankInverseText.map torusMacaulayParseIntegerRow

end Biunimodular.F11
