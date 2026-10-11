/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber7LaurentRankPolynomialTables

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
def h252Fiber7LaurentRankIntegralRows013 : Array TorusMacaulayRow := (#[
"461 0;797 0",
"462 0;798 0;807 0",
"441 0;463 0;807 0",
"464 0;799 0;808 0",
"442 0;465 0;808 0",
"443 0;466 0",
"467 0;800 0;809 0",
"444 0;468 0;809 0",
"445 0;469 0",
"446 0;470 0",
"810 0;1036 0",
"447 0;810 0;1040 4",
"448 0",
"449 0",
"450 0",
"451 0;1037 0",
"452 0;801 0;1180 0",
"453 0;1037 0;1038 0",
"451 0;454 0;1180 4",
"455 0;802 0",
"456 0;803 0",
"452 0;457 0",
"458 0;1038 0;1039 0",
"453 0;459 0",
"454 0;460 0",
"461 0;804 0",
"462 0;805 0",
"455 0;463 0",
"464 0;806 0",
"456 0;465 0",
"457 0;466 0",
"467 0;1039 0;1040 0",
"458 0;468 0",
"459 0;469 0",
"460 0;470 0",
"807 0",
"808 0",
"461 0",
"809 0",
"462 0",
"463 0",
"810 0",
"464 0",
"465 0",
"466 0",
"1040 0",
"467 0",
"468 0",
"469 0",
"470 0"] : Array String).map (torusMacaulayParseIndexedRow h252Fiber7LaurentRankIntegralCoefficients)

end Biunimodular.F11
