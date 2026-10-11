/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.RingTheory.Polynomial.Bernstein
public import Biunimodular.F11.P150PolynomialData11
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
public meta import Mathlib.RingTheory.Polynomial.Bernstein
public meta import Biunimodular.F11.P150PolynomialData11
public meta import Mathlib.Basic.Real.Basic
public meta import Mathlib.Algebra.Algebra.Rat

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# A rational positivity certificate for the P150 cofactor

The degree-102 cofactor is even, so it is a degree-51 polynomial in
`y = k²`.  Its Bernstein coefficients are strictly positive on each of the
two affine halves `[0, 1/2]` and `[1/2, 1]`.  The two closed polynomial
identities below make this an exact rational certificate rather than a
floating-point root count.
-/

def r102LowerBernsteinCoeffs11 : List ℚ := [
  52422651536636717671204157171598525230137152512,
  (19098546785575999847675901583720874915592813411880 : ℚ) / 51,
  (1561656861279078161039947272315939760775800287937967 : ℚ) / 1700,
  (147928667098873049614785624629193683860496264411864587 : ℚ) / 83300,
  (30604216263956721079009153175123406599832102685493893 : ℚ) / 9996,
  (2311231109644360605820631079872125565202521249315513087 : ℚ) / 469812,
  (33876915201705008456806063209404099471944410821767588702 : ℚ) / 4502365,
  (6826594278856518335852763359996717911007872435216416872 : ℚ) / 615825,
  (131064165246239086948001877036059734911606868248581774953 : ℚ) / 8269650,
  (130046464680474922953453127425885066306829105528024523399 : ℚ) / 5884550,
  (70072358668852591437449418860992655058603588530687181550841 : ℚ) / 2323220340,
  (3847949297218624094982639136057594445210601653481538260289477 : ℚ) / 95252033940,
  (8446610379296407852560383194522581482996401449185009748269331 : ℚ) / 158753389900,
  (276221850145492093043893064691414313013083779289480994828627 : ℚ) / 4002186300,
  (404730414775282227754887713270905045344737911359201850824091 : ℚ) / 4584064450,
  (3782339906205448169852959074522900538285250257216555627990307 : ℚ) / 33922076930,
  (47533688071743374821563228842864911842823610677362641480569319 : ℚ) / 341643774795,
  (110246955427916074750155194317285821547897538651083913421038059 : ℚ) / 642220395075,
  (1230936316764846007788004860010422037325024308590985613759219501 : ℚ) / 5873875426300,
  (4462605464447065748171791554343245118880430609791660516982672659 : ℚ) / 17621626278900,
  (356064394979964023000814231888158874809075258382166011191439681 : ℚ) / 1174775085260,
  (373956738349398013782964017539800557962184561248700267151033729 : ℚ) / 1040515075516,
  (119422007644152610831835819341776169053189932726617353743863609 : ℚ) / 282748661825,
  (4034847648784401977114961535664577948185136974456541256634535363 : ℚ) / 8199711192925,
  (65258464653089509543217180042041381065902393464647859315178984841 : ℚ) / 114795956700950,
  (80754064978895865285896419145886679959439096065337168756123790191 : ℚ) / 123979633237026,
  (61188195598082044795085578219853903392448544794812759690644733459 : ℚ) / 82653088824684,
  (191647500469005388372113193450206642865816398505438143351508324559 : ℚ) / 229591913401900,
  (18377025723665934600118107306975747591786908667496264792058614679 : ℚ) / 19679306863020,
  (80890356061906390388339189536078401895654208078380319511945540853 : ℚ) / 78038630663700,
  (34937151837000602955804390302089283617893180958649463946658735 : ℚ) / 30603384574,
  (439667673716304340644795637277983664897127336155832571288898981 : ℚ) / 352432525578,
  (5958515505948729479954289251917336662309095749402426333195144466 : ℚ) / 4405406569725,
  (1159669598560811433911133913067212111071174675911997828850194326 : ℚ) / 797168807855,
  (91696332585976744250272952143842758297806162042243767148693401739 : ℚ) / 59084276346900,
  (47120236920448119973314098665557129730612068006445734894583551581 : ℚ) / 28698077082780,
  (5491725448206260378061243763589789067928304758889718740121666993 : ℚ) / 3188675231420,
  (771533028211152101697244721895081260145231604066475887820338317 : ℚ) / 430902058300,
  (219586738724290945174671233956073075422226064826434819405936236 : ℚ) / 119065042425,
  (74662285854740997278857990966897677639832296086440517492177042 : ℚ) / 39688347475,
  (90455565362555462049852786394382538412563783324248304388984969 : ℚ) / 47626016970,
  (104917423624793822144953274508613468531050347056458057366489 : ℚ) / 55314770,
  (1035645119614061394281380702064503364895063586364916575218753 : ℚ) / 553147700,
  (211320477872775397656359648254129150711424038316230563129767 : ℚ) / 115775100,
  (29040710133707379579579932950939478479905856277556759805937 : ℚ) / 16539300,
  (1764077328072950571909154883634501032863130153389630282849 : ℚ) / 1059380,
  (1827108092128846618386116855578077053458090679802398141767 : ℚ) / 1174530,
  (178781377684009405114311273096863917162145493742136798261 : ℚ) / 124950,
  (26993365614756407846641963933487179693711064700293867287 : ℚ) / 20825,
  (1477646443712125729762289986272559433847671335625344489 : ℚ) / 1275,
  (209773014140861680568223527048824371287016397209725489 : ℚ) / 204,
  (3663209239233198959008040455015870171696311195688103 : ℚ) / 4
]

def r102UpperBernsteinCoeffs11 : List ℚ := [
  (3663209239233198959008040455015870171696311195688103 : ℚ) / 4,
  (163874328260924613250596599362794386226007344750461017 : ℚ) / 204,
  (903912870212912388291953390197184620585058179884538589 : ℚ) / 1275,
  (2683341672107818323334703807564956529583400181897131712 : ℚ) / 4165,
  (25948388131495148483813513754171104954010773271045233871 : ℚ) / 41650,
  (258961255952687485920849498757469444969801690971234818653 : ℚ) / 391510,
  (14019205702311576972574872580207069468848231471136681219601 : ℚ) / 18009460,
  (115273959758754213177573079464960124415933463243393959334763 : ℚ) / 115775100,
  (51626080692569736553341963872695342566747272095289681893741 : ℚ) / 38591700,
  (1013513473869343793577702769412558264181070686715342528576233 : ℚ) / 553147700,
  (126756929410756189253520469378066713490101193031362566995027 : ℚ) / 50504790,
  (32422367373989488251088119488712805768238904273423461097391199 : ℚ) / 9525203394,
  (7224288032291831141287383700807035996801424158299633332750310 : ℚ) / 1587533899,
  (713054649800219888013428880562272914212850241438408145044095576 : ℚ) / 119065042425,
  (10029926787689823874793234392010412694896270248025877427490209639 : ℚ) / 1292706174900,
  (4510944427451966210065160376560451778445464152077665645648266979 : ℚ) / 455525033060,
  (8317593949293532408124958281079503584267399060812404808781097047 : ℚ) / 667397141460,
  (22308743458250040518076352549547090912889710935772030421605394059 : ℚ) / 1441079910900,
  (106001447115515037699745273269896756923888364495077380509127979366 : ℚ) / 5580181654985,
  (82877471811095722325365588662777438128400366736352925217595855 : ℚ) / 3596250261,
  (9748297146564961777153358594236385399158931689684596540668529101 : ℚ) / 352432525578,
  (5028646020656564215109018982546488336838886649648101958924350731 : ℚ) / 153016922870,
  (179850881054391106589098550336009487781599008911604530015509791 : ℚ) / 4650970300,
  (4435789845232553188155097594091114034678731035870683848219996568647 : ℚ) / 98396534315100,
  (11958177114559079838013206373324215611671726874155859484096142039343 : ℚ) / 229591913401900,
  (4930351647696982474301392403653090653970433308091766573833495163659 : ℚ) / 82653088824684,
  (962005128973327353200550452618714423254581519495360901054964207 : ℚ) / 14203188594,
  (1250541618351987966769714459646673283377324816790723911735773961409 : ℚ) / 16399422385850,
  (2094075005088735096664271594185848043265406383401732402756109124397 : ℚ) / 24599133578775,
  (612810827903385597870797143059527769623789453678585522881578625067 : ℚ) / 6503219221975,
  (31651515591891029769714847507013366456921335796591881733234425141 : ℚ) / 306033845740,
  (7777146024229334941545493108566051506060563551862589610979094469 : ℚ) / 69104416780,
  (713076200236516822834400409705760649287268686003993528548708770353 : ℚ) / 5873875426300,
  (14485187298401523454238649203127380800238365039404846040792438073967 : ℚ) / 111603633099700,
  (2031174299473768008599880026454840809242914773301994756733856016201 : ℚ) / 14771069086725,
  (5051531343355247705968311465575819345557148177980384274242306594 : ℚ) / 34997654979,
  (34179533847872135033429148643302841620207987630567337962337539091 : ℚ) / 227762516530,
  (33285864918833672628933550531779186662283116106330376692872785541 : ℚ) / 215451029150,
  (10711963859760289639787691894129912601911482096688935623686676963 : ℚ) / 68037167100,
  (25203882661776814898293998369776107867916483375729296020609868951 : ℚ) / 158753389900,
  (307771835630124741924670397800047321196079652292609776612631093 : ℚ) / 1943919060,
  (72502020662637756763847440255117013874958711547548642087140013 : ℚ) / 464644068,
  (8397762390219315576663166199480221392842347540988054402478141 : ℚ) / 55314770,
  (8427689706293416452271770666557550799714111575028355686674197 : ℚ) / 57887550,
  (794520169492153693331217585828474584599808026065341732189756 : ℚ) / 5788755,
  (114079168175646663833362376884775452492515206006082905033154 : ℚ) / 900473,
  (267186745230369700896791985154857097508426489020692245624891 : ℚ) / 2349060,
  (4912205973664126928225342026985785863381318963414909420637 : ℚ) / 49980,
  (6692789654045231906519808171314978074328385109196329480523 : ℚ) / 83300,
  (308236356160506521899726351515919690652631380936582870549 : ℚ) / 5100,
  (2047906126745930024804610296569666394913587236516883212 : ℚ) / 51,
  23259918611879306358289549439122245880819438565614569
]

/-- Executable coefficient-list addition used to replay the two identities. -/
def coefficientAddQ11 : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: coefficientAddQ11 xs ys

def coefficientScaleQ11 (c : ℚ) : List ℚ → List ℚ := List.map (c * ·)

/-- Executable convolution of ascending rational coefficient lists. -/
def coefficientMulQ11 : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | _, [] => []
  | x :: xs, ys =>
      coefficientAddQ11 (coefficientScaleQ11 x ys)
        (0 :: coefficientMulQ11 xs ys)

def coefficientPowQ11 (xs : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => coefficientMulQ11 xs (coefficientPowQ11 xs n)

/-- Coefficients after the affine substitution `X ↦ a + dX`. -/
def coefficientAffineQ11 : List ℚ → ℚ → ℚ → List ℚ
  | [], _, _ => []
  | c :: cs, a, d =>
      coefficientAddQ11 [c]
        (coefficientMulQ11 [a, d] (coefficientAffineQ11 cs a d))

def coefficientBernsteinBasisQ11 (n i : ℕ) : List ℚ :=
  coefficientScaleQ11 (n.choose i)
    (coefficientMulQ11 (coefficientPowQ11 [0, 1] i)
      (coefficientPowQ11 [1, -1] (n - i)))

def coefficientBernsteinCombinationQ11 (n i : ℕ) : List ℚ → List ℚ
  | [] => []
  | c :: cs =>
      coefficientAddQ11
        (coefficientScaleQ11 c (coefficientBernsteinBasisQ11 n i))
        (coefficientBernsteinCombinationQ11 n (i + 1) cs)

/-- Polynomial semantics of an ascending rational coefficient list. -/
def polynomialOfCoefficientsQ11 (cs : List ℚ) : ℚ[X] :=
  cs.foldr (fun c p => C c + X * p) 0

/-- The corresponding Bernstein combination, kept recursive so positivity
proofs need no large normalization. -/
def bernsteinCombinationQ11 (n i : ℕ) : List ℚ → ℚ[X]
  | [] => 0
  | c :: cs =>
      C c * bernsteinPolynomial ℚ n i +
        bernsteinCombinationQ11 n (i + 1) cs

@[simp] theorem polynomialOfCoefficientsQ11_nil :
    polynomialOfCoefficientsQ11 [] = 0 := rfl

@[simp] theorem polynomialOfCoefficientsQ11_cons (c : ℚ) (cs : List ℚ) :
    polynomialOfCoefficientsQ11 (c :: cs) =
      C c + X * polynomialOfCoefficientsQ11 cs := rfl

theorem polynomialOfCoefficientsQ11_add (xs ys : List ℚ) :
    polynomialOfCoefficientsQ11 (coefficientAddQ11 xs ys) =
      polynomialOfCoefficientsQ11 xs + polynomialOfCoefficientsQ11 ys := by
  induction xs generalizing ys with
  | nil => simp [coefficientAddQ11]
  | cons x xs ih =>
    cases ys with
    | nil => simp [coefficientAddQ11]
    | cons y ys => simp [coefficientAddQ11, ih]; ring

theorem polynomialOfCoefficientsQ11_scale (c : ℚ) (xs : List ℚ) :
    polynomialOfCoefficientsQ11 (coefficientScaleQ11 c xs) =
      C c * polynomialOfCoefficientsQ11 xs := by
  induction xs with
  | nil => simp [coefficientScaleQ11]
  | cons x xs ih =>
    change C (c * x) + X *
        polynomialOfCoefficientsQ11 (coefficientScaleQ11 c xs) = _
    rw [ih]
    simp
    ring

theorem polynomialOfCoefficientsQ11_mul (xs ys : List ℚ) :
    polynomialOfCoefficientsQ11 (coefficientMulQ11 xs ys) =
      polynomialOfCoefficientsQ11 xs * polynomialOfCoefficientsQ11 ys := by
  induction xs generalizing ys with
  | nil => simp [coefficientMulQ11]
  | cons x xs ih =>
    cases ys with
    | nil => simp [coefficientMulQ11]
    | cons y ys =>
      simp [coefficientMulQ11, polynomialOfCoefficientsQ11_add,
        polynomialOfCoefficientsQ11_scale, ih]
      ring

theorem polynomialOfCoefficientsQ11_pow (xs : List ℚ) (n : ℕ) :
    polynomialOfCoefficientsQ11 (coefficientPowQ11 xs n) =
      polynomialOfCoefficientsQ11 xs ^ n := by
  induction n with
  | zero => simp [coefficientPowQ11]
  | succ n ih =>
    simp [coefficientPowQ11, polynomialOfCoefficientsQ11_mul, ih, pow_succ]
    ring

theorem polynomialOfCoefficientsQ11_affine (cs : List ℚ) (a d : ℚ) :
    polynomialOfCoefficientsQ11 (coefficientAffineQ11 cs a d) =
      (polynomialOfCoefficientsQ11 cs).comp (C a + C d * X) := by
  induction cs with
  | nil => simp [coefficientAffineQ11]
  | cons c cs ih =>
    simp [coefficientAffineQ11, polynomialOfCoefficientsQ11_add,
      polynomialOfCoefficientsQ11_mul, ih]

theorem polynomialOfCoefficientsQ11_bernsteinBasis (n i : ℕ) :
    polynomialOfCoefficientsQ11 (coefficientBernsteinBasisQ11 n i) =
      bernsteinPolynomial ℚ n i := by
  simp [coefficientBernsteinBasisQ11, polynomialOfCoefficientsQ11_scale,
    polynomialOfCoefficientsQ11_mul, polynomialOfCoefficientsQ11_pow,
    bernsteinPolynomial]
  ring

theorem polynomialOfCoefficientsQ11_bernsteinCombination
    (n i : ℕ) (cs : List ℚ) :
    polynomialOfCoefficientsQ11
        (coefficientBernsteinCombinationQ11 n i cs) =
      bernsteinCombinationQ11 n i cs := by
  induction cs generalizing i with
  | nil => simp [coefficientBernsteinCombinationQ11, bernsteinCombinationQ11]
  | cons c cs ih =>
    simp [coefficientBernsteinCombinationQ11, bernsteinCombinationQ11,
      polynomialOfCoefficientsQ11_add,
      polynomialOfCoefficientsQ11_scale,
      polynomialOfCoefficientsQ11_bernsteinBasis, ih]

theorem r102LowerBernsteinCoeffs11_length :
    r102LowerBernsteinCoeffs11.length = 52 := by native_decide

theorem r102UpperBernsteinCoeffs11_length :
    r102UpperBernsteinCoeffs11.length = 52 := by native_decide

theorem r102LowerBernsteinCoeffs11_pos :
    ∀ i < r102LowerBernsteinCoeffs11.length,
      0 < r102LowerBernsteinCoeffs11[i]! := by native_decide

theorem r102UpperBernsteinCoeffs11_pos :
    ∀ i < r102UpperBernsteinCoeffs11.length,
      0 < r102UpperBernsteinCoeffs11[i]! := by native_decide

def r102SquaredYQ11 : ℚ[X] :=
  polynomialOfCoefficientsQ11
    (r102SquaredCoeffs11.map (fun c => (c : ℚ)))

/-- Executable coefficient replay for the lower affine half. -/
theorem r102_lower_bernstein_coefficients_exact11 :
    coefficientAffineQ11
        (r102SquaredCoeffs11.map (fun c => (c : ℚ))) 0 (1 / 2) =
      coefficientBernsteinCombinationQ11 51 0
        r102LowerBernsteinCoeffs11 := by native_decide

/-- Executable coefficient replay for the upper affine half. -/
theorem r102_upper_bernstein_coefficients_exact11 :
    coefficientAffineQ11
        (r102SquaredCoeffs11.map (fun c => (c : ℚ))) (1 / 2) (1 / 2) =
      coefficientBernsteinCombinationQ11 51 0
        r102UpperBernsteinCoeffs11 := by native_decide

/-- Exact Bernstein identity after substituting `y = t/2`. -/
theorem r102_lower_bernstein_identity11 :
    r102SquaredYQ11.comp (C (1 / 2) * X) =
      bernsteinCombinationQ11 51 0 r102LowerBernsteinCoeffs11 := by
  let cs := r102SquaredCoeffs11.map (fun c => (c : ℚ))
  have hAffine :
      polynomialOfCoefficientsQ11 (coefficientAffineQ11 cs 0 (1 / 2)) =
        (polynomialOfCoefficientsQ11 cs).comp (C (1 / 2) * X) := by
    simpa using polynomialOfCoefficientsQ11_affine cs 0 (1 / 2)
  change (polynomialOfCoefficientsQ11 cs).comp (C (1 / 2) * X) = _
  rw [← hAffine,
    ← polynomialOfCoefficientsQ11_bernsteinCombination]
  change polynomialOfCoefficientsQ11
      (coefficientAffineQ11
        (r102SquaredCoeffs11.map (fun c => (c : ℚ))) 0 (1 / 2)) = _
  exact congrArg polynomialOfCoefficientsQ11
    r102_lower_bernstein_coefficients_exact11

/-- Exact Bernstein identity after substituting `y = (1+t)/2`. -/
theorem r102_upper_bernstein_identity11 :
    r102SquaredYQ11.comp (C (1 / 2) + C (1 / 2) * X) =
      bernsteinCombinationQ11 51 0 r102UpperBernsteinCoeffs11 := by
  change (polynomialOfCoefficientsQ11
      (r102SquaredCoeffs11.map (fun c => (c : ℚ)))).comp
        (C (1 / 2) + C (1 / 2) * X) = _
  rw [← polynomialOfCoefficientsQ11_affine,
    ← polynomialOfCoefficientsQ11_bernsteinCombination]
  exact congrArg polynomialOfCoefficientsQ11
    r102_upper_bernstein_coefficients_exact11

/-- Mapping a Horner coefficient list from the integers to the rationals is
the same as mapping the list first. -/
theorem polynomialOfCoefficientsZ_map_Q11 (cs : List ℤ) :
    (polynomialOfCoefficientsZ cs).map (Int.castRingHom ℚ) =
      polynomialOfCoefficientsQ11 (cs.map (fun c => (c : ℚ))) := by
  induction cs with
  | nil => simp [polynomialOfCoefficientsZ, polynomialOfCoefficientsQ11]
  | cons c cs ih =>
    change (C c + X * polynomialOfCoefficientsZ cs).map _ =
      C (c : ℚ) + X *
        polynomialOfCoefficientsQ11 (cs.map fun c => (c : ℚ))
    rw [Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul,
      Polynomial.map_X, ih]
    simp

/-- The rational polynomial port agrees with the integral coefficient data. -/
theorem r102SquaredYQ11_eq_map_integer :
    r102SquaredYQ11 = r102SquaredY11.map (Int.castRingHom ℚ) := by
  exact (polynomialOfCoefficientsZ_map_Q11 r102SquaredCoeffs11).symm

/-- A Bernstein combination with nonnegative coefficients is nonnegative on
the unit interval. -/
theorem bernsteinCombinationQ11_eval_nonneg
    (n i : ℕ) (cs : List ℚ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcs : ∀ c ∈ cs, 0 ≤ c) :
    0 ≤ ((bernsteinCombinationQ11 n i cs).map
      (algebraMap ℚ ℝ)).eval t := by
  induction cs generalizing i with
  | nil => simp [bernsteinCombinationQ11.eq_def]
  | cons c cs ih =>
    rw [bernsteinCombinationQ11.eq_def]
    rw [Polynomial.map_add, Polynomial.eval_add,
      Polynomial.map_mul, Polynomial.eval_mul]
    simp only [Polynomial.map_C, Polynomial.eval_C,
      bernsteinPolynomial.map]
    apply add_nonneg
    · apply mul_nonneg
      · change 0 ≤ (c : ℝ)
        exact Rat.cast_nonneg.mpr (hcs c (by simp))
      · simp only [bernsteinPolynomial, Polynomial.eval_mul,
          Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_sub, Polynomial.eval_one]
        positivity
    · apply ih
      intro x hx
      exact hcs x (by simp [hx])

/-- If the zeroth Bernstein coefficient is positive, the combination is
strictly positive on `[0,1)`. -/
theorem bernsteinCombinationQ11_eval_pos_at_zero_index
    (n : ℕ) (c : ℚ) (cs : List ℚ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hc : 0 < c)
    (hcs : ∀ x ∈ cs, 0 ≤ x) :
    0 < ((bernsteinCombinationQ11 n 0 (c :: cs)).map
      (algebraMap ℚ ℝ)).eval t := by
  rw [bernsteinCombinationQ11.eq_def]
  rw [Polynomial.map_add, Polynomial.eval_add,
    Polynomial.map_mul, Polynomial.eval_mul]
  simp only [Polynomial.map_C, Polynomial.eval_C,
    bernsteinPolynomial.map]
  apply add_pos_of_pos_of_nonneg
  · apply mul_pos
    · change 0 < (c : ℝ)
      exact Rat.cast_pos.mpr hc
    · simp only [bernsteinPolynomial, Nat.choose_zero_right, Nat.cast_one,
        Polynomial.eval_one, one_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub, pow_zero, Nat.sub_zero]
      exact pow_pos (sub_pos.mpr ht1) n
  · exact bernsteinCombinationQ11_eval_nonneg n 1 cs t ht0 ht1.le hcs

def r102SquaredYR11 : ℝ[X] :=
  r102SquaredYQ11.map (algebraMap ℚ ℝ)

theorem r102SquaredYR11_pos_lower (y : ℝ)
    (hy0 : 0 ≤ y) (hyhalf : y < 1 / 2) :
    0 < r102SquaredYR11.eval y := by
  let t : ℝ := 2 * y
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t < 1 := by dsimp [t]; linarith
  have htail : ∀ x ∈ r102LowerBernsteinCoeffs11.tail, 0 ≤ x := by
    intro x hx
    have hmem : x ∈ r102LowerBernsteinCoeffs11 := List.mem_of_mem_tail hx
    have hp : ∀ x ∈ r102LowerBernsteinCoeffs11, 0 < x := by native_decide
    exact (hp x hmem).le
  have hpos := bernsteinCombinationQ11_eval_pos_at_zero_index
    51 (r102LowerBernsteinCoeffs11[0]!)
      r102LowerBernsteinCoeffs11.tail t ht0 ht1 (by native_decide) htail
  have hlist : (r102LowerBernsteinCoeffs11[0]!) ::
      r102LowerBernsteinCoeffs11.tail = r102LowerBernsteinCoeffs11 := by
    native_decide
  rw [hlist] at hpos
  have hidR := congrArg (Polynomial.map (algebraMap ℚ ℝ))
    r102_lower_bernstein_identity11
  have heval := congrArg (fun p : ℝ[X] => p.eval t) hidR
  simp only [Polynomial.map_comp, Polynomial.eval_comp] at heval
  rw [← heval] at hpos
  have harg : ((C (1 / 2) * X : ℚ[X]).map
      (algebraMap ℚ ℝ)).eval t = y := by
    dsimp [t]
    norm_num
    ring
  rw [harg] at hpos
  exact hpos

theorem r102SquaredYR11_pos_upper (y : ℝ)
    (hyhalf : 1 / 2 ≤ y) (hy1 : y < 1) :
    0 < r102SquaredYR11.eval y := by
  let t : ℝ := 2 * y - 1
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have htail : ∀ x ∈ r102UpperBernsteinCoeffs11.tail, 0 ≤ x := by
    intro x hx
    have hmem : x ∈ r102UpperBernsteinCoeffs11 := List.mem_of_mem_tail hx
    have hp : ∀ x ∈ r102UpperBernsteinCoeffs11, 0 < x := by native_decide
    exact (hp x hmem).le
  have hpos := bernsteinCombinationQ11_eval_pos_at_zero_index
    51 (r102UpperBernsteinCoeffs11[0]!)
      r102UpperBernsteinCoeffs11.tail t ht0 ht1 (by native_decide) htail
  have hlist : (r102UpperBernsteinCoeffs11[0]!) ::
      r102UpperBernsteinCoeffs11.tail = r102UpperBernsteinCoeffs11 := by
    native_decide
  rw [hlist] at hpos
  have hidR := congrArg (Polynomial.map (algebraMap ℚ ℝ))
    r102_upper_bernstein_identity11
  have heval := congrArg (fun p : ℝ[X] => p.eval t) hidR
  simp only [Polynomial.map_comp, Polynomial.eval_comp] at heval
  rw [← heval] at hpos
  have harg : ((C (1 / 2) + C (1 / 2) * X : ℚ[X]).map
      (algebraMap ℚ ℝ)).eval t = y := by
    dsimp [t]
    norm_num
    ring
  rw [harg] at hpos
  exact hpos

theorem r102SquaredYR11_eval_one_pos :
    0 < r102SquaredYR11.eval 1 := by
  norm_num [r102SquaredYR11, r102SquaredYQ11,
    polynomialOfCoefficientsQ11, r102SquaredCoeffs11]

/-- The cofactor in `y` is positive on the entire interval relevant to a
circle coordinate. -/
theorem r102SquaredYR11_pos_of_mem_Icc (y : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < r102SquaredYR11.eval y := by
  by_cases hyhalf : y < 1 / 2
  · exact r102SquaredYR11_pos_lower y hy0 hyhalf
  · by_cases hyeq : y = 1
    · simpa [hyeq] using r102SquaredYR11_eval_one_pos
    · exact r102SquaredYR11_pos_upper y (le_of_not_gt hyhalf)
        (lt_of_le_of_ne hy1 hyeq)

def r102KQ11 : ℚ[X] := r102SquaredYQ11.comp (X ^ 2)
def r102KR11 : ℝ[X] := r102KQ11.map (algebraMap ℚ ℝ)

theorem r102KR11_eval (k : ℝ) :
    r102KR11.eval k = r102SquaredYR11.eval (k ^ 2) := by
  simp [r102KR11, r102KQ11, r102SquaredYR11, Polynomial.map_comp,
    Polynomial.eval_comp]

/-- The degree-102 cofactor cannot vanish at a real circle coordinate. -/
theorem r102KR11_pos_of_abs_le_one (k : ℝ) (hk : |k| ≤ 1) :
    0 < r102KR11.eval k := by
  rw [r102KR11_eval]
  apply r102SquaredYR11_pos_of_mem_Icc
  · positivity
  · exact (sq_le_one_iff_abs_le_one k).mpr hk

theorem r102KR11_not_isRoot_of_abs_le_one (k : ℝ) (hk : |k| ≤ 1) :
    ¬r102KR11.IsRoot k := by
  rw [Polynomial.IsRoot]
  exact ne_of_gt (r102KR11_pos_of_abs_le_one k hk)

end


end Biunimodular.F11
