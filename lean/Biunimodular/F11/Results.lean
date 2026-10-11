/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252ComplexPhaseEliminationIdeal
import Biunimodular.F11.GaussianG10Irreducibility
import Biunimodular.F11.ASectorQ60Irreducibility
import Biunimodular.F11.BSectorQ80OriginalIrreducibility
import Biunimodular.F11.R102GlobalPositive
import Biunimodular.F11.H252DegreeEven
import Biunimodular.F11.H252ComplexRootCount
import Biunimodular.F11.PhaseGramExactRank11
import Biunimodular.F11.Even11FourierEigenspaces
import Biunimodular.F11.CoordinateEliminantAssembly
import Biunimodular.F11.HomogeneousRegularCertificates
import Biunimodular.F11.Even11HomogeneousRegularSequence
import Biunimodular.F11.H252ComplexPhaseDistinctPoints
import Biunimodular.F11.Conductor77CharacterPeriod
import Biunimodular.F11.Conductor77KernelDilation
import Biunimodular.F11.Conductor77CharacterPowers
import Biunimodular.F11.ArithmeticTheoremAssembly
import Biunimodular.F11.ASectorPhysicalFactorBoxes11
import Biunimodular.F11.ASectorF30PhysicalPolynomialBridge11
import Biunimodular.F11.ASectorPhysicalInvariantBoxes11
import Biunimodular.F11.ASectorPhysicalOrbitCoordinate11
import Biunimodular.F11.ASectorAnalyticEmbedding77
import Biunimodular.F11.ASectorPhysicalAnalyticConjugacy77
import Biunimodular.F11.ASectorAnalyticCoordinateDistinct77
import Biunimodular.F11.ASectorPhysicalCoordinateDistinct11
import Biunimodular.F11.ASectorPhysicalRootCoverage11
import Biunimodular.F11.ASectorPhysicalRootCount11
import Biunimodular.F11.ASectorPhysicalAnalyticClassification77
import Biunimodular.F11.ASectorPeriodSubfieldValues77
import Biunimodular.F11.ASectorPeriodSubfieldDegrees77
import Biunimodular.F11.ASectorPeriodCyclicGalois77
import Biunimodular.F11.ASectorPeriodIntegerOrder77
import Biunimodular.F11.ASectorCubicRealSubfield77
import Biunimodular.F11.ASectorPeriodTraceDenominator77
import Biunimodular.F11.ASectorPeriodMaximalOrder77
import Biunimodular.F11.ASectorAnalyticQuadraticSign77
import Biunimodular.F11.BjorckEvenExclusion11
import Biunimodular.F11.BSectorRealRootCount11
import Biunimodular.F11.DegreeEight875CertificateData
import Biunimodular.F11.Even11FourierLift
import Biunimodular.F11.Even11FourierPhaseAction11
import Biunimodular.F11.Even11FixedSliceFourierQuotient
import Biunimodular.F11.Even11FixedSliceGeometryCertificate
import Biunimodular.F11.Even11FixedSliceQuotientGeometry
import Biunimodular.F11.Even11FixedSliceTrace
import Biunimodular.F11.FixedSliceQuotientCoordinateAlgebra
import Biunimodular.F11.FixedSliceTraceCoordinateAlgebra
import Biunimodular.F11.FixedSliceSchemeCoordinateAlgebra
import Biunimodular.F11.FixedSliceFiveCoordinateAlgebra
import Biunimodular.F11.FixedSliceNormalizedAffineChart
import Biunimodular.F11.FixedSliceRegularPresentation
import Biunimodular.F11.FixedSliceHomogeneousIdeal
import Biunimodular.F11.FixedSliceProjectiveChart
import Biunimodular.F11.FixedSliceProjectiveChartAlgebra
import Biunimodular.F11.FixedSliceProjectiveSchemeProperties
import Biunimodular.F11.FixedSliceFiveQuadricJacobian
import Biunimodular.F11.FixedSliceInvariantCharacteristicPolynomial
import Biunimodular.F11.FixedSliceCoordinateAlgebraPoints
import Biunimodular.F11.SplitPolynomialFunctionAlgebra
import Biunimodular.F11.Even11FixedSliceExplicitPoints
import Biunimodular.F11.Even11PrincipalMinorBridge
import Biunimodular.F11.Even11PrincipalMinorCertificate
import Biunimodular.F11.PhaseGramFixedSliceBridge11
import Biunimodular.F11.PhaseGramSpectrumReduction11
import Biunimodular.F11.PhaseGramIntrinsic11
import Biunimodular.F11.PhaseClassification11
import Biunimodular.F11.FixedSliceGeometryAssembly
import Biunimodular.F11.FullSymmetryClassification11

set_option autoImplicit false

namespace Biunimodular.F11.Results

/-!
# Exact results at prime 11

This module collects fixed-slice geometry, Gram moduli, coordinate elimination,
conductor-77 arithmetic, and the concrete Fourier symmetry classification.
The classification, complex scheme, character cutout, and RUR parametrization
also have dedicated result modules. Public summaries live in
`Biunimodular.F11.Results`; the underlying object-level lemmas remain in
`Biunimodular.F11`.
-/

/-- The concrete homogeneous equations have degree two, and their normalized
affine chart is the reduced degree-32 coordinate algebra. -/
theorem fixedSliceHomogeneous_chart :
    even11FixedSliceHomogeneousGenerators.length = 5 ∧
      (∀ p ∈ even11FixedSliceHomogeneousGenerators, p.totalDegree = 2) ∧
      Module.finrank ℂ FixedSliceNormalizedAffineChartAlgebra = 32 ∧
      IsReduced FixedSliceNormalizedAffineChartAlgebra := by
  exact ⟨even11FixedSliceHomogeneousGenerators_length,
    even11FixedSliceHomogeneousGenerators_totalDegree,
    fixedSliceNormalizedAffineChart_finrank, inferInstance⟩

/-- Scheme-level boundary exclusion: every relevant prime over the actual
homogeneous Fourier equations lies in the zero-th-coordinate chart. -/
theorem fixedSliceHomogeneous_prime_chart
    (P : Ideal (MvPolynomial (Fin 6) ℂ)) (hP : P.IsPrime)
    (heq : ∀ j : Fin 6, fixedSliceHomogeneousQuadric even11FourierNormalized j ∈ P)
    (hrelevant : ∃ j : Fin 6, (MvPolynomial.X j : MvPolynomial (Fin 6) ℂ) ∉ P) :
    (MvPolynomial.X 0 : MvPolynomial (Fin 6) ℂ) ∉ P :=
  even11FixedSliceHomogeneous_prime_chart P hP heq hrelevant

/-- Every algebraic integer has denominator bounded by the computed period
order discriminant. -/
theorem period_integer_denominator {x : conductor77PeriodField}
    (hx : IsIntegral ℤ x) : (7^5 * 11^3 : ℚ) • x ∈ periodIntegerSpan77 :=
  periodIntegerSpan77_discriminant_smul_mem hx

/-- The integer period span is the full ring of integers, and its basis
discriminant is the actual sextic number-field discriminant. -/
theorem conductor77_integer_order_and_discriminant :
    (∀ x : conductor77PeriodField, IsIntegral ℤ x ↔ x ∈ periodIntegerSpan77) ∧
      NumberField.discr conductor77PeriodField = (7^5 * 11^3 : ℤ) :=
  ⟨periodIntegerSpan77_integral_iff, conductor77PeriodField_discr⟩

/-- The actual affine chart is zero-dimensional and has a regular
hypersurface presentation. -/
theorem fixedSlice_chart_regular_presentation :
    ringKrullDim FixedSliceNormalizedAffineChartAlgebra = 0 ∧
      ∃ p : Polynomial ℂ, RingTheory.Sequence.IsRegular (Polynomial ℂ) [p] ∧
        Nonempty (FixedSliceNormalizedAffineChartAlgebra ≃ₐ[ℂ]
          (Polynomial ℂ ⧸ Ideal.span {p})) :=
  ⟨fixedSliceNormalizedAffineChart_krullDimension,
    fixedSliceNormalizedAffineChart_regular_presentation⟩

/-- Imposing the actual homogeneous equations in the degree-zero projective
chart localization gives the reduced etale algebra of degree 32. -/
theorem fixedSlice_projective_chart_algebra :
    Module.finrank ℂ FixedSliceProjectiveChartAlgebra = 32 ∧
      IsReduced FixedSliceProjectiveChartAlgebra ∧
      Algebra.Etale ℂ FixedSliceProjectiveChartAlgebra :=
  ⟨fixedSliceProjectiveChart_finrank, inferInstance, inferInstance⟩

/-- The actual projective fixed slice is a closed reduced scheme, finite
etale over the complex numbers, with exactly 32 projective primes. -/
theorem fixedSlice_projective_scheme :
    AlgebraicGeometry.IsClosedImmersion fixedSliceProjectiveSchemeι ∧
      AlgebraicGeometry.IsFinite fixedSliceProjectiveSchemeToComplex ∧
      AlgebraicGeometry.Etale fixedSliceProjectiveSchemeToComplex ∧
      AlgebraicGeometry.IsReduced fixedSliceProjectiveScheme ∧
      Nat.card fixedSliceProjectiveZeroLocus = 32 ∧
      ringKrullDim FixedSliceProjectiveChartAlgebra = 0 :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    fixedSliceProjectiveZeroLocus_card, fixedSliceProjectiveChart_krullDimension⟩

/-- The original five quadrics, in the chart covering the entire projective
zero locus, give a nonsingular square presentation. -/
theorem fixedSlice_original_five_quadric_jacobian :
    IsUnit fixedSliceFiveQuadricPrePresentation.jacobian ∧
      (∀ i : Fin 5, fixedSliceFiveQuadricSubmersivePresentation.relation i =
        fixedSliceHomogeneousAffineMap
          (fixedSliceHomogeneousQuadric even11FourierNormalized i.succ)) :=
  ⟨fixedSliceFiveQuadricJacobian_isUnit,
    fixedSliceFiveQuadricSubmersivePresentation_relations⟩

/-- A compact compilation seam exposing the exact finite cardinality data used
by the classification proof. -/
theorem fixedSlice_numeric_data :
    Fintype.card FixedSliceQuotientRoot = 16 ∧
    Fintype.card SplitQuotientRoot = 8 ∧
    Fintype.card NonGaussianSplitQuotientRoot = 7 := by
  exact ⟨fixedSliceQuotientRoot_card, splitQuotientRoot_card,
    nonGaussianSplitQuotientRoot_card⟩

/-- The rational invariant algebra and its complexification both have
dimension sixteen and contain no nonzero nilpotents. -/
theorem fixedSlice_invariant_algebras_reduced :
    Module.finrank ℚ FixedSliceQuotientCoordinateAlgebra = 16 ∧
    IsReduced FixedSliceQuotientCoordinateAlgebra ∧
    Module.finrank ℂ FixedSliceQuotientComplexCoordinateAlgebra = 16 ∧
    IsReduced FixedSliceQuotientComplexCoordinateAlgebra := by
  exact ⟨fixedSliceQuotientCoordinateAlgebra_finrank, inferInstance,
    fixedSliceQuotientComplexCoordinateAlgebra_finrank, inferInstance⟩

/-- The thirty-two-point trace algebra is also reduced over the rationals
and over the complex numbers. -/
theorem fixedSlice_trace_algebras_reduced :
    Module.finrank ℚ FixedSliceTraceCoordinateAlgebra = 32 ∧
    IsReduced FixedSliceTraceCoordinateAlgebra ∧
    Module.finrank ℂ FixedSliceTraceComplexCoordinateAlgebra = 32 ∧
    IsReduced FixedSliceTraceComplexCoordinateAlgebra := by
  exact ⟨fixedSliceTraceCoordinateAlgebra_finrank, inferInstance,
    fixedSliceTraceComplexCoordinateAlgebra_finrank, inferInstance⟩

/-- The original multivariate affine fixed-slice ideal is radical, and its
actual coordinate ring is a reduced complex algebra of dimension thirty-two. -/
theorem fixedSlice_scheme_algebra_reduced :
    Module.finrank ℂ FixedSliceSchemeCoordinateAlgebra = 32 ∧
      IsReduced FixedSliceSchemeCoordinateAlgebra ∧
      (fixedSliceSparseIdeal fixedSliceOriginalSystem).IsRadical := by
  exact ⟨fixedSliceSchemeCoordinateAlgebra_finrank, inferInstance,
    fixedSliceOriginalIdeal_isRadical⟩

/-- The trace-free coordinate ring of the original five affine quadrics is
reduced and has dimension thirty-two. -/
theorem fixedSlice_five_algebra_reduced :
    Module.finrank ℂ FixedSliceFiveCoordinateAlgebra = 32 ∧
      IsReduced FixedSliceFiveCoordinateAlgebra ∧
      (RedundantCoordinate.baseIdeal fixedSliceFiveGenerators).IsRadical :=
  ⟨fixedSliceFiveCoordinateAlgebra_finrank, inferInstance, fixedSliceFiveIdeal_isRadical⟩

/-- The explicit Gaussian-period quadratic and cubic relations hold in the
conductor-77 field itself. -/
theorem conductor77_period_subfield_relations :
    periodQuadraticGenerator77 ^ 2 = 77 ∧
      periodCubicGenerator77 ^ 3 - periodCubicGenerator77 ^ 2 -
        2 * periodCubicGenerator77 + 1 = 0 :=
  ⟨periodQuadraticGenerator77_square, periodCubicGenerator77_relation⟩

/-- The explicit period sums generate quadratic and cubic subfields, and
their compositum is exactly the sextic Gaussian-period field. -/
theorem conductor77_period_subfields :
    Module.finrank ℚ conductor77QuadraticSubfield = 2 ∧
      Module.finrank ℚ conductor77CubicSubfield = 3 ∧
      conductor77PeriodField = conductor77QuadraticSubfield ⊔ conductor77CubicSubfield :=
  ⟨conductor77QuadraticSubfield_finrank, conductor77CubicSubfield_finrank,
    conductor77PeriodField_eq_quadratic_sup_cubic⟩

/-- The actual Gaussian periods form a rational basis with the displayed
discriminant. -/
theorem conductor77_period_basis_discriminant :
    Algebra.discr ℚ conductor77PeriodBasis = 7^5 * 11^3 :=
  conductor77PeriodBasis_discr

/-- The positive square-root sign in the period-half formula holds at the
specified analytic embedding. -/
theorem conductor77_quadratic_sign :
    conductor77AnalyticEmbedding periodQuadraticGenerator77 = (Real.sqrt 77 : ℂ) :=
  periodQuadraticGenerator77_analytic_sqrt

/-- The cubic period subfield is the real conductor-seven coordinate field. -/
theorem conductor77_cubic_real_subfield :
    conductor77CubicSubfield = conductor7RealSubfield77 :=
  conductor77CubicSubfield_eq_real7

/-- The concrete dilation/conjugation group has order ten and acts freely on
the normalized phase-solution locus.  Thus the tenfold multiplicity used by
normalized even classification is proved from the phase equations rather than supplied as
certificate data. -/
theorem phaseSolution11_symmetry :
    Fintype.card EvenSymmetry11 = 10 ∧
      ∀ s : PhaseSolution11,
        MulAction.stabilizer EvenSymmetry11 s = ⊥ := by
  refine ⟨evenSymmetry11_card, ?_⟩
  intro s
  exact IsCancelSMul.stabilizer_eq_bot s

/-- The physical invariant is constant on every normalized symmetry orbit and
lies in `[0, 1)` on every phase solution. -/
theorem phaseSolution11_invariant :
    (∀ g : EvenSymmetry11, ∀ s : PhaseSolution11,
      phaseInvariantU11 (g • s.1) = phaseInvariantU11 s.1) ∧
    (∀ s : PhaseSolution11,
      0 ≤ phaseInvariantU11 s.1 ∧ phaseInvariantU11 s.1 < 1) := by
  exact ⟨fun g s => phaseInvariantU11_smul g s.1,
    fun s => (phaseSolution11FixedSliceCertificateOfGram
      even11FixedSliceGeometryCertificate phaseGramSpectrumCertificate11).invariantU_mem_Ico s⟩

/-- The concrete physical quotient is the cyclic quotient of the real
rank-two Gram locus; this equivalence includes the converse reconstruction
up to simultaneous conjugation. -/
noncomputable def phaseSolution11GramModuliEquiv :
    PhaseSolution11Orbit ≃ PhaseGramOrbit11 :=
  phaseSolution11OrbitGramEquiv

/-- The intrinsic PSD matrix conditions are equivalent to being the Gram
matrix of a physical solution. This includes reconstruction from an arbitrary
matrix satisfying those conditions. -/
theorem phaseGramIntrinsic11_eq_range :
    Set.range phaseSolution11GramMap = phaseGramIntrinsicSet11 :=
  phaseGramLocus11_eq_intrinsic

/-- The physical quotient as the cyclic quotient of the intrinsic PSD locus. -/
noncomputable def phaseSolution11IntrinsicGramModuliEquiv :
    PhaseSolution11Orbit ≃ PhaseGramIntrinsicOrbit11 :=
  phaseSolution11OrbitIntrinsicGramEquiv

theorem phaseSolution11IntrinsicGramModuliEquiv_value (q : PhaseSolution11Orbit) :
    phaseGramIntrinsicOrbitInvariantU11
        (phaseSolution11IntrinsicGramModuliEquiv q) =
      phaseSolution11OrbitInvariantU q :=
  phaseSolution11OrbitIntrinsicGramEquiv_value q

/-- Every point in the concrete Gram image has the advertised symmetry,
positivity, diagonal, rank, and five linear relations. -/
theorem phaseGramLocus11_geometry (K : PhaseGramLocus11) :
    K.1.IsSymm ∧ K.1.PosSemidef ∧
      (∀ i, K.1 i i = 2) ∧ K.1.rank = 2 ∧
      PhaseGramLinearRelations11 K.1 :=
  Biunimodular.F11.phaseGramLocus11_geometry K

/-- On the unit torus, the Gram linear relations recover exactly the five
physical phase equations. -/
theorem phaseGramMatrix11_relations_iff
    (x : PhaseCoords11) (hc : x.CircleEquations) :
    PhaseGramLinearRelations11 (phaseGramMatrix11 x) ↔
      x.IsPhaseSolution :=
  phaseGramMatrix11_linearRelations_iff x hc

/-- The Gram-moduli equivalence preserves the invariant, whose matrix formula
is `u = σ(K)² / 11`. -/
theorem phaseSolution11GramModuliEquiv_value
    (q : PhaseSolution11Orbit) :
    phaseGramOrbitInvariantU11 (phaseSolution11GramModuliEquiv q) =
      phaseSolution11OrbitInvariantU q :=
  phaseSolution11OrbitGramEquiv_value q

/-- The concrete Gram spectrum: necessity, orbit separation, and realization
of every admissible invariant root. -/
theorem phaseGramSpectrum :
    PhaseGramSpectrumCertificate :=
  phaseGramSpectrumCertificate11

/-- The independent physical bridge itself: after quotienting phases by
dilation and conjugation, their Gram moduli are identified with the split
part of the concrete fixed-slice quotient. -/
noncomputable def phaseSolution11FixedSliceEquiv :
    PhaseSolution11Orbit ≃
      Even11PhysicalFixedSliceQuotient even11FixedSliceGeometryCertificate :=
  phaseSolution11FixedSliceQuotientEquiv
    even11FixedSliceGeometryCertificate phaseGramSpectrumCertificate11

/-- The physical bridge preserves the common quotient coordinate. -/
theorem phaseSolution11FixedSliceEquiv_value
    (q : PhaseSolution11Orbit) :
    even11FixedSliceQuotientU
        (phaseSolution11FixedSliceEquiv q).1 =
      (phaseSolution11OrbitInvariantU q : ℂ) :=
  phaseSolution11FixedSliceQuotientEquiv_value
    even11FixedSliceGeometryCertificate phaseGramSpectrumCertificate11 q

/-- The result collection uses the concrete normalized order-11 Fourier
operator; it is involutive and defines the same projective slice as the exact
unnormalised DFT matrix. -/
theorem even11_fourier_model :
    (∀ h : Even6 ℂ,
      even11FourierNormalized (even11FourierNormalized h) = h) ∧
    (∀ h : Even6 ℂ,
      FixedSliceEq even11FourierNormalized h ↔ FixedSliceEq even11Fourier h) := by
  exact ⟨even11FourierNormalized_sq, even11_fixedSliceEq_normalized_iff⟩

/-- The exact 63-row certificate eliminates the projective boundary of the
concrete order-11 fixed slice without importing the degree-150 eliminant. -/
theorem even11_fixedSlice_no_boundary
    {h : Even6 ℂ} (hnz : h ≠ 0) (hh : FixedSliceEq even11Fourier h) :
    fourierCoordProduct even11Fourier h 0 ≠ 0 :=
  even11_fixedSlice_common_ne_zero_certified hnz hh

/-- Normalized version of the unconditional no-boundary theorem, matching
the involutive operator used by the quotient invariant. -/
theorem even11_normalized_fixedSlice_no_boundary
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hh : FixedSliceEq even11FourierNormalized h) :
    fourierCoordProduct even11FourierNormalized h 0 ≠ 0 :=
  even11_normalized_fixedSlice_common_ne_zero_certified hnz hh

/-- On the normalized concrete fixed slice, the homogeneous quotient equation
is equivalent to its unique affine value.  This packages the exact no-boundary
certificate directly into the quotient-invariant layer. -/
theorem even11_normalized_fixedSlice_quotient
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hh : FixedSliceEq even11FourierNormalized h) {u : ℂ} :
    fixedSliceUEquation even11FourierNormalized h u ↔
      u = fixedSliceUValue even11FourierNormalized h :=
  even11_normalized_fixedSliceUEquation_iff hnz hh

/-- The complete, unconditional concrete fixed-slice geometry certificate.
Its proof checks the exact degree-32 trace shape and reconstructs every affine
coordinate from the trace; the projective boundary is excluded separately. -/
theorem even11_fixedSlice_geometry :
    Even11FixedSliceGeometryCertificate :=
  even11FixedSliceGeometryCertificate

/-- The normalized Fourier involution acts freely on the concrete projective
fixed slice and therefore exhibits it as a two-sheeted cover of its orbit
quotient. -/
noncomputable def even11FixedSliceTwoSheetedEquiv :
    Even11FixedSlicePoint ≃ Even11FixedSliceFourierQuotient × Bool :=
  even11FixedSliceTwoSheeted

/-- The concrete projective invariant `u=q²`, descended through the free
Fourier orbit quotient. -/
noncomputable def even11FixedSliceQuotientU :
    Even11FixedSliceFourierQuotient → ℂ :=
  Biunimodular.F11.even11FixedSliceQuotientU

/-- The concrete quotient is identified with the degree-sixteen root space
by its actual `u=q²` value. -/
noncomputable def even11FixedSliceQuotientRootEquiv :
    Even11FixedSliceFourierQuotient ≃ FixedSliceQuotientRoot :=
  even11FixedSliceGeometryCertificate.quotientRootEquiv

/-- Unconditional `32/16/8/7` cardinality statement obtained from the exact
fixed-slice shape certificate. -/
theorem even11_fixedSlice_cardinality :
    Nat.card Even11FixedSlicePoint = 32 ∧
    Nat.card {p : Even11FixedSlicePoint // even11FixedSliceIsReal p} = 16 ∧
    Fintype.card SplitQuotientRoot = 8 ∧
    Fintype.card NonGaussianSplitQuotientRoot = 7 :=
  even11FixedSliceGeometryCertificate.cardinality_core

/-- real-locus criterion, derived from the concrete
Fourier-conjugate involutions and the separating quotient coordinate. -/
theorem even11_fixedSlice_real_iff_split
    (p : Even11FixedSlicePoint) :
    even11FixedSliceIsReal p ↔
      fixedSliceQuotientRootSplit
        (even11FixedSliceQuotientRootEquiv (Quotient.mk'' p)) :=
  even11FixedSliceGeometryCertificate.real_iff_split p

/-- The original ten-equation complex phase ideal has exactly the
H252 coordinate elimination ideal, and that generator is separable. -/
theorem full_complex_coordinate_eliminant :
    h252ComplexPhaseEliminationIdeal =
      Ideal.span ({h252K11.map (Int.castRingHom ℂ)} : Set (Polynomial ℂ)) ∧
      h252KComplex.Separable :=
  ⟨h252ComplexPhaseEliminationIdeal_eq_span, h252KComplex_separable⟩

/-- The degree-10, degree-60, and degree-80 factors of the real
degree-150 coordinate factor are irreducible over the rationals. The full
degree-252 eliminant also contains the degree-102 cofactor. -/
theorem coordinate_factors_irreducible :
    Irreducible p150G10KQ11 ∧ Irreducible p150Q60KQ11 ∧ Irreducible p150Q80KQ11 :=
  ⟨p150G10KQ11_irreducible, p150Q60KQ11_irreducible, p150Q80KQ11_irreducible⟩

theorem coordinate_eliminant_degree_and_parity :
    h252K11.natDegree = 252 ∧
      ∀ k : ℂ, h252KComplex.eval (-k) = h252KComplex.eval k :=
  ⟨h252K11_degree, h252KComplex_even⟩

theorem coordinate_cofactor_no_real_roots :
    ∀ k : ℝ, ¬r102KR11.IsRoot k := r102KR11_not_isRoot

theorem phaseGramIntrinsic11_exact_rank :
    ∀ K : PhaseGramIntrinsicLocus11, K.val.rank = 2 := phaseGramIntrinsic11_rank_two

theorem real_fourier_eigenspaces_dimension :
    Module.finrank ℝ Even11FourierRealPlus = 3 ∧
      Module.finrank ℝ Even11FourierRealMinus = 3 :=
  even11FourierReal_eigenspaces_dimension

theorem coordinate_factor_root_counts :
    Nat.card (CoordinatePhaseUnitRoot11 .g5) = 10 ∧
      Nat.card (CoordinatePhaseUnitRoot11 .f30) = 30 ∧
      Nat.card (CoordinatePhaseUnitRoot11 .f40) = 40 :=
  coordinatePhaseFactors11_root_counts

theorem coordinate_real_zero_sets (k : ℝ) :
    h252KR11.IsRoot k ↔ p150KR11.IsRoot k := h252KR11_isRoot_iff_real_factor k

theorem coordinate_factor_simple_roots :
    ∀ f : KFactor, (coordinatePhaseFactorR11 f).Separable :=
  coordinatePhaseFactorsR11_separable

theorem full_coordinate_complex_root_count :
  Nat.card (h252KComplex.rootSet ℂ) = 252 := h252KComplex_rootSet_card

/-- Last-component membership for the original finite syzygy export. -/
theorem homogeneous_syzygy_last_components (j : Fin 5) :
    ∀ p ∈ homogeneousRegularLastComponents j,
      homogeneousSparsePolynomial p ∈
        Ideal.ofList (even11FixedSliceHomogeneousGenerators.take j.val) :=
  homogeneousRegularCertificates_last_mem j

/-- The actual five normalized homogeneous Fourier quadrics form a regular
sequence in the six-variable complex polynomial ring. -/
theorem homogeneous_regular_sequence :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin 6) ℂ)
      even11FixedSliceHomogeneousGenerators :=
  even11FixedSliceHomogeneousGenerators_regular

/-- The 252 distinct coordinate roots lift to pairwise distinct points of
the original complexified ten-equation scheme. -/
theorem full_complex_distinct_points :
    ∃ f : Fin 252 → (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ), Function.Injective f :=
  h252ComplexPhase_has_252_distinct_points

/-- The explicit character controlling the period kernel is even, has order
six, and has conductor exactly 77. Its unit-group map is onto C6. -/
theorem conductor77_primitive_character :
    conductor77PrimitiveCharacter.conductor = 77 ∧
      orderOf conductor77PrimitiveCharacter = 6 ∧
      conductor77PrimitiveCharacter (-1) = 1 ∧
      Function.Surjective conductor77CharacterUnitHom :=
  ⟨conductor77PrimitiveCharacter_conductor, conductor77PrimitiveCharacter_order,
    conductor77PrimitiveCharacter_even, conductor77CharacterUnitHom_surjective⟩

/-- The actual sextic generator is the Gaussian period over the character
kernel; that kernel consists of the ten powers of 6 modulo 77. -/
theorem conductor77_character_period :
    (∀ a : ZMod 77, conductor77PrimitiveCharacter a = 1 ↔
      ∃ j : Fin 10, a = 6 ^ j.val) ∧
    periodEta77 = ∑ a : ZMod 77, if conductor77PrimitiveCharacter a = 1 then
      zeta77 ^ a.val else 0 :=
  ⟨conductor77PrimitiveCharacter_kernel_powers, periodEta77_character_kernel⟩

/-- The even character descends to the real unit quotient, with cyclic
kernel of order five and surjective quotient character of order six. -/
theorem conductor77_real_character_exact :
    Function.Surjective conductor77RealCharacter ∧
      Nat.card conductor77RealCharacter.ker = 5 ∧
      orderOf conductor77RealSix = 5 :=
  ⟨conductor77RealCharacter_surjective, conductor77RealCharacter_kernel_card,
    conductor77RealSix_order⟩

/-- Reduction modulo eleven is the actual isomorphism from the relative
character kernel to the length-eleven unit group modulo signs. -/
theorem conductor77_kernel_dilation : Function.Bijective conductor77KernelReduction11 :=
  ⟨conductor77KernelReduction11_injective, conductor77KernelReduction11_surjective⟩

/-- The cubic character is induced from conductor seven; the quadratic
character is primitive of conductor seventy-seven. -/
theorem conductor77_character_powers :
    orderOf (conductor77PrimitiveCharacter ^ 2) = 3 ∧
      (conductor77PrimitiveCharacter ^ 2).conductor = 7 ∧
      orderOf (conductor77PrimitiveCharacter ^ 3) = 2 ∧
      (conductor77PrimitiveCharacter ^ 3).conductor = 77 :=
  ⟨conductor77Character_square_order, conductor77Character_square_conductor,
    conductor77Character_cube_order, conductor77Character_cube_conductor⟩

end Biunimodular.F11.Results
