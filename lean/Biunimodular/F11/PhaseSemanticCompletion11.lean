/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PhaseFixedSliceExistence11
import Biunimodular.F11.Even11FixedSliceExplicitPoints

set_option autoImplicit false

namespace Biunimodular.F11

open ZMod AddChar

/-- Read the five independent complex values of a normalized even signal. -/
def phaseCoordsOfSignal11 (z : ZeroAutocorrSignal11) : PhaseCoords11 where
  a := (z.signal 1).re
  b := (z.signal 1).im
  c := (z.signal 2).re
  d := (z.signal 2).im
  e := (z.signal 3).re
  f := (z.signal 3).im
  g := (z.signal 4).re
  h := (z.signal 4).im
  j := (z.signal 5).re
  k := (z.signal 5).im

theorem phaseSignal11_phaseCoordsOfSignal11 (z : ZeroAutocorrSignal11) :
    phaseSignal11 (phaseCoordsOfSignal11 z) = z.signal := by
  funext t
  have h0 := z.normalized
  have h1 := z.even (1 : Fin 11)
  have h2 := z.even (2 : Fin 11)
  have h3 := z.even (3 : Fin 11)
  have h4 := z.even (4 : Fin 11)
  have h5 := z.even (5 : Fin 11)
  simp only [neg11] at h1 h2 h3 h4 h5
  fin_cases t <;>
    simp [phaseSignal11, phaseCoordsOfSignal11, phaseC_re_im,
      h0, ← h1, ← h2, ← h3, ← h4, ← h5]

theorem phaseCoordsOfSignal11_phaseSignal11 (x : PhaseCoords11)
    (hx : x.IsPhaseSolution) :
    phaseCoordsOfSignal11 (phaseSolutionToZeroAutocorrSignal11 x hx) = x := by
  cases x
  rfl

private theorem zeroAutocorrSignal11_ext {z w : ZeroAutocorrSignal11}
    (h : z.signal = w.signal) : z = w := by
  cases z with
  | mk f hn he hf hz =>
    cases w with
    | mk g gn ge gf gz =>
      cases h
      rfl

/-- The ten real phase equations describe exactly the normalized even
zero-autocorrelation signals. -/
def phaseSolutionSignalEquiv11 : PhaseSolution11 ≃ ZeroAutocorrSignal11 where
  toFun s := phaseSolutionToZeroAutocorrSignal11 s.1 s.2
  invFun z :=
    ⟨phaseCoordsOfSignal11 z,
      isPhaseSolution_of_normSq_autocorr11 (phaseCoordsOfSignal11 z)
        (by simpa only [phaseSignal11_phaseCoordsOfSignal11] using z.normSq_one)
        (by simpa only [phaseSignal11_phaseCoordsOfSignal11] using z.zero_autocorr)⟩
  left_inv s := by
    apply Subtype.ext
    exact phaseCoordsOfSignal11_phaseSignal11 s.1 s.2
  right_inv z := by
    apply zeroAutocorrSignal11_ext
    exact phaseSignal11_phaseCoordsOfSignal11 z

/-- The signal-level form of the exact F11 count. -/
theorem zeroAutocorrSignal11_card : Nat.card ZeroAutocorrSignal11 = 80 := by
  calc
    Nat.card ZeroAutocorrSignal11 = Nat.card PhaseSolution11 :=
      Nat.card_congr phaseSolutionSignalEquiv11.symm
    _ = 80 := phaseSolution11_classification_complete.2.1

/-- Coordinates of the normalized quadratic phase `t ↦ ψ(a t²)`. -/
noncomputable def gaussianCoords11 (a : ZMod 11) : PhaseCoords11 where
  a := (stdAddChar a).re
  b := (stdAddChar a).im
  c := (stdAddChar (4 * a)).re
  d := (stdAddChar (4 * a)).im
  e := (stdAddChar (9 * a)).re
  f := (stdAddChar (9 * a)).im
  g := (stdAddChar (5 * a)).re
  h := (stdAddChar (5 * a)).im
  j := (stdAddChar (3 * a)).re
  k := (stdAddChar (3 * a)).im

theorem phaseSignal11_gaussianCoords11 (a : ZMod 11) (t : Fin 11) :
    phaseSignal11 (gaussianCoords11 a) t =
      stdAddChar (a * (t.1 : ZMod 11) ^ 2) := by
  fin_cases t <;>
    simp [phaseSignal11, gaussianCoords11, phaseC_re_im] <;>
    congr 1 <;> native_decide +revert

private theorem phaseSignal11_injective : Function.Injective phaseSignal11 := by
  intro x y h
  have h1 := congrFun h (1 : Fin 11)
  have h2 := congrFun h (2 : Fin 11)
  have h3 := congrFun h (3 : Fin 11)
  have h4 := congrFun h (4 : Fin 11)
  have h5 := congrFun h (5 : Fin 11)
  cases x
  cases y
  simp only [phaseSignal11, phaseC] at h1 h2 h3 h4 h5
  simp_all

/-- A phase solution is quadratic Gaussian if its signal is a nonconstant
quadratic additive character. -/
def IsQuadraticGaussian11 (s : PhaseSolution11) : Prop :=
  ∃ a : ZMod 11, a ≠ 0 ∧
    ∀ t : Fin 11, phaseSignal11 s.1 t =
      stdAddChar (a * (t.1 : ZMod 11) ^ 2)

theorem isQuadraticGaussian11_iff_coords (s : PhaseSolution11) :
    IsQuadraticGaussian11 s ↔
      ∃ a : ZMod 11, a ≠ 0 ∧ s.1 = gaussianCoords11 a := by
  constructor
  · rintro ⟨a, ha, hs⟩
    refine ⟨a, ha, ?_⟩
    apply phaseSignal11_injective
    funext t
    rw [hs, phaseSignal11_gaussianCoords11]
  · rintro ⟨a, ha, hs⟩
    exact ⟨a, ha, by simpa [hs] using phaseSignal11_gaussianCoords11 a⟩

theorem even11GaussianBranchPoint_real :
    even11FixedSliceIsReal even11GaussianBranchPoint := by
  apply (even11FixedSliceGeometryCertificate.real_iff_u_interval
    even11GaussianBranchPoint).2
  simp [even11FixedSliceQuotientU_mk, even11GaussianBranchPoint_u]

/-- The concrete quadratic point, converted to a phase solution. -/
noncomputable def gaussianBasePhase11 : PhaseSolution11 :=
  ⟨phaseCoordsOfEven11 even11GaussianBranchPoint.1.rep,
    phaseCoordsOfEven11_isPhaseSolution even11GaussianBranchPoint
      even11GaussianBranchPoint_real⟩

theorem gaussianBasePhase11_u_zero :
    phaseInvariantU11 gaussianBasePhase11.1 = 0 := by
  have h := phaseInvariantU11_phaseCoordsOfEven11
    even11GaussianBranchPoint even11GaussianBranchPoint_real
  change (phaseInvariantU11 gaussianBasePhase11.1 : ℂ) =
    even11FixedSliceU even11GaussianBranchPoint at h
  rw [even11GaussianBranchPoint_u] at h
  exact_mod_cast h

theorem gaussianBasePhase11_coords :
    gaussianBasePhase11.1 = gaussianCoords11 5 := by
  let h : Even6 ℂ := even11GaussianBranchPoint.1.rep
  have hgauss : even11GaussianVector ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    norm_num [even11GaussianVector] at h0
  have hproj : Projectivization.mk ℂ h even11GaussianBranchPoint.1.rep_nonzero =
      Projectivization.mk ℂ even11GaussianVector hgauss := by
    rw [even11GaussianBranchPoint.1.mk_rep]
    rfl
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ h even11GaussianVector
      even11GaussianBranchPoint.1.rep_nonzero hgauss).mp hproj
  have hcne : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hc
    exact even11GaussianBranchPoint.1.rep_nonzero hc.symm
  have hzero : h 0 = c := by
    have h0 := congrFun hc 0
    simpa [h, even11GaussianVector, Pi.smul_apply, smul_eq_mul] using h0.symm
  have hh0 : h 0 ≠ 0 := by rw [hzero]; exact hcne
  have hdiv (i : Fin 6) : h i / h 0 = even11GaussianVector i := by
    have hi := congrFun hc i
    change c * even11GaussianVector i = h i at hi
    rw [← hi, hzero]
    exact mul_div_cancel_left₀ _ hcne
  apply phaseSignal11_injective
  funext t
  calc
    phaseSignal11 gaussianBasePhase11.1 t =
        even11Lift ((h 0)⁻¹ • h) (t.1 : ZMod 11) :=
      phaseSignal11_phaseCoordsOfEven11 h hh0 t
    _ = even11Lift even11GaussianVector (t.1 : ZMod 11) := by
      simp only [even11Lift_apply, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
      exact hdiv _
    _ = stdAddChar (5 * (t.1 : ZMod 11) ^ 2) :=
      even11Lift_gaussianVector _
    _ = phaseSignal11 (gaussianCoords11 5) t := by
      rw [phaseSignal11_gaussianCoords11]

private theorem phaseDilate11_gaussianCoords11 (a : ZMod 11) :
    phaseDilate11 (gaussianCoords11 a) = gaussianCoords11 (4 * a) := by
  apply phaseSignal11_injective
  funext t
  fin_cases t <;>
    simp [phaseSignal11, phaseDilate11, gaussianCoords11,
      phaseC_re_im] <;>
    congr 1 <;> native_decide +revert

private theorem phaseConjugate11_gaussianCoords11 (a : ZMod 11) :
    phaseConjugate11 (gaussianCoords11 a) = gaussianCoords11 (-a) := by
  apply phaseSignal11_injective
  funext t
  fin_cases t <;>
    simp [phaseSignal11, phaseConjugate11, gaussianCoords11,
      ← even11_conj_stdAddChar]

private theorem phaseDilationGenerator11_pow_gaussianCoords11
    (n : ℕ) (a : ZMod 11) :
    (phaseDilationGenerator11 ^ n) • gaussianCoords11 a =
      gaussianCoords11 ((4 : ZMod 11) ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_smul, ih, phaseDilationGenerator11_smul,
        phaseDilate11_gaussianCoords11]
      congr 1
      simp [pow_succ]
      ring

private theorem phaseConjugationGenerator11_pow_gaussianCoords11
    (n : ℕ) (a : ZMod 11) :
    (phaseConjugationGenerator11 ^ n) • gaussianCoords11 a =
      gaussianCoords11 ((-1 : ZMod 11) ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_smul, ih, phaseConjugationGenerator11_smul,
        phaseConjugate11_gaussianCoords11]
      congr 1
      simp [pow_succ]

def gaussianCoeff11 (g : EvenSymmetry11) : ZMod 11 :=
  (4 : ZMod 11) ^ g.toAdd.1.val *
    ((-1 : ZMod 11) ^ g.toAdd.2.val * 5)

private theorem gaussianBasePhase11_smul (g : EvenSymmetry11) :
    (g • gaussianBasePhase11).1 = gaussianCoords11 (gaussianCoeff11 g) := by
  change g • gaussianBasePhase11.1 = gaussianCoords11 (gaussianCoeff11 g)
  rw [gaussianBasePhase11_coords]
  conv_lhs => rw [evenSymmetry11_generator_decomposition g]
  rw [mul_smul, phaseConjugationGenerator11_pow_gaussianCoords11,
    phaseDilationGenerator11_pow_gaussianCoords11]
  rfl

private theorem gaussianCoeff11_nonzero (g : EvenSymmetry11) :
    gaussianCoeff11 g ≠ 0 := by
  native_decide +revert

private theorem gaussianCoeff11_surjective_nonzero (a : ZMod 11)
    (ha : a ≠ 0) : ∃ g : EvenSymmetry11, gaussianCoeff11 g = a := by
  native_decide +revert

/-- The distinguished invariant fiber is exactly the classical quadratic
Gaussian family, with the Gaussian property stated on the actual signal. -/
theorem isQuadraticGaussian11_iff_invariantU_eq_zero
    (s : PhaseSolution11) :
    IsQuadraticGaussian11 s ↔ phaseInvariantU11 s.1 = 0 := by
  constructor
  · intro hquad
    obtain ⟨a, ha, hs⟩ := (isQuadraticGaussian11_iff_coords s).mp hquad
    obtain ⟨g, hg⟩ := gaussianCoeff11_surjective_nonzero a ha
    have heq : s = g • gaussianBasePhase11 := by
      apply Subtype.ext
      rw [hs, gaussianBasePhase11_smul, hg]
    rw [heq]
    exact (phaseInvariantU11_smul g gaussianBasePhase11.1).trans
      gaussianBasePhase11_u_zero
  · intro hu
    have hrel :=
      (phaseGramSpectrumCertificate11.toPhaseInvariantSpectrumCertificate11).u_complete
        s gaussianBasePhase11 (hu.trans gaussianBasePhase11_u_zero.symm)
    obtain ⟨g, hg⟩ := hrel
    have hcoords : s.1 = gaussianCoords11 (gaussianCoeff11 g) := by
      rw [← hg]
      exact gaussianBasePhase11_smul g
    apply (isQuadraticGaussian11_iff_coords s).2
    exact ⟨gaussianCoeff11 g, gaussianCoeff11_nonzero g, hcoords⟩

/-- The classical quadratic-Gaussian predicate on actual signals. -/
def IsQuadraticGaussianSignal11 (z : ZeroAutocorrSignal11) : Prop :=
  ∃ a : ZMod 11, a ≠ 0 ∧
    ∀ t : Fin 11, z.signal t = stdAddChar (a * (t.1 : ZMod 11) ^ 2)

theorem isQuadraticGaussian11_signal_iff (s : PhaseSolution11) :
    IsQuadraticGaussian11 s ↔
      IsQuadraticGaussianSignal11 (phaseSolutionSignalEquiv11 s) :=
  Iff.rfl

/-- The formal count on normalized even signals, including the genuine
quadratic-Gaussian split. -/
theorem zeroAutocorrSignal11_classification :
    Nat.card ZeroAutocorrSignal11 = 80 ∧
    Nat.card {z : ZeroAutocorrSignal11 // IsQuadraticGaussianSignal11 z} = 10 ∧
    Nat.card {z : ZeroAutocorrSignal11 // ¬ IsQuadraticGaussianSignal11 z} = 70 := by
  refine ⟨zeroAutocorrSignal11_card, ?_, ?_⟩
  · calc
      Nat.card {z : ZeroAutocorrSignal11 // IsQuadraticGaussianSignal11 z} =
          Nat.card {s : PhaseSolution11 // IsQuadraticGaussian11 s} :=
        (Nat.card_congr
          (Equiv.subtypeEquiv phaseSolutionSignalEquiv11
            isQuadraticGaussian11_signal_iff)).symm
      _ = Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 = 0} :=
        Nat.card_congr
          (Equiv.subtypeEquivRight isQuadraticGaussian11_iff_invariantU_eq_zero)
      _ = 10 := phaseSolution11_classification_complete.2.2.1
  · calc
      Nat.card {z : ZeroAutocorrSignal11 // ¬ IsQuadraticGaussianSignal11 z} =
          Nat.card {s : PhaseSolution11 // ¬ IsQuadraticGaussian11 s} :=
        (Nat.card_congr
          (Equiv.subtypeEquiv phaseSolutionSignalEquiv11
            (fun s => not_congr (isQuadraticGaussian11_signal_iff s)))).symm
      _ = Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 ≠ 0} :=
        Nat.card_congr
          (Equiv.subtypeEquivRight
            (fun s => not_congr (isQuadraticGaussian11_iff_invariantU_eq_zero s)))
      _ = 70 := phaseSolution11_classification_complete.2.2.2

end Biunimodular.F11
