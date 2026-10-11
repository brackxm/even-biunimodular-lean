/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.GroupTheory.GroupAction.Quotient
import Biunimodular.F11.FixedSliceRootIntervalCertificate
import Biunimodular.F11.PhaseGram11
import Mathlib.Algebra.Ring.BooleanRing

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# The physical phase quotient as a rank-two Gram quotient

The Gram matrix forgets exactly simultaneous complex conjugation.  Dilation
then acts by cyclic relabelling of the last five rows and columns.  This file
proves the resulting value-preserving equivalence between the concrete
order-ten physical orbit quotient and the cyclic quotient of the real Gram
locus.
-/

/-- The simultaneous conjugate of a concrete phase solution. -/
def phaseSolution11Conjugate (s : PhaseSolution11) : PhaseSolution11 :=
  ⟨phaseConjugate11 s.1,
    (phaseConjugate11_isPhaseSolution_iff s.1).2 s.2⟩

@[simp] theorem phaseSolution11Conjugate_val (s : PhaseSolution11) :
    (phaseSolution11Conjugate s).1 = phaseConjugate11 s.1 := rfl

@[simp] theorem phaseSolution11Conjugate_conjugate (s : PhaseSolution11) :
    phaseSolution11Conjugate (phaseSolution11Conjugate s) = s := by
  apply Subtype.ext
  change phaseConjugate11 (phaseConjugate11 s.1) = s.1
  rcases s.1 with ⟨a, b, c, d, e, f, g, h, j, k⟩
  simp [phaseConjugate11]

/-- The Boolean action which remembers only simultaneous conjugation. -/
def phaseSolution11ConjVAdd (b : Bool) (s : PhaseSolution11) :
    PhaseSolution11 :=
  bif b then phaseSolution11Conjugate s else s

instance : VAdd Bool PhaseSolution11 := ⟨phaseSolution11ConjVAdd⟩

@[simp] theorem false_vadd_phaseSolution11 (s : PhaseSolution11) :
    false +ᵥ s = s := rfl

@[simp] theorem true_vadd_phaseSolution11 (s : PhaseSolution11) :
    true +ᵥ s = phaseSolution11Conjugate s := rfl

instance : AddAction Bool PhaseSolution11 where
  zero_vadd s := rfl
  add_vadd b c s := by
    cases b <;> cases c <;> simp [Bool.add_eq_xor]

/-- The normalized real Gram matrix attached to a phase solution. -/
def phaseSolution11GramMap (s : PhaseSolution11) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  phaseGramMatrix11 s.1

/-- The physical Gram locus, defined as the actual image of normalized phase
solutions.  Its intrinsic PSD/rank/linear properties are proved below. -/
abbrev PhaseGramLocus11 := Set.range phaseSolution11GramMap

/-- Every point of the physical Gram locus is symmetric, PSD, has diagonal
`2`, rank at most `2`, and satisfies the five linear simple-index relations.
-/
theorem phaseGramLocus11_properties (K : PhaseGramLocus11) :
    K.1.IsSymm ∧ K.1.PosSemidef ∧
      (∀ i, K.1 i i = 2) ∧ K.1.rank ≤ 2 ∧
      PhaseGramLinearRelations11 K.1 := by
  rcases K.2 with ⟨s, hs⟩
  rw [← hs]
  exact ⟨phaseGramMatrix11_isSymm s.1,
    phaseGramMatrix11_posSemidef s.1,
    phaseGramMatrix11_diagonal s.1 s.2.1,
    phaseGramMatrix11_rank_le_two s.1,
    phaseGramMatrix11_linearRelations s.1 s.2⟩

/-- Equality of physical Gram matrices is exactly equality modulo simultaneous
conjugation. -/
theorem phaseSolution11GramMap_eq_iff (s t : PhaseSolution11) :
    phaseSolution11GramMap s = phaseSolution11GramMap t ↔
      t = s ∨ t = phaseSolution11Conjugate s := by
  change phaseGramMatrix11 s.1 = phaseGramMatrix11 t.1 ↔ _
  rw [phaseGramMatrix11_eq_iff_eq_or_conjugate s.1 t.1 s.2.1 t.2.1]
  constructor
  · rintro (h | h)
    · left
      exact Subtype.ext h
    · right
      apply Subtype.ext
      exact h
  · rintro (h | h)
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h

/-- The Boolean conjugation orbit relation is the kernel relation of the
concrete Gram map. -/
theorem phaseSolution11_conjOrbitRel_iff_gram_eq
    (s t : PhaseSolution11) :
    AddAction.orbitRel Bool PhaseSolution11 s t ↔
      phaseSolution11GramMap s = phaseSolution11GramMap t := by
  rw [AddAction.orbitRel_apply, phaseSolution11GramMap_eq_iff]
  constructor
  · rintro ⟨b, rfl⟩
    cases b <;> simp
  · rintro (rfl | h)
    · exact ⟨false, rfl⟩
    · refine ⟨true, ?_⟩
      simp [h]

/-- Physical phases modulo conjugation are exactly their real Gram matrices.
This is the converse Gram reconstruction theorem at the quotient level. -/
noncomputable def phaseSolution11ConjQuotientGramEquiv :
    AddAction.orbitRel.Quotient Bool PhaseSolution11 ≃ PhaseGramLocus11 :=
  (Quotient.congrRight phaseSolution11_conjOrbitRel_iff_gram_eq).trans
    (Setoid.quotientKerEquivRange phaseSolution11GramMap)

/-- Cyclic relabelling preserves the physical Gram locus. -/
def phaseGramLocus11VAdd (r : ZMod 5) (K : PhaseGramLocus11) :
    PhaseGramLocus11 :=
  ⟨phaseGramRelabelMatrix11 r K.1, by
    rcases K.2 with ⟨s, hs⟩
    refine ⟨(Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • s, ?_⟩
    change phaseGramMatrix11
        ((Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • s.1) = _
    rw [phaseGramMatrix11_dilation]
    exact congrArg (phaseGramRelabelMatrix11 r) hs⟩

instance : VAdd (ZMod 5) PhaseGramLocus11 := ⟨phaseGramLocus11VAdd⟩

@[simp] theorem zero_vadd_phaseGramLocus11 (K : PhaseGramLocus11) :
    (0 : ZMod 5) +ᵥ K = K := by
  apply Subtype.ext
  exact phaseGramRelabelMatrix11_zero K.1

instance : AddAction (ZMod 5) PhaseGramLocus11 where
  zero_vadd := zero_vadd_phaseGramLocus11
  add_vadd r s K := by
    apply Subtype.ext
    exact phaseGramRelabelMatrix11_add r s K.1

/-- Dilation equivariance on the physical Gram locus. -/
theorem phaseSolution11GramPoint_smul
    (g : EvenSymmetry11) (s : PhaseSolution11) :
    (⟨phaseSolution11GramMap (g • s), ⟨g • s, rfl⟩⟩ : PhaseGramLocus11) =
      g.toAdd.1 +ᵥ
        (⟨phaseSolution11GramMap s, ⟨s, rfl⟩⟩ : PhaseGramLocus11) := by
  apply Subtype.ext
  exact phaseGramMatrix11_smul g s.1

/-- The cyclic quotient of the real PSD rank-two Gram locus. -/
abbrev PhaseGramOrbit11 :=
  AddAction.orbitRel.Quotient (ZMod 5) PhaseGramLocus11

/-- The Gram orbit attached to a normalized physical solution. -/
def phaseSolution11GramOrbitMap : PhaseSolution11Orbit → PhaseGramOrbit11 :=
  Quotient.lift
    (fun s : PhaseSolution11 ↦
      Quotient.mk''
        (⟨phaseSolution11GramMap s, ⟨s, rfl⟩⟩ : PhaseGramLocus11))
    (by
      intro s t hst
      change MulAction.orbitRel EvenSymmetry11 PhaseSolution11 s t at hst
      rw [MulAction.orbitRel_apply] at hst
      rcases hst with ⟨g, rfl⟩
      rw [phaseSolution11GramPoint_smul]
      exact AddAction.orbitRel.Quotient.quotient_vadd_eq)

@[simp] theorem phaseSolution11GramOrbitMap_mk (s : PhaseSolution11) :
    phaseSolution11GramOrbitMap (Quotient.mk'' s) =
      Quotient.mk''
        (⟨phaseSolution11GramMap s, ⟨s, rfl⟩⟩ : PhaseGramLocus11) := rfl

/-- The physical order-ten quotient and the cyclic Gram quotient are
equivalent.  Surjectivity is Gram reconstruction; injectivity uses the fact
that a normalized Gram fiber consists of one conjugate pair. -/
theorem phaseSolution11GramOrbitMap_bijective :
    Function.Bijective phaseSolution11GramOrbitMap := by
  constructor
  · intro q₁ q₂ hq
    refine Quotient.inductionOn₂' q₁ q₂ ?_ hq
    intro s t hst
    apply Quotient.sound
    have hrel := Quotient.exact hst
    change AddAction.orbitRel (ZMod 5) PhaseGramLocus11
      (⟨phaseSolution11GramMap s, ⟨s, rfl⟩⟩ : PhaseGramLocus11)
      (⟨phaseSolution11GramMap t, ⟨t, rfl⟩⟩ : PhaseGramLocus11) at hrel
    rw [AddAction.orbitRel_apply] at hrel
    rcases hrel with ⟨r, hr⟩
    have hmatrix :
        phaseGramMatrix11
            ((Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • t.1) =
          phaseGramMatrix11 s.1 := by
      rw [phaseGramMatrix11_dilation]
      exact congrArg Subtype.val hr
    have hfiber :=
      (phaseGramMatrix11_eq_iff_eq_or_conjugate
        (((Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • t).1)
        s.1
        (((Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • t).2.1)
        s.2.1).mp hmatrix
    change MulAction.orbitRel EvenSymmetry11 PhaseSolution11 s t
    rw [MulAction.orbitRel_apply]
    rcases hfiber with hsame | hconj
    · refine ⟨Multiplicative.ofAdd (r, 0), ?_⟩
      exact Subtype.ext hsame.symm
    · refine ⟨phaseConjugationGenerator11 *
          Multiplicative.ofAdd (r, 0), ?_⟩
      change (phaseConjugationGenerator11 *
        Multiplicative.ofAdd (r, 0)) • t = s
      rw [mul_smul]
      apply Subtype.ext
      change phaseConjugationGenerator11 •
          ((Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • t.1) = s.1
      rw [phaseConjugationGenerator11_smul]
      exact hconj.symm
  · intro q
    refine Quotient.inductionOn' q ?_
    intro K
    rcases K.2 with ⟨s, hs⟩
    refine ⟨Quotient.mk'' s, ?_⟩
    apply Quotient.sound
    change AddAction.orbitRel (ZMod 5) PhaseGramLocus11
      (⟨phaseSolution11GramMap s, ⟨s, rfl⟩⟩ : PhaseGramLocus11) K
    rw [AddAction.orbitRel_apply]
    refine ⟨0, ?_⟩
    apply Subtype.ext
    simpa using hs.symm

/-- The symmetry-preserving Gram-moduli equivalence. -/
noncomputable def phaseSolution11OrbitGramEquiv :
    PhaseSolution11Orbit ≃ PhaseGramOrbit11 :=
  Equiv.ofBijective phaseSolution11GramOrbitMap
    phaseSolution11GramOrbitMap_bijective

/-- Cyclic rotation of the five nonzero vertices as an equivalence. -/
def phaseGramRotateEquiv11 (r : ZMod 5) : Fin 5 ≃ Fin 5 where
  toFun := phaseRotateIndex11 r
  invFun := phaseRotateIndex11 (-r)
  left_inv i := by
    rw [phaseRotateIndex11_add]
    simp
  right_inv i := by
    rw [phaseRotateIndex11_add]
    simp

/-- The Gram coordinate `σ² / 11` is invariant under cyclic relabelling. -/
theorem phaseGramSigma11_relabel (r : ZMod 5)
    (K : Matrix (Fin 6) (Fin 6) ℝ) :
    phaseGramSigma11 (phaseGramRelabelMatrix11 r K) =
      phaseGramSigma11 K := by
  simp only [phaseGramSigma11, phaseGramRelabelMatrix11,
    phaseGramRelabelIndex11_vertex]
  congr 1
  exact Equiv.sum_comp (phaseGramRotateEquiv11 r)
    (fun a ↦ K 0 (phaseGramVertex11 a))

/-- The squared affine Gram coordinate descended through cyclic relabelling.
-/
def phaseGramOrbitInvariantU11 : PhaseGramOrbit11 → ℝ :=
  Quotient.lift
    (fun K : PhaseGramLocus11 ↦ phaseGramSigma11 K.1 ^ 2 / 11)
    (by
      intro K L hKL
      change AddAction.orbitRel (ZMod 5) PhaseGramLocus11 K L at hKL
      rw [AddAction.orbitRel_apply] at hKL
      rcases hKL with ⟨r, rfl⟩
      change phaseGramSigma11 (phaseGramRelabelMatrix11 r L.1) ^ 2 / 11 = _
      rw [phaseGramSigma11_relabel])

@[simp] theorem phaseGramOrbitInvariantU11_mk (K : PhaseGramLocus11) :
    phaseGramOrbitInvariantU11 (Quotient.mk'' K) =
      phaseGramSigma11 K.1 ^ 2 / 11 := rfl

/-- The Gram-moduli equivalence preserves the concrete physical invariant.
-/
theorem phaseSolution11OrbitGramEquiv_value
    (q : PhaseSolution11Orbit) :
    phaseGramOrbitInvariantU11 (phaseSolution11OrbitGramEquiv q) =
      phaseSolution11OrbitInvariantU q := by
  refine Quotient.inductionOn' q ?_
  intro s
  exact (phaseInvariantU11_eq_gramSigma s.1).symm

/-- The physical orbit invariant lies in the closed unit interval before any
root-spectrum input is used. -/
theorem phaseSolution11OrbitInvariantU_mem_unitInterval
    (q : PhaseSolution11Orbit) :
    0 ≤ phaseSolution11OrbitInvariantU q ∧
      phaseSolution11OrbitInvariantU q ≤ 1 := by
  refine Quotient.inductionOn' q ?_
  intro s
  exact phaseInvariantU11_mem_unitInterval s.1 s.2

/-- The same unconditional interval bound in Gram-moduli coordinates. -/
theorem phaseGramOrbitInvariantU11_mem_unitInterval
    (q : PhaseGramOrbit11) :
    0 ≤ phaseGramOrbitInvariantU11 q ∧ phaseGramOrbitInvariantU11 q ≤ 1 := by
  let p : PhaseSolution11Orbit := phaseSolution11OrbitGramEquiv.symm q
  have hp := phaseSolution11OrbitInvariantU_mem_unitInterval p
  have hvalue : phaseGramOrbitInvariantU11 q =
      phaseSolution11OrbitInvariantU p := by
    rw [← phaseSolution11OrbitGramEquiv_value p]
    simp [p]
  rwa [hvalue]

/-- Turn polynomial-root evidence for the concrete Gram invariant into the
actual split-root map.  Strictness at the upper endpoint is derived from the
fact that `P₁₆(1) ≠ 0`. -/
def phaseGramOrbitSplitRootMap
    (hroot : ∀ q : PhaseGramOrbit11,
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (phaseGramOrbitInvariantU11 q : ℂ)) :
    PhaseGramOrbit11 → SplitQuotientRoot :=
  fun q ↦
    let r : FixedSliceQuotientRoot :=
      ⟨(phaseGramOrbitInvariantU11 q : ℂ), by
        rw [Polynomial.mem_rootSet]
        refine ⟨fixedSliceQuotientP16Q_separable.ne_zero, ?_⟩
        rw [aeval_def, eval₂_eq_eval_map]
        exact hroot q⟩
    ⟨r, (fixedSliceQuotientRootSplit_iff r).2 <| by
      have hu := phaseGramOrbitInvariantU11_mem_unitInterval q
      refine ⟨by simp [r], by simpa [r] using hu.1, ?_⟩
      have hne : phaseGramOrbitInvariantU11 q ≠ 1 := by
        intro hone
        apply fixedSliceQuotientP16Q_one_not_isRoot
        simpa [hone] using hroot q
      simpa [r] using lt_of_le_of_ne hu.2 hne⟩

@[simp] theorem phaseGramOrbitSplitRootMap_value
    (hroot : ∀ q : PhaseGramOrbit11,
      (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
        (phaseGramOrbitInvariantU11 q : ℂ))
    (q : PhaseGramOrbit11) :
    ((phaseGramOrbitSplitRootMap hroot q : SplitQuotientRoot) : ℂ) =
      (phaseGramOrbitInvariantU11 q : ℂ) := rfl

/-- The physical root-spectrum certificate.  Both fields
refer to the concrete rank-two Gram quotient and its actual coordinate
`σ²/11`; an arbitrary eight-point equivalence is not accepted. -/
structure PhaseGramSpectrumCertificate where
  gram_u_isRoot : ∀ q : PhaseGramOrbit11,
    (fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot
      (phaseGramOrbitInvariantU11 q : ℂ)
  gram_u_bijective :
    Function.Bijective (phaseGramOrbitSplitRootMap gram_u_isRoot)

/-- The Gram spectrum certificate identifies the physical moduli with the
eight split roots by the actual invariant value. -/
noncomputable def PhaseGramSpectrumCertificate.gramRootEquiv
    (C : PhaseGramSpectrumCertificate) :
    PhaseGramOrbit11 ≃ SplitQuotientRoot :=
  Equiv.ofBijective (phaseGramOrbitSplitRootMap C.gram_u_isRoot)
    C.gram_u_bijective

@[simp] theorem PhaseGramSpectrumCertificate.gramRootEquiv_value
    (C : PhaseGramSpectrumCertificate) (q : PhaseGramOrbit11) :
    ((C.gramRootEquiv q : SplitQuotientRoot) : ℂ) =
      (phaseGramOrbitInvariantU11 q : ℂ) := rfl

end

end Biunimodular.F11
