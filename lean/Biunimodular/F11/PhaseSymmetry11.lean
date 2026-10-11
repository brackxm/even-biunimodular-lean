/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.EvenSymmetry11Group
public import Biunimodular.F11.PhaseSignalSemantic11
public meta import Biunimodular.F11.ProofTactics
public meta import Biunimodular.F11.EvenSymmetry11Group
public meta import Biunimodular.F11.PhaseSignalSemantic11

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# The concrete dilation/conjugation action on p = 11 phase coordinates

The five nonzero even coordinates are put in multiplicative order
`(κ, λ, ν, μ, ξ)`. Translation of this five-cycle is dilation by `2`, while
the second `ZMod 2` coordinate acts by simultaneous complex conjugation.
-/

/-- Phase coordinates in multiplicative order `(κ, λ, ν, μ, ξ)`. -/
def phaseMultiplicativeValues11 : PhaseCoords11 ≃ (Fin 5 → ℂ) where
  toFun x i :=
    match i.1 with
    | 0 => phaseC x.a x.b
    | 1 => phaseC x.c x.d
    | 2 => phaseC x.g x.h
    | 3 => phaseC x.e x.f
    | _ => phaseC x.j x.k
  invFun c :=
    { a := (c 0).re
      b := (c 0).im
      c := (c 1).re
      d := (c 1).im
      e := (c 3).re
      f := (c 3).im
      g := (c 2).re
      h := (c 2).im
      j := (c 4).re
      k := (c 4).im }
  left_inv x := rfl
  right_inv c := by
    funext i
    fin_cases i <;> apply Complex.ext <;> rfl

/-- Translation of the multiplicative index cycle by an element of `ZMod 5`.
-/
def phaseRotateIndex11 (r : ZMod 5) (i : Fin 5) : Fin 5 :=
  (ZMod.finEquiv 5).symm (ZMod.finEquiv 5 i + r)

@[simp] theorem phaseRotateIndex11_zero (i : Fin 5) :
    phaseRotateIndex11 0 i = i := by
  simp [phaseRotateIndex11]

theorem phaseRotateIndex11_add (r s : ZMod 5) (i : Fin 5) :
    phaseRotateIndex11 s (phaseRotateIndex11 r i) =
      phaseRotateIndex11 (r + s) i := by
  apply (ZMod.finEquiv 5).injective
  simp [phaseRotateIndex11, add_assoc]

@[simp] theorem phaseRotateIndex11_one_zero :
    phaseRotateIndex11 1 0 = 1 := by native_decide

@[simp] theorem phaseRotateIndex11_one_one :
    phaseRotateIndex11 1 1 = 2 := by native_decide

@[simp] theorem phaseRotateIndex11_one_two :
    phaseRotateIndex11 1 2 = 3 := by native_decide

@[simp] theorem phaseRotateIndex11_one_three :
    phaseRotateIndex11 1 3 = 4 := by native_decide

@[simp] theorem phaseRotateIndex11_one_four :
    phaseRotateIndex11 1 4 = 0 := by native_decide

@[simp] theorem phaseRotateIndex11_one_val (i : Fin 5) :
    (phaseRotateIndex11 1 i).val = (i.val + 1) % 5 := by
  native_decide +revert

/-- The order-two action by complex conjugation. -/
def phaseConjugateBit11 (b : ZMod 2) (z : ℂ) : ℂ :=
  if b = 0 then z else star z

@[simp] theorem phaseConjugateBit11_zero (z : ℂ) :
    phaseConjugateBit11 0 z = z := by
  simp [phaseConjugateBit11]

theorem phaseConjugateBit11_add (b c : ZMod 2) (z : ℂ) :
    phaseConjugateBit11 (b + c) z =
      phaseConjugateBit11 b (phaseConjugateBit11 c z) := by
  have hb : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hc : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [phaseConjugateBit11,
      show (1 + 1 : ZMod 2) = 0 by native_decide]

/-- Dilation and conjugation on the five multiplicatively ordered complex
phase values. -/
@[instance_reducible]
def phaseValueAction11 : MulAction EvenSymmetry11 (Fin 5 → ℂ) where
  smul g c i := phaseConjugateBit11 g.toAdd.2
    (c (phaseRotateIndex11 g.toAdd.1 i))
  one_smul c := by
    funext i
    change phaseConjugateBit11 0 (c (phaseRotateIndex11 0 i)) = c i
    simp
  mul_smul g h c := by
    funext i
    change phaseConjugateBit11 (g.toAdd.2 + h.toAdd.2)
        (c (phaseRotateIndex11 (g.toAdd.1 + h.toAdd.1) i)) = _
    rw [phaseConjugateBit11_add, ← phaseRotateIndex11_add]
    rfl

/-- The transported concrete action on the repository's ten real phase
coordinates. -/
@[instance_reducible]
def phaseCoords11Action : MulAction EvenSymmetry11 PhaseCoords11 where
  smul g x := phaseMultiplicativeValues11.symm
    (phaseValueAction11.smul g (phaseMultiplicativeValues11 x))
  one_smul x := by
    change phaseMultiplicativeValues11.symm
      (phaseValueAction11.smul 1 (phaseMultiplicativeValues11 x)) = x
    rw [← phaseMultiplicativeValues11.symm_apply_apply x]
    apply congrArg phaseMultiplicativeValues11.symm
    exact phaseValueAction11.one_smul _
  mul_smul g h x := by
    change phaseMultiplicativeValues11.symm
        (phaseValueAction11.smul (g * h) (phaseMultiplicativeValues11 x)) =
      phaseMultiplicativeValues11.symm
        (phaseValueAction11.smul g
          (phaseMultiplicativeValues11
            (phaseMultiplicativeValues11.symm
              (phaseValueAction11.smul h
                (phaseMultiplicativeValues11 x)))))
    rw [phaseMultiplicativeValues11.apply_symm_apply]
    apply congrArg phaseMultiplicativeValues11.symm
    exact phaseValueAction11.mul_smul _ _ _

instance : MulAction EvenSymmetry11 PhaseCoords11 := phaseCoords11Action

/-- Dilation by the generator `2`, written in the repository's additive
coordinate order `(κ, λ, μ, ν, ξ)`. -/
def phaseDilate11 (x : PhaseCoords11) : PhaseCoords11 where
  a := x.c
  b := x.d
  c := x.g
  d := x.h
  e := x.j
  f := x.k
  g := x.e
  h := x.f
  j := x.a
  k := x.b

/-- Simultaneous complex conjugation of the five phase values. -/
def phaseConjugate11 (x : PhaseCoords11) : PhaseCoords11 where
  a := x.a
  b := -x.b
  c := x.c
  d := -x.d
  e := x.e
  f := -x.f
  g := x.g
  h := -x.h
  j := x.j
  k := -x.k

/-- The five phase equations are invariant under generator dilation. -/
theorem phaseDilate11_isPhaseSolution_iff (x : PhaseCoords11) :
    (phaseDilate11 x).IsPhaseSolution ↔ x.IsPhaseSolution := by
  simp only [PhaseCoords11.IsPhaseSolution, PhaseCoords11.CircleEquations,
    PhaseCoords11.E1, PhaseCoords11.E2, PhaseCoords11.E3,
    PhaseCoords11.E4, PhaseCoords11.E5, phaseDilate11]
  ring_nf
  tauto

/-- The five phase equations are invariant under simultaneous conjugation. -/
theorem phaseConjugate11_isPhaseSolution_iff (x : PhaseCoords11) :
    (phaseConjugate11 x).IsPhaseSolution ↔ x.IsPhaseSolution := by
  simp only [PhaseCoords11.IsPhaseSolution, PhaseCoords11.CircleEquations,
    PhaseCoords11.E1, PhaseCoords11.E2, PhaseCoords11.E3,
    PhaseCoords11.E4, PhaseCoords11.E5, phaseConjugate11]
  ring_nf

def phaseDilationGenerator11 : EvenSymmetry11 :=
  Multiplicative.ofAdd (1, 0)

def phaseConjugationGenerator11 : EvenSymmetry11 :=
  Multiplicative.ofAdd (0, 1)

theorem phaseDilationGenerator11_smul (x : PhaseCoords11) :
    phaseDilationGenerator11 • x = phaseDilate11 x := by
  change phaseMultiplicativeValues11.symm
      (phaseValueAction11.smul phaseDilationGenerator11
        (phaseMultiplicativeValues11 x)) = phaseDilate11 x
  apply phaseMultiplicativeValues11.injective
  rw [phaseMultiplicativeValues11.apply_symm_apply]
  change (fun i => phaseConjugateBit11 0
      (phaseMultiplicativeValues11 x (phaseRotateIndex11 1 i))) =
    phaseMultiplicativeValues11 (phaseDilate11 x)
  funext i
  fin_cases i <;>
    norm_num [phaseDilationGenerator11, phaseCoords11Action,
      phaseValueAction11, phaseMultiplicativeValues11,
      phaseConjugateBit11, phaseDilate11, phaseC]

theorem phaseConjugationGenerator11_smul (x : PhaseCoords11) :
    phaseConjugationGenerator11 • x = phaseConjugate11 x := by
  change phaseMultiplicativeValues11.symm
      (phaseValueAction11.smul phaseConjugationGenerator11
        (phaseMultiplicativeValues11 x)) = phaseConjugate11 x
  apply phaseMultiplicativeValues11.injective
  rw [phaseMultiplicativeValues11.apply_symm_apply]
  change (fun i => phaseConjugateBit11 1
      (phaseMultiplicativeValues11 x (phaseRotateIndex11 0 i))) =
    phaseMultiplicativeValues11 (phaseConjugate11 x)
  funext i
  fin_cases i <;>
    norm_num [phaseConjugationGenerator11, phaseCoords11Action,
      phaseValueAction11, phaseMultiplicativeValues11,
      phaseConjugateBit11, phaseConjugate11, phaseC, Complex.ext_iff]

theorem phaseDilationGenerator11_pow_isPhaseSolution_iff
    (n : ℕ) (x : PhaseCoords11) :
    ((phaseDilationGenerator11 ^ n) • x).IsPhaseSolution ↔
      x.IsPhaseSolution := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_smul, phaseDilationGenerator11_smul,
        phaseDilate11_isPhaseSolution_iff, ih]

theorem phaseConjugationGenerator11_pow_isPhaseSolution_iff
    (n : ℕ) (x : PhaseCoords11) :
    ((phaseConjugationGenerator11 ^ n) • x).IsPhaseSolution ↔
      x.IsPhaseSolution := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_smul, phaseConjugationGenerator11_smul,
        phaseConjugate11_isPhaseSolution_iff, ih]

/-- Every normalized even symmetry is uniquely a power of generator dilation
times a possible conjugation. -/
theorem evenSymmetry11_generator_decomposition (g : EvenSymmetry11) :
    g = phaseDilationGenerator11 ^ g.toAdd.1.val *
      phaseConjugationGenerator11 ^ g.toAdd.2.val := by
  native_decide +revert

/-- The actual order-ten symmetry action preserves the polynomial phase
solution locus. -/
theorem phaseCoords11_isPhaseSolution_smul_iff
    (g : EvenSymmetry11) (x : PhaseCoords11) :
    (g • x).IsPhaseSolution ↔ x.IsPhaseSolution := by
  rw [evenSymmetry11_generator_decomposition g, mul_smul,
    phaseDilationGenerator11_pow_isPhaseSolution_iff,
    phaseConjugationGenerator11_pow_isPhaseSolution_iff]

/-- A nontrivial generator dilation cannot fix a phase solution: it would
make all five nonzero phase values equal, forcing the first autocorrelation
to be both zero and an impossible odd sum. -/
theorem phaseDilationGenerator11_no_fixed
    (x : PhaseCoords11) (hs : x.IsPhaseSolution) :
    phaseDilationGenerator11 • x ≠ x := by
  intro hfix
  rw [phaseDilationGenerator11_smul] at hfix
  have hca : x.c = x.a := congrArg PhaseCoords11.a hfix
  have hdb : x.d = x.b := congrArg PhaseCoords11.b hfix
  have hgc : x.g = x.c := congrArg PhaseCoords11.c hfix
  have hhd : x.h = x.d := congrArg PhaseCoords11.d hfix
  have hje : x.j = x.e := congrArg PhaseCoords11.e hfix
  have hkf : x.k = x.f := congrArg PhaseCoords11.f hfix
  have heg : x.e = x.g := congrArg PhaseCoords11.g hfix
  have hfh : x.f = x.h := congrArg PhaseCoords11.h hfix
  rcases hs with ⟨⟨hab, _, _, _, _⟩, h1, _, _, _, _⟩
  unfold PhaseCoords11.E1 at h1
  rw [hje, heg, hgc, hca, hkf, hfh, hhd, hdb] at h1
  nlinarith

/-- Simultaneous conjugation cannot fix a phase solution, since a fixed point
would be a sign-valued CAZAC sequence of odd length. -/
theorem phaseConjugationGenerator11_no_fixed
    (x : PhaseCoords11) (hs : x.IsPhaseSolution) :
    phaseConjugationGenerator11 • x ≠ x := by
  intro hfix
  rw [phaseConjugationGenerator11_smul] at hfix
  have hb : -x.b = x.b := congrArg PhaseCoords11.b hfix
  have hd : -x.d = x.d := congrArg PhaseCoords11.d hfix
  have hf : -x.f = x.f := congrArg PhaseCoords11.f hfix
  have hh : -x.h = x.h := congrArg PhaseCoords11.h hfix
  have hk : -x.k = x.k := congrArg PhaseCoords11.k hfix
  have hb0 : x.b = 0 := by linarith
  have hd0 : x.d = 0 := by linarith
  have hf0 : x.f = 0 := by linarith
  have hh0 : x.h = 0 := by linarith
  have hk0 : x.k = 0 := by linarith
  rcases hs with ⟨⟨hab, hcd, hef, hgh, hjk⟩, h1, _, _, _, _⟩
  have ha2 : x.a ^ 2 = 1 := by nlinarith
  have hc2 : x.c ^ 2 = 1 := by nlinarith
  have he2 : x.e ^ 2 = 1 := by nlinarith
  have hg2 : x.g ^ 2 = 1 := by nlinarith
  have hj2 : x.j ^ 2 = 1 := by nlinarith
  unfold PhaseCoords11.E1 at h1
  rw [hb0, hd0, hf0, hh0, hk0] at h1
  rcases sq_eq_one_iff.mp ha2 with ha | ha <;>
    rcases sq_eq_one_iff.mp hc2 with hc | hc <;>
    rcases sq_eq_one_iff.mp he2 with he | he <;>
    rcases sq_eq_one_iff.mp hg2 with hg | hg <;>
    rcases sq_eq_one_iff.mp hj2 with hj | hj <;>
    norm_num [ha, hc, he, hg, hj] at h1

private theorem phaseCoords11_pow_smul_eq_of_smul_eq
    (g : EvenSymmetry11) (x : PhaseCoords11) (hfix : g • x = x) :
    ∀ n : ℕ, (g ^ n) • x = x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_smul, ih, hfix]

private theorem phaseRotation11_generates_dilation
    (r : ZMod 5) (hr : r ≠ 0) :
    ∃ n : Fin 5,
      (Multiplicative.ofAdd (r, 0) : EvenSymmetry11) ^ n.val =
        phaseDilationGenerator11 := by
  native_decide +revert

/-- Every nonidentity dilation acts without fixed points on the phase-solution
locus. -/
theorem phaseRotation11_no_fixed
    (r : ZMod 5) (hr : r ≠ 0)
    (x : PhaseCoords11) (hs : x.IsPhaseSolution) :
    (Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • x ≠ x := by
  intro hfix
  rcases phaseRotation11_generates_dilation r hr with ⟨n, hn⟩
  have hp := phaseCoords11_pow_smul_eq_of_smul_eq
    (Multiplicative.ofAdd (r, 0)) x hfix n.val
  rw [hn] at hp
  exact phaseDilationGenerator11_no_fixed x hs hp

private theorem phaseConjugatedSymmetry11_sq (r : ZMod 5) :
    (Multiplicative.ofAdd (r, 1) : EvenSymmetry11) ^ 2 =
      Multiplicative.ofAdd (r + r, 0) := by
  native_decide +revert

private theorem zmod5_add_self_ne_zero (r : ZMod 5) (hr : r ≠ 0) :
    r + r ≠ 0 := by
  native_decide +revert

private theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  native_decide +revert

/-- The only normalized even symmetry fixing a phase solution is the identity.
This combines the nontrivial-rotation argument with the fact that the square
of a conjugated nontrivial rotation is again a nontrivial rotation. -/
theorem phaseSymmetry11_eq_one_of_fixed
    (g : EvenSymmetry11) (x : PhaseCoords11) (hs : x.IsPhaseSolution)
    (hfix : g • x = x) : g = 1 := by
  let r : ZMod 5 := g.toAdd.1
  let b : ZMod 2 := g.toAdd.2
  have hg : g = Multiplicative.ofAdd (r, b) := by
    dsimp [r, b]
    exact (ofAdd_toAdd g).symm
  have hb : b = 0 ∨ b = 1 := zmod2_eq_zero_or_one b
  rcases hb with hb | hb
  · by_cases hr : r = 0
    · rw [hg, hb, hr]
      rfl
    · exfalso
      apply phaseRotation11_no_fixed r hr x hs
      simpa [hg, hb] using hfix
  · by_cases hr : r = 0
    · exfalso
      apply phaseConjugationGenerator11_no_fixed x hs
      simpa [hg, hb, hr, phaseConjugationGenerator11] using hfix
    · exfalso
      have hraw : (Multiplicative.ofAdd (r, 1) : EvenSymmetry11) • x = x := by
        simpa [hg, hb] using hfix
      have hsq := phaseCoords11_pow_smul_eq_of_smul_eq
        (Multiplicative.ofAdd (r, 1)) x hraw 2
      rw [phaseConjugatedSymmetry11_sq] at hsq
      exact phaseRotation11_no_fixed (r + r)
        (zmod5_add_self_ne_zero r hr) x hs hsq

/-- The concrete normalized even `p = 11` polynomial solution type. -/
abbrev PhaseSolution11 := {x : PhaseCoords11 // x.IsPhaseSolution}

/-- The concrete symmetry action restricted to normalized even p = 11 phase
solutions. -/
instance : MulAction EvenSymmetry11 PhaseSolution11 where
  smul g x := ⟨g • x.1,
    (phaseCoords11_isPhaseSolution_smul_iff g x.1).2 x.2⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : EvenSymmetry11) • x.1 = x.1
    exact one_smul EvenSymmetry11 x.1
  mul_smul g h x := by
    apply Subtype.ext
    change (g * h) • x.1 = g • h • x.1
    exact mul_smul g h x.1

/-- The concrete dilation/conjugation action on normalized phase solutions is
free. -/
instance : IsCancelSMul EvenSymmetry11 PhaseSolution11 :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (fun g x hfix =>
    phaseSymmetry11_eq_one_of_fixed g x.1 x.2
      (congrArg Subtype.val hfix))

end Biunimodular.F11
