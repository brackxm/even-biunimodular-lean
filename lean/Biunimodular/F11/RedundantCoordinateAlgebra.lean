/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.MvPolynomial.Ideal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Biunimodular.F11.RedundantCoordinate
noncomputable section

variable {R : Type*} [CommRing R] {n : ℕ}

abbrev BasePolynomial (R : Type*) [CommRing R] (n : ℕ) := MvPolynomial (Fin n) R
abbrev ExtendedPolynomial (R : Type*) [CommRing R] (n : ℕ) :=
  MvPolynomial (Fin (n + 1)) R

def baseIdeal (gs : List (BasePolynomial R n)) : Ideal (BasePolynomial R n) :=
  Ideal.span {f | f ∈ gs}

abbrev BaseAlgebra (gs : List (BasePolynomial R n)) := BasePolynomial R n ⧸ baseIdeal gs

/-- Include the original variables while reserving the last variable for a
redundant polynomial coordinate. -/
def includeVariables : BasePolynomial R n →ₐ[R] ExtendedPolynomial R n :=
  MvPolynomial.rename Fin.castSucc

def extendedGenerators (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    List (ExtendedPolynomial R n) :=
  gs.map includeVariables ++ [MvPolynomial.X (Fin.last n) - includeVariables t]

def extendedIdeal (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    Ideal (ExtendedPolynomial R n) := Ideal.span {f | f ∈ extendedGenerators gs t}

abbrev ExtendedAlgebra (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :=
  ExtendedPolynomial R n ⧸ extendedIdeal gs t

def values (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    Fin (n + 1) → BaseAlgebra gs :=
  Fin.lastCases (Ideal.Quotient.mkₐ R (baseIdeal gs) t)
    (fun i => Ideal.Quotient.mkₐ R (baseIdeal gs) (MvPolynomial.X i))

private theorem eval_include (gs : List (BasePolynomial R n)) (t f : BasePolynomial R n) :
    MvPolynomial.aeval (values gs t) (includeVariables f) =
      Ideal.Quotient.mkₐ R (baseIdeal gs) f := by
  have h : (MvPolynomial.aeval (values gs t)).comp includeVariables =
      Ideal.Quotient.mkₐ R (baseIdeal gs) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [includeVariables, values]
  exact congrArg (fun a : BasePolynomial R n →ₐ[R] BaseAlgebra gs => a f) h

private theorem eval_vanish (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    ∀ f ∈ extendedIdeal gs t, MvPolynomial.aeval (values gs t) f = 0 := by
  have hle : extendedIdeal gs t ≤ RingHom.ker (MvPolynomial.aeval (values gs t)).toRingHom := by
    apply Ideal.span_le.mpr
    intro f hf
    simp only [extendedGenerators, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      change MvPolynomial.aeval (values gs t) (includeVariables g) = 0
      rw [eval_include]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hg)
    · simp [RingHom.mem_ker, eval_include, values]
  intro f hf
  exact hle hf

def toBase (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    ExtendedAlgebra gs t →ₐ[R] BaseAlgebra gs :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (values gs t)) (eval_vanish gs t)

private theorem include_vanish (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    ∀ f ∈ baseIdeal gs, Ideal.Quotient.mkₐ R (extendedIdeal gs t) (includeVariables f) = 0 := by
  have hle : baseIdeal gs ≤ RingHom.ker
      ((Ideal.Quotient.mkₐ R (extendedIdeal gs t)).comp includeVariables).toRingHom := by
    apply Ideal.span_le.mpr
    intro f hf
    change Ideal.Quotient.mkₐ R (extendedIdeal gs t) (includeVariables f) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    apply List.mem_append.mpr
    exact Or.inl (List.mem_map.mpr ⟨f, hf, rfl⟩)
  intro f hf
  exact hle hf

def fromBase (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    BaseAlgebra gs →ₐ[R] ExtendedAlgebra gs t :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ R (extendedIdeal gs t)).comp includeVariables) (include_vanish gs t)

private theorem last_eq_trace (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    Ideal.Quotient.mkₐ R (extendedIdeal gs t) (MvPolynomial.X (Fin.last n)) =
      Ideal.Quotient.mkₐ R (extendedIdeal gs t) (includeVariables t) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  simp [extendedGenerators]

/-- Adding a variable with its defining polynomial equation preserves the
actual coordinate algebra, including any nilpotents. -/
def algebraEquiv (gs : List (BasePolynomial R n)) (t : BasePolynomial R n) :
    ExtendedAlgebra gs t ≃ₐ[R] BaseAlgebra gs := by
  apply AlgEquiv.ofAlgHom (toBase gs t) (fromBase gs t)
  · apply AlgHom.ext
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (baseIdeal gs) x
    simp [toBase, fromBase, Ideal.Quotient.liftₐ_apply,
      Ideal.Quotient.lift_mk, eval_include]
  · apply AlgHom.ext
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (extendedIdeal gs t) x
    have h : ((fromBase gs t).comp (toBase gs t)).comp
        (Ideal.Quotient.mkₐ R (extendedIdeal gs t)) =
        Ideal.Quotient.mkₐ R (extendedIdeal gs t) := by
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [toBase, fromBase, values, Ideal.Quotient.liftₐ_apply,
          Ideal.Quotient.lift_mk] using (last_eq_trace gs t).symm
      · simp [toBase, fromBase, values, includeVariables,
          Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact congrArg (fun a : ExtendedPolynomial R n →ₐ[R] ExtendedAlgebra gs t => a f) h

end
end Biunimodular.F11.RedundantCoordinate
