/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FiniteFieldFrobeniusCycle
import Biunimodular.F11.FrobeniusRootReduction

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- The concrete finite-field Frobenius permutation acts by the cardinality
power on every root. -/
theorem finiteFieldFrobPerm_apply (p : F[X])
    (x : p.rootSet p.SplittingField) :
    ((finiteFieldFrobPerm p x) : p.SplittingField) =
      (x : p.SplittingField) ^ Fintype.card F := by
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨SplittingField.splits p⟩
  let : MulAction p.Gal (p.rootSet p.SplittingField) :=
    Polynomial.Gal.galActionAux p
  let : SMul p.Gal (p.rootSet p.SplittingField) :=
    (Polynomial.Gal.galActionAux p).toSMul
  change (FiniteField.frobeniusAlgEquivOfAlgebraic F p.SplittingField) x.1 = _
  exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic F p.SplittingField) x.1

/-- The Frobenius permutation on roots in any splitting field for `p`. -/
noncomputable def finiteFieldFrobPermIn (p : F[X]) (K : Type*)
    [Field K] [Algebra F K]
    [Fact ((p.map (algebraMap F K)).Splits)] :
    Equiv.Perm (p.rootSet K) :=
  (Polynomial.Gal.rootsEquivRootsAux p K).permCongrHom (finiteFieldFrobPerm p)

theorem finiteFieldFrobPermIn_apply (p : F[X]) (K : Type*)
    [Field K] [Algebra F K]
    [Fact ((p.map (algebraMap F K)).Splits)]
    (x : p.rootSet K) :
    ((finiteFieldFrobPermIn p K x) : K) =
      (x : K) ^ Fintype.card F := by
  let e := Polynomial.Gal.rootsEquivRootsAux p K
  have h := finiteFieldFrobPerm_apply p (e.symm x)
  have hmap := congrArg (algebraMap p.SplittingField K) h
  have he (y : p.rootSet p.SplittingField) :
      ((e y : p.rootSet K) : K) =
        algebraMap p.SplittingField K y.1 := rfl
  rw [map_pow, ← he (e.symm x), e.apply_symm_apply] at hmap
  change ((e ((finiteFieldFrobPerm p) (e.symm x)) : p.rootSet K) : K) = _
  exact hmap

theorem finiteFieldFrobPermIn_isCycle (p : F[X]) (K : Type*)
    [Field K] [Algebra F K]
    [Fact ((p.map (algebraMap F K)).Splits)]
    (hp : Irreducible p) (hdeg : 2 ≤ p.natDegree) :
    (finiteFieldFrobPermIn p K).IsCycle := by
  let e := (Polynomial.Gal.rootsEquivRootsAux p K).symm
  apply isCycle_of_equivariant_equiv e
    (finiteFieldFrobPermIn p K) (finiteFieldFrobPerm p)
  · intro x
    simp only [finiteFieldFrobPermIn, e, Equiv.permCongrHom_coe,
      Equiv.permCongr_apply, Equiv.symm_apply_apply]
  · exact finiteFieldFrobPerm_isCycle p hp hdeg

theorem finiteFieldFrobPermIn_support_card (p : F[X]) (K : Type*)
    [Field K] [Algebra F K]
    [Fact ((p.map (algebraMap F K)).Splits)]
    [DecidableEq (p.rootSet K)]
    (hp : Irreducible p) (hdeg : 2 ≤ p.natDegree) :
    (finiteFieldFrobPermIn p K).support.card = p.natDegree := by
  classical
  exact (support_card_eq_of_equivariant_equiv
    (Polynomial.Gal.rootsEquivRootsAux p K)
    (finiteFieldFrobPerm p) (finiteFieldFrobPermIn p K)
    (fun x => by
      simp only [finiteFieldFrobPermIn, Equiv.permCongrHom_coe,
        Equiv.permCongr_apply, Equiv.symm_apply_apply])).symm.trans
        (finiteFieldFrobPerm_support_card p hp hdeg)

end Biunimodular.F11
