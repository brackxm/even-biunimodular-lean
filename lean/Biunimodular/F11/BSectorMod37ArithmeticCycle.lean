/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorMonicFiniteCycles
import Biunimodular.F11.BSectorModularCycleLift

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

private instance : Fact (Nat.Prime 37) := ⟨by decide⟩
private noncomputable instance :
    DecidableEq (invariantBMonicTransform.rootSet BIntegers) := Classical.decEq _

/-- An actual arithmetic Frobenius element at 37 induces a seven-cycle on
the eight integral roots of the monic B transform. -/
theorem exists_bMonic_seven_cycle :
    ∃ σ : BOriginalQ.Gal,
      (MulAction.toPermHom BOriginalQ.Gal
        (invariantBMonicTransform.rootSet BIntegers) σ).IsCycle ∧
      (MulAction.toPermHom BOriginalQ.Gal
        (invariantBMonicTransform.rootSet BIntegers) σ).support.card = 7 := by
  classical
  obtain ⟨Q, hmax, hQ, hunder, σ, hσ⟩ :=
    exists_bMonic_arithFrob_at_prime 37 (by decide)
  let : Q.IsMaximal := hmax
  let : Q.IsPrime := hQ
  let : Field (BIntegers ⧸ Q) := Ideal.Quotient.field Q
  let : CharP (BIntegers ⧸ Q) 37 := bResidue_charP 37 Q hunder
  let : Algebra (ZMod 37) (BIntegers ⧸ Q) := ZMod.algebra _ 37
  let K := BIntegers ⧸ Q
  let q : (ZMod 37)[X] := (X + C 36) * B37monicSeven
  have hqeq : q = invariantBMonicTransform.map (Int.castRingHom (ZMod 37)) := by
    simpa only [q, Polynomial.C_ofNat] using bMonic_mod37_factor.symm
  have hcomp : (algebraMap (ZMod 37) K).comp (Int.castRingHom (ZMod 37)) =
      algebraMap ℤ K := by
    ext n
    simp
  have hsplitZ : (invariantBMonicTransform.map (algebraMap ℤ K)).Splits := by
    have hs := bMonicInteger_splits.map (Ideal.Quotient.mk Q)
    have hcompInt : (Ideal.Quotient.mk Q).comp (algebraMap ℤ BIntegers) =
        algebraMap ℤ K := by
      ext n
      rfl
    simpa only [Polynomial.map_map, hcompInt] using hs
  have hsplit : (q.map (algebraMap (ZMod 37) K)).Splits := by
    rw [hqeq, Polynomial.map_map, hcomp]
    exact hsplitZ
  let : Fact ((q.map (algebraMap (ZMod 37) K)).Splits) := ⟨hsplit⟩
  let g := finiteFieldFrobPermIn q K
  have hcycle : g.IsCycle ∧ g.support.card = 7 := by
    exact bMonic_mod37_frob_cycle K
  have hpow (x : q.rootSet K) : (g x).1 = (x.1 : K) ^ 37 := by
    simpa only [g, ZMod.card] using finiteFieldFrobPermIn_apply q K x
  have hset := bMonic_modp_rootSet_eq 37 K q hqeq
  exact ⟨σ, bMonic_lift_residue_cycle 37 Q q hunder
    bMonic_mod37_separable σ hσ hset g hpow hcycle.1 7 hcycle.2⟩

end Biunimodular.F11
