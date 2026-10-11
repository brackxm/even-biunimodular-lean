/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FourierTrace
import Biunimodular.F11.InvolutionEigenspaceDimension
import Biunimodular.F11.Even11FixedSliceQuotientGeometry

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

def even11RealEmbed : Even6 ℝ →ₗ[ℝ] Even6 ℂ where
  toFun x i := (x i : ℂ)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

def even11RealPart : Even6 ℂ →ₗ[ℝ] Even6 ℝ where
  toFun x i := (x i).re
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

def even11FourierReal : Module.End ℝ (Even6 ℝ) :=
  even11RealPart.comp ((even11FourierNormalized.restrictScalars ℝ).comp even11RealEmbed)

theorem even11RealEmbed_injective : Function.Injective even11RealEmbed := by
  intro x y h
  funext i
  exact Complex.ofReal_injective (congrFun h i)

theorem even11FourierReal_embed (x : Even6 ℝ) :
    even11RealEmbed (even11FourierReal x) = even11FourierNormalized (even11RealEmbed x) := by
  have hc : even11Conj (even11RealEmbed x) = even11RealEmbed x := by
    funext i
    simp [even11Conj, even11RealEmbed]
  have h := even11FourierNormalized_conj (even11RealEmbed x)
  rw [hc] at h
  funext i
  have hi := congrArg Complex.im (congrFun h i)
  change -(even11FourierNormalized (even11RealEmbed x) i).im =
    (even11FourierNormalized (even11RealEmbed x) i).im at hi
  apply Complex.ext
  · rfl
  · change 0 = (even11FourierNormalized (even11RealEmbed x) i).im
    linarith

theorem even11FourierReal_sq (x : Even6 ℝ) : even11FourierReal (even11FourierReal x) = x := by
  apply even11RealEmbed_injective
  rw [even11FourierReal_embed, even11FourierReal_embed, even11FourierNormalized_sq]

theorem even11FourierReal_trace : LinearMap.trace ℝ (Even6 ℝ) even11FourierReal = 0 := by
  classical
  have hs (j : Fin 6) : even11RealEmbed (Pi.single j (1 : ℝ)) = Pi.single j (1 : ℂ) := by
    funext i
    simp only [even11RealEmbed, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
    split_ifs <;> rfl
  have ht := congrArg Complex.re even11FourierNormalized_trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 6))] at ht
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 6))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_apply] at ht ⊢
  change Complex.reLm (∑ j : Fin 6, even11FourierNormalized (Pi.single j 1) j) = 0 at ht
  rw [map_sum] at ht
  change (∑ j : Fin 6, (even11FourierNormalized (Pi.single j 1) j).re) = 0 at ht
  change (∑ j : Fin 6, (even11FourierNormalized (even11RealEmbed (Pi.single j 1)) j).re) = 0
  simpa only [hs] using ht

abbrev Even11FourierRealPlus := even11FourierReal.eigenspace 1
abbrev Even11FourierRealMinus := even11FourierReal.eigenspace (-1)

theorem even11FourierReal_eigenspaces_dimension :
    Module.finrank ℝ Even11FourierRealPlus = 3 ∧
      Module.finrank ℝ Even11FourierRealMinus = 3 :=
  involution_eigenspaces_finrank_three even11FourierReal even11FourierReal_sq
    even11FourierReal_trace (by simp [Even6])

/-- Real bases of the two actual three-dimensional Fourier eigenspaces. -/
def even11FourierRealPlusBasis : Module.Basis (Fin 3) ℝ Even11FourierRealPlus :=
  Module.finBasisOfFinrankEq ℝ _ even11FourierReal_eigenspaces_dimension.1

def even11FourierRealMinusBasis : Module.Basis (Fin 3) ℝ Even11FourierRealMinus :=
  Module.finBasisOfFinrankEq ℝ _ even11FourierReal_eigenspaces_dimension.2

theorem even11Fourier_real_imag (x y : Even6 ℝ) :
    even11FourierNormalized (even11RealEmbed x + Complex.I • even11RealEmbed y) =
      even11RealEmbed (even11FourierReal x) +
        Complex.I • even11RealEmbed (even11FourierReal y) := by
  rw [map_add, map_smul, even11FourierReal_embed, even11FourierReal_embed]

/-- The the Fourier-conjugate real slice is precisely `E₊ + i E₋`. -/
theorem even11Fourier_conjugate_slice_iff (x y : Even6 ℝ) :
    even11FourierNormalized (even11RealEmbed x + Complex.I • even11RealEmbed y) =
        even11Conj (even11RealEmbed x + Complex.I • even11RealEmbed y) ↔
      x ∈ Even11FourierRealPlus ∧ y ∈ Even11FourierRealMinus := by
  rw [even11Fourier_real_imag]
  simp only [Module.End.mem_eigenspace_iff, one_smul, neg_one_smul]
  constructor
  · intro h
    constructor
    · funext i
      have hi := congrArg Complex.re (congrFun h i)
      simpa [even11RealEmbed, even11Conj, smul_eq_mul] using hi
    · funext i
      have hi := congrArg Complex.im (congrFun h i)
      simpa [even11RealEmbed, even11Conj, smul_eq_mul] using hi
  · rintro ⟨hx, hy⟩
    rw [hx, hy]
    funext i
    apply Complex.ext <;> simp [even11RealEmbed, even11Conj, smul_eq_mul]

end
end Biunimodular.F11
