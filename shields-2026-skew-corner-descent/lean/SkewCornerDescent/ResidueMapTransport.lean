/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ResidueTranspose

/-!
# Universal property of the actual affine prime residue

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
A field map on the full coefficient field is compatible with every polynomial
once it agrees on the coefficient ring and kills the actual affine prime.
The nonzero top cofactor supplies the selected generator value. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Agreement on the full coefficient ring and the actual prime equation
forces agreement with the actual residue on every original polynomial. -/
theorem residueMap_comp_eq_of_coefficients {K : Type*} [Field K]
    (γ : OtherField c.top →+* K) (η : Lambda →+* K)
    (hcoeff : ∀ p : OtherPolynomial c.top,
      γ (algebraMap (OtherPolynomial c.top) (OtherField c.top) p) = η (rename Subtype.val p))
    (hprime : η (cellSchur D hD.1) = 0) : γ.comp c.residueMap = η := by
  let ρ := γ.comp c.residueMap
  have hother (f : Lambda) (hf : c.top ∉ f.vars) : ρ f = η f := by
    have hs : f ∈ supported ℚ {j : ℕ+ | j ≠ c.top} := by
      apply mem_supported.mpr
      intro j hj he
      exact hf (he ▸ hj)
    rw [supported_eq_range_rename, AlgHom.mem_range] at hs
    obtain ⟨p, rfl⟩ := hs
    calc
      _ = γ (algebraMap (OtherPolynomial c.top) (OtherField c.top) p) :=
        congrArg γ (c.residueMap_otherPolynomial p)
      _ = _ := hcoeff p
  apply MvPolynomial.ringHom_ext'
  · exact RingHom.ext_rat _ _
  · intro j
    by_cases hj : j = c.top
    · subst j
      have ha := hother c.coefficient c.top_notMem_coefficient
      have hr := hother c.remainder c.top_notMem_remainder
      have hco : c.residueMap c.coefficient ≠ 0 :=
        (c.residueMap_ne_zero_iff c.coefficient).mpr c.not_dvd_coefficient
      have hn : ρ c.coefficient ≠ 0 :=
        (map_ne_zero_iff γ γ.injective).mpr hco
      have hpρ : ρ (cellSchur D hD.1) = 0 := by
        change γ (c.residueMap (cellSchur D hD.1)) = 0
        rw [(c.residueMap_eq_zero_iff _).mpr (dvd_refl _), map_zero]
      have hpη := hprime
      rw [c.prime_eq, affineCoordinate, map_add, map_mul] at hpρ hpη
      rw [← ha, ← hr] at hpη
      exact mul_left_cancel₀ hn (add_right_cancel (hpρ.trans hpη.symm))
    · apply hother (X j)
      simp only [vars_X, Finset.mem_singleton]
      exact Ne.symm hj

end SkewCornerDescent.Matrix.SelectedCoordinate
