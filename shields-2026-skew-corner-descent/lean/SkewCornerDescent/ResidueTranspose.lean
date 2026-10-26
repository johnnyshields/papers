/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SchurInvolutionField
import SkewCornerDescent.Matrix.NormalResidue

/-!
# Actual residue-field transport under Schur involution

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The actual polynomial residue kernel supplies the injectivity needed to extend
whole-diagram transpose to the full coefficient fraction field. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Omitting the selected generator and taking the actual residue is the
canonical embedding of the entire coefficient polynomial ring. -/
theorem residueMap_otherPolynomial (p : OtherPolynomial c.top) :
    c.residueMap (rename Subtype.val p) =
      algebraMap (OtherPolynomial c.top) (OtherField c.top) p := by
  have h : c.residueMap.comp (rename (Subtype.val : {j : ℕ+ // j ≠ c.top} → ℕ+)).toRingHom =
      algebraMap (OtherPolynomial c.top) (OtherField c.top) := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_rat _ _
    · intro j
      change c.residueMap (rename Subtype.val (X j)) = _
      rw [rename_X, c.residueMap_other j.val j.prop]
  exact RingHom.congr_fun h p

variable (d : SelectedCoordinate (transpose D) (isConnectedSkew_transpose hD))

/-- Evaluate every original omitted generator after whole-diagram transpose
in the actual transposed selected-prime residue field. -/
noncomputable def otherPolynomialTranspose : OtherPolynomial c.top →+* OtherField d.top :=
  (d.residueMap.comp schurInvolution.toRingHom).comp
    (rename (Subtype.val : {j : ℕ+ // j ≠ c.top} → ℕ+)).toRingHom

/-- Injectivity comes from the exact actual prime kernel on both sides,
not from an assumed algebraic independence of transformed responses. -/
theorem otherPolynomialTranspose_injective : Function.Injective (c.otherPolynomialTranspose d) := by
  intro p q he
  have hz : c.otherPolynomialTranspose d (p - q) = 0 := by
    rw [map_sub, he, sub_self]
  change d.residueMap (schurInvolution (rename Subtype.val (p - q))) = 0 at hz
  have hd := (d.residueMap_eq_zero_iff _).mp hz
  rw [← schurInvolution_cellSchur hD, schurInvolution_dvd_iff] at hd
  have hc := (c.residueMap_eq_zero_iff _).mpr hd
  rw [c.residueMap_otherPolynomial] at hc
  have hzero : p - q = 0 := (IsFractionRing.injective (OtherPolynomial c.top)
    (OtherField c.top)) (hc.trans (map_zero _).symm)
  exact sub_eq_zero.mp hzero

/-- The full actual coefficient fraction field transports to the transposed
selected-prime residue field. -/
noncomputable def residueTranspose : OtherField c.top →+* OtherField d.top :=
  IsFractionRing.lift (c.otherPolynomialTranspose_injective d)

/-- The field transport retains the complete original polynomial coefficient map. -/
theorem residueTranspose_otherPolynomial (p : OtherPolynomial c.top) :
    c.residueTranspose d (algebraMap (OtherPolynomial c.top) (OtherField c.top) p) =
      d.residueMap (schurInvolution (rename Subtype.val p)) := by
  exact IsFractionRing.lift_algebraMap (c.otherPolynomialTranspose_injective d) p

/-- The produced residue-field map agrees with whole-diagram transpose on
every polynomial omitting the selected generator, including all higher generators. -/
theorem residueTranspose_residueMap_of_notMem (f : Lambda) (hf : c.top ∉ f.vars) :
    c.residueTranspose d (c.residueMap f) = d.residueMap (schurInvolution f) := by
  have hs : f ∈ supported ℚ {j : ℕ+ | j ≠ c.top} := by
    apply mem_supported.mpr
    intro j hj he
    exact hf (he ▸ hj)
  rw [supported_eq_range_rename, AlgHom.mem_range] at hs
  obtain ⟨p, rfl⟩ := hs
  calc
    _ = c.residueTranspose d
        (algebraMap (OtherPolynomial c.top) (OtherField c.top) p) :=
      congrArg (c.residueTranspose d) (c.residueMap_otherPolynomial p)
    _ = _ := c.residueTranspose_otherPolynomial d p

/-- The full actual residue commutes with whole-diagram transpose even on
the selected generator. Its affine prime equation and nonzero cofactor produce
that last generator value; it is not an assumed compatibility. -/
theorem residueTranspose_residueMap (f : Lambda) :
    c.residueTranspose d (c.residueMap f) = d.residueMap (schurInvolution f) := by
  let ρ := (c.residueTranspose d).comp c.residueMap
  let σ := d.residueMap.comp schurInvolution.toRingHom
  have hmaps : ρ = σ := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_rat _ _
    · intro j
      by_cases hj : j = c.top
      · subst j
        have ha : ρ c.coefficient = σ c.coefficient :=
          c.residueTranspose_residueMap_of_notMem d c.coefficient c.top_notMem_coefficient
        have hr : ρ c.remainder = σ c.remainder :=
          c.residueTranspose_residueMap_of_notMem d c.remainder c.top_notMem_remainder
        have hco : c.residueMap c.coefficient ≠ 0 :=
          (c.residueMap_ne_zero_iff c.coefficient).mpr c.not_dvd_coefficient
        have hn : ρ c.coefficient ≠ 0 :=
          (map_ne_zero_iff (c.residueTranspose d) (c.residueTranspose d).injective).mpr hco
        have hpρ : ρ (cellSchur D hD.1) = 0 := by
          change c.residueTranspose d (c.residueMap (cellSchur D hD.1)) = 0
          rw [(c.residueMap_eq_zero_iff _).mpr (dvd_refl _), map_zero]
        have hpσ : σ (cellSchur D hD.1) = 0 := by
          change d.residueMap (schurInvolution (cellSchur D hD.1)) = 0
          rw [schurInvolution_cellSchur hD]
          exact (d.residueMap_eq_zero_iff _).mpr (dvd_refl _)
        rw [c.prime_eq, affineCoordinate, map_add, map_mul] at hpρ hpσ
        rw [← ha, ← hr] at hpσ
        exact mul_left_cancel₀ hn (add_right_cancel (hpρ.trans hpσ.symm))
      · have hx : c.top ∉ (X j : Lambda).vars := by
          simp only [vars_X, Finset.mem_singleton]
          exact Ne.symm hj
        exact c.residueTranspose_residueMap_of_notMem d (X j) hx
  exact RingHom.congr_fun hmaps f

end SkewCornerDescent.Matrix.SelectedCoordinate
