/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ResidueMapTransport

/-!
# Invertible whole-diagram transport of actual residue fields

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The two actual selected-prime residue kernels construct both coefficient-field
maps. Their full polynomial compatibility proves they are inverse. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)
variable (d : SelectedCoordinate (transpose D) (isConnectedSkew_transpose hD))

/-- Reverse whole-diagram transpose on the complete target coefficient ring. -/
noncomputable def otherPolynomialTransposeBack : OtherPolynomial d.top →+* OtherField c.top :=
  (c.residueMap.comp schurInvolution.toRingHom).comp
    (rename (Subtype.val : {j : ℕ+ // j ≠ d.top} → ℕ+)).toRingHom

/-- The actual selected-prime kernels prove reverse coefficient injectivity. -/
theorem otherPolynomialTransposeBack_injective :
    Function.Injective (c.otherPolynomialTransposeBack d) := by
  intro p q he
  have hz : c.otherPolynomialTransposeBack d (p - q) = 0 := by
    rw [map_sub, he, sub_self]
  change c.residueMap (schurInvolution (rename Subtype.val (p - q))) = 0 at hz
  have hc := (c.residueMap_eq_zero_iff _).mp hz
  have hd := map_dvd schurInvolution hc
  rw [schurInvolution_cellSchur hD,
    schurInvolution_involutive (rename Subtype.val (p - q))] at hd
  have hzero := (d.residueMap_eq_zero_iff _).mpr hd
  rw [d.residueMap_otherPolynomial] at hzero
  have hpq : p - q = 0 := (IsFractionRing.injective (OtherPolynomial d.top)
    (OtherField d.top)) (hzero.trans (map_zero _).symm)
  exact sub_eq_zero.mp hpq

/-- Reverse field transport constructed from its proved injective coefficient map. -/
noncomputable def residueTransposeBack : OtherField d.top →+* OtherField c.top :=
  IsFractionRing.lift (c.otherPolynomialTransposeBack_injective d)

/-- Reverse transport agrees with the full target polynomial coefficient ring. -/
theorem residueTransposeBack_otherPolynomial (p : OtherPolynomial d.top) :
    c.residueTransposeBack d (algebraMap (OtherPolynomial d.top) (OtherField d.top) p) =
      c.residueMap (schurInvolution (rename Subtype.val p)) := by
  exact IsFractionRing.lift_algebraMap (c.otherPolynomialTransposeBack_injective d) p

/-- The reverse map commutes with the full actual target polynomial residue,
including its selected generator. -/
theorem residueTransposeBack_residueMap (f : Lambda) :
    c.residueTransposeBack d (d.residueMap f) = c.residueMap (schurInvolution f) := by
  have h := d.residueMap_comp_eq_of_coefficients (c.residueTransposeBack d)
    (c.residueMap.comp schurInvolution.toRingHom)
    (fun p => c.residueTransposeBack_otherPolynomial d p) (by
      change c.residueMap (schurInvolution
        (cellSchur (transpose D) (isSkew_transpose hD.1))) = 0
      rw [← schurInvolution_cellSchur hD,
        schurInvolution_involutive (cellSchur D hD.1)]
      exact (c.residueMap_eq_zero_iff _).mpr (dvd_refl _))
  exact RingHom.congr_fun h f

/-- Reverse then forward transport is the identity on the entire source field. -/
theorem residueTranspose_left_inverse :
    (c.residueTransposeBack d).comp (c.residueTranspose d) = RingHom.id (OtherField c.top) := by
  apply IsFractionRing.ringHom_ext (A := OtherPolynomial c.top)
  intro p
  change c.residueTransposeBack d
    (c.residueTranspose d (algebraMap (OtherPolynomial c.top) (OtherField c.top) p)) = _
  rw [c.residueTranspose_otherPolynomial d, c.residueTransposeBack_residueMap d,
    schurInvolution_involutive (rename Subtype.val p), c.residueMap_otherPolynomial]
  rfl

/-- Forward then reverse transport is the identity on the entire target field. -/
theorem residueTranspose_right_inverse :
    (c.residueTranspose d).comp (c.residueTransposeBack d) = RingHom.id (OtherField d.top) := by
  apply IsFractionRing.ringHom_ext (A := OtherPolynomial d.top)
  intro p
  change c.residueTranspose d
    (c.residueTransposeBack d (algebraMap (OtherPolynomial d.top) (OtherField d.top) p)) = _
  rw [c.residueTransposeBack_otherPolynomial d, c.residueTranspose_residueMap d,
    schurInvolution_involutive (rename Subtype.val p), d.residueMap_otherPolynomial]
  rfl

/-- The full actual selected-prime coefficient fields are isomorphic under
whole-diagram transpose. Both inverse maps are produced, not assumed. -/
noncomputable def residueTransposeEquiv : OtherField c.top ≃+* OtherField d.top :=
  RingEquiv.ofRingHom (c.residueTranspose d) (c.residueTransposeBack d)
    (c.residueTranspose_right_inverse d) (c.residueTranspose_left_inverse d)

end SkewCornerDescent.Matrix.SelectedCoordinate
