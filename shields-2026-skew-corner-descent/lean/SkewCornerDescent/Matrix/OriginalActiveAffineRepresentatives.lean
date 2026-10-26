/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ConstantActiveRoots
import SkewCornerDescent.Matrix.OriginalExposedPolynomials

/-!
# Active affine identities from original residue responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`, `lem:exposure`).
An equality of the full original monic response functions yields the cleared polynomial
identity used to compare active roots in different chambers. The common denominator may
be nonconstant; no specialization of the entire original residue field is used. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing SelectedCoordinate

/-- An injective coefficient map reflects the cleared affine relation between two regular
fractions. This is the representation seam between a full field identity and its slice. -/
theorem fraction_affine_cross_identity {R F : Type*} [CommRing R] [Field F]
    (ι : R →+* F) (hι : Function.Injective ι) (p q base cap scaleDen c : R)
    (hq : ι q ≠ 0) (hscale : ι scaleDen ≠ 0)
    (hidentity : ι p / ι q = ι base / ι scaleDen - ι c * (ι cap / ι scaleDen)) :
    p * scaleDen = (base - c * cap) * q := by
  rw [← mul_div_assoc, ← sub_div] at hidentity
  have hcross := (div_eq_div_iff hq hscale).mp hidentity
  apply hι
  simpa only [map_mul, map_sub] using hcross

/-- The active source identity, with its common monic top retained on both sides, produces
the actual cleared real polynomial identity needed by the two-chamber root comparison. -/
theorem original_active_affine_representative (N K : ℕ+) (hKN : K ≠ N)
    (p q base cap scaleDen : OtherPolynomial N) (label : ℚ)
    (hq : q ≠ 0) (hscale : scaleDen ≠ 0)
    (hidentity :
      let ι := algebraMap (OtherPolynomial N) (OtherField N)
      residueGenerator N ⟨K, hKN⟩ + ι p / ι q =
        residueGenerator N ⟨K, hKN⟩ + ι base / ι scaleDen -
          (label : OtherField N) * (ι cap / ι scaleDen)) :
    realResiduePolynomial N p * realResiduePolynomial N scaleDen =
      (realResiduePolynomial N base - MvPolynomial.C (label : ℝ) *
        realResiduePolynomial N cap) * realResiduePolynomial N q := by
  let ι := algebraMap (OtherPolynomial N) (OtherField N)
  have hscalar : ι (MvPolynomial.C label) = (label : OtherField N) := by
    simpa only [Rat.cast_id, RingHom.comp_apply] using map_ratCast (ι.comp MvPolynomial.C) label
  have hquot : ι p / ι q = ι base / ι scaleDen -
      ι (MvPolynomial.C label) * (ι cap / ι scaleDen) := by
    apply add_left_cancel (a := residueGenerator N ⟨K, hKN⟩)
    simpa only [hscalar, add_sub_assoc] using hidentity
  have hcross := fraction_affine_cross_identity ι (IsFractionRing.injective _ _)
    p q base cap scaleDen (MvPolynomial.C label)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hscale) hquot
  have hrealC : realResiduePolynomial N (MvPolynomial.C label) =
      MvPolynomial.C (label : ℝ) := by
    simp [realResiduePolynomial]
  simpa only [map_mul, map_sub, hrealC] using congrArg (realResiduePolynomial N) hcross

end SkewCornerDescent.Matrix
