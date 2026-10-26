/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalDerivative

/-!
# Recognition of protected original generator tops at residue

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). A
nonzero lower coefficient multiplying a protected surviving generator cannot
vanish or move into the strict lower field. Equal such expressions therefore
identify their original generator indices. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The strict lower remainder cannot cancel the protected affine top. -/
theorem residue_protected_affine_not_lower (J : ℕ+) (hJ : c.top < J)
    (a R : OtherField c.top) (ha : a ∈ residueLowerField c.top J)
    (ha0 : a ≠ 0) (hR : R ∈ residueLowerField c.top J) :
    residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * a + R ∉ residueLowerField c.top J := by
  have hd : residueGeneratorDeriv c.top ⟨J, ne_of_gt hJ⟩
      (residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * a + R) = a := by
    rw [map_add, Derivation.leibniz, residueGeneratorDeriv_lower c.top ⟨J, ne_of_gt hJ⟩ ha,
      residueGeneratorDeriv_lower c.top ⟨J, ne_of_gt hJ⟩ hR, residueGeneratorDeriv_generator]
    simp only [ite_true, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero]
  intro hx
  have hz := residueGeneratorDeriv_lower c.top ⟨J, ne_of_gt hJ⟩ hx
  rw [hd] at hz
  exact ha0 hz

/-- In particular every complete coefficient with this protected top is nonzero. -/
theorem residue_protected_affine_ne_zero (J : ℕ+) (hJ : c.top < J)
    (a R : OtherField c.top) (ha : a ∈ residueLowerField c.top J)
    (ha0 : a ≠ 0) (hR : R ∈ residueLowerField c.top J) :
    residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * a + R ≠ 0 := by
  intro hz
  apply c.residue_protected_affine_not_lower J hJ a R ha ha0 hR
  rw [hz]
  exact (residueLowerField c.top J).zero_mem

/-- An expression with smaller protected index cannot equal one with a larger
nonzero protected index. Every lower fraction and its denominator is retained. -/
theorem residue_affine_distinct_higher_top (J K : ℕ+) (hJ : c.top < J) (hJK : J < K)
    (a R b T : OtherField c.top)
    (ha : a ∈ residueLowerField c.top J) (hR : R ∈ residueLowerField c.top J)
    (hb : b ∈ residueLowerField c.top K) (hb0 : b ≠ 0) (hT : T ∈ residueLowerField c.top K) :
    residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * a + R ≠
      residueGenerator c.top ⟨K, ne_of_gt (hJ.trans hJK)⟩ * b + T := by
  have hg : residueGenerator c.top ⟨J, ne_of_gt hJ⟩ ∈ residueLowerField c.top K := by
    have h := c.residue_other_mem_lower K J (ne_of_gt hJ) hJK
    rw [c.residueMap_other J (ne_of_gt hJ)] at h
    exact h
  have hlow : residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * a + R ∈ residueLowerField c.top K :=
    (residueLowerField c.top K).add_mem
      ((residueLowerField c.top K).mul_mem hg (residueLowerField_mono hJK.le ha))
      (residueLowerField_mono hJK.le hR)
  intro he
  rw [he] at hlow
  exact c.residue_protected_affine_not_lower K (hJ.trans hJK) b T hb hb0 hT hlow

/-- Equal complete protected affine coefficients identify the original top,
not merely a numeric value at one specialization. -/
theorem residue_protected_affine_top_unique (J K : ℕ+) (hJ : c.top < J) (hK : c.top < K)
    (a R b T : OtherField c.top)
    (ha : a ∈ residueLowerField c.top J) (ha0 : a ≠ 0) (hR : R ∈ residueLowerField c.top J)
    (hb : b ∈ residueLowerField c.top K) (hb0 : b ≠ 0) (hT : T ∈ residueLowerField c.top K)
    (he : residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * a + R =
      residueGenerator c.top ⟨K, ne_of_gt hK⟩ * b + T) : J = K := by
  rcases lt_trichotomy J K with h | h | h
  · exact (c.residue_affine_distinct_higher_top J K hJ h a R b T ha hR hb hb0 hT he).elim
  · exact h
  · exact (c.residue_affine_distinct_higher_top K J hK h b T a R hb hT ha ha0 hR he.symm).elim

end SkewCornerDescent.Matrix.SelectedCoordinate
