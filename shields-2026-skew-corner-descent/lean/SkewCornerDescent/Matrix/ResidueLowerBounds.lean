/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ResidueProtectedGenerator
import SkewCornerDescent.Matrix.OriginalDenominators

/-!
# Lower generator bounds after the actual prime residue

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:residue-classifier`). The normal
relation eliminates only the selected generator, through its produced lower coefficient
and remainder. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

noncomputable local instance (N : ℕ+) : Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- A polynomial supported in specified generators maps into any subfield containing them. -/
theorem supported_map_mem_subfield {F : Type*} [Field F] [CharZero F]
    (f : Lambda →+* F) (S : Subfield F) (s : Set ℕ+)
    (hX : ∀ j ∈ s, f (X j) ∈ S) {p : Lambda} (hp : p ∈ supported ℚ s) : f p ∈ S := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨j, hj, rfl⟩ := hp
    exact hX j hj
  | algebraMap q =>
    have he := map_ratCast (f.comp (MvPolynomial.C : ℚ →+* Lambda)) q
    change f (C q) = (q : F) at he
    change f (C q) ∈ S
    rw [he]
    exact SubfieldClass.ratCast_mem S q
  | add p q _ _ hp hq =>
    rw [map_add]
    exact S.add_mem hp hq
  | mul p q _ _ hp hq =>
    rw [map_mul]
    exact S.mul_mem hp hq

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every surviving smaller original generator belongs to the stated residue field. -/
theorem residue_other_mem_lower (K j : ℕ+) (hj : j ≠ c.top) (hK : j < K) :
    c.residueMap (X j) ∈ residueLowerField c.top K := by
  rw [c.residueMap_other j hj]
  apply IntermediateField.subset_adjoin ℚ
  exact ⟨⟨j, hj⟩, hK, rfl⟩

/-- The produced cofactor and remainder already lie strictly below the selected top at residue. -/
theorem residue_lower_polynomial {p : Lambda}
    (hp : p ∈ supported ℚ {j : ℕ+ | j < c.top}) :
    c.residueMap p ∈ residueLowerField c.top c.top :=
  supported_map_mem_subfield c.residueMap _ _
    (fun j hj => c.residue_other_mem_lower c.top j (ne_of_lt hj) hj) hp

/-- The actual selected relation solves its original generator, with a nonzero cofactor. -/
theorem residue_top_eq : c.residueMap (X c.top) =
    -c.residueMap c.remainder / c.residueMap c.coefficient := by
  have he : c.residueMap (cellSchur D hD.1) = 0 :=
    (c.residueMap_eq_zero_iff _).mpr dvd_rfl
  rw [c.prime_eq, affineCoordinate, map_add, map_mul] at he
  have hn := (c.residueMap_ne_zero_iff _).mpr c.not_dvd_coefficient
  apply (eq_div_iff hn).mpr
  linear_combination he

/-- The original selected generator becomes a rational function of strictly smaller ones. -/
theorem residue_top_mem_lower : c.residueMap (X c.top) ∈ residueLowerField c.top c.top := by
  rw [c.residue_top_eq]
  exact (residueLowerField c.top c.top).div_mem
    ((residueLowerField c.top c.top).neg_mem (c.residue_lower_polynomial c.remainder_lower))
    (c.residue_lower_polynomial c.coefficient_lower)

/-- Increasing the surviving generator ceiling embeds the residue lower fields. -/
theorem residueLowerField_mono {N K L : ℕ+} (h : K ≤ L) :
    residueLowerField N K ≤ residueLowerField N L := by
  apply IntermediateField.adjoin.mono
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, lt_of_lt_of_le hj h, rfl⟩

/-- Every polynomial below a protected top stays below it after the actual normal substitution. -/
theorem residue_supported_below (K : ℕ+) (hK : c.top < K) {p : Lambda}
    (hp : p ∈ supported ℚ {j : ℕ+ | j < K}) :
    c.residueMap p ∈ residueLowerField c.top K := by
  apply supported_map_mem_subfield c.residueMap _ _ _ hp
  intro j hj
  by_cases he : j = c.top
  · subst j
    exact residueLowerField_mono hK.le c.residue_top_mem_lower
  · exact c.residue_other_mem_lower K j he hj

/-- Every actual smaller matrix entry remains below the protected generator at residue. -/
theorem residue_hh_mem_lower (K : ℕ+) (hK : c.top < K) (z : ℤ) (hz : z < (K : ℤ)) :
    c.residueMap (hh z) ∈ residueLowerField c.top K := by
  apply c.residue_supported_below K hK
  by_cases hn : z < 0
  · rw [hh_of_neg hn]
    exact Subalgebra.zero_mem _
  by_cases h0 : z = 0
  · rw [h0, hh_zero]
    exact Subalgebra.one_mem _
  let j : ℕ+ := ⟨z.toNat, by omega⟩
  have hj : (j : ℤ) = z := Int.toNat_of_nonneg (by omega)
  rw [← hj, hh_pnat]
  apply X_mem_supported.mpr
  change z.toNat < (K : ℕ)
  omega

/-- A polynomial using indices at most the selected top becomes strictly lower at residue. -/
theorem residue_span_mem_lower {p : Lambda} (hp : polynomialSpan p ≤ (c.top : ℕ)) :
    c.residueMap p ∈ residueLowerField c.top c.top := by
  apply supported_map_mem_subfield c.residueMap _ {j : ℕ+ | j ≤ c.top} _ _
  · intro j hj
    by_cases he : j = c.top
    · subst j
      exact c.residue_top_mem_lower
    · exact c.residue_other_mem_lower c.top j he (lt_of_le_of_ne hj he)
  · apply mem_supported.mpr
    intro j hj
    exact (Finset.le_sup hj).trans hp

end SelectedCoordinate
end SkewCornerDescent.Matrix
