/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryCrossingCounts
import SkewClassInflation.RegroupSigns

/-!
# The actual common-beta deletion sign is positive

The parity assertion in `eq:boundary-lowest-degree` of
`shields-2026-skew-class-inflation.tex`.  Each restored suffix beta has
retained crossing counts `s-1` and `s+1`; the actual row and column
regrouping signs therefore multiply to one.  Sorry-free.
-/

namespace SkewClassInflation.BoundaryParameters

open SkewJacobiNegative SkewJacobiNegative.BetaDiagram
open SkewJacobiNegative.BetaEndpointCounts
open scoped BigOperators

variable (B : BoundaryParameters)

/-- The actual parent's row and column deletion permutations have product sign one. -/
theorem restoredParent_deletionSign_one (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) :
    let C := B.core M hM T
    let Z := B.commonBetas T
    let hZ := B.commonBetas_available M hM T hT
    let hr := C.available_disjoint_rows Z hZ
    let hc := C.available_disjoint_cols Z hZ
    C.deletionSign Z hr hc (B.restoredParent M hM T hT)
      (C.restore_rowSet _ _ _ _) (C.restore_colSet _ _ _ _) = 1 := by
  classical
  intro C Z hZ hr hc
  let D : BetaDiagram (M + 1 + Z.card) := B.restoredParent M hM T hT
  have er : D.rowSet = C.rowSet ∪ Z := C.restore_rowSet _ _ _ _
  have ec : D.colSet = C.colSet ∪ Z := C.restore_colSet _ _ _ _
  change C.deletionSign Z hr hc D er ec = 1
  rw [deletionSign_count]
  apply Finset.prod_eq_one
  intro j _
  have hj : descending Z rfl j ∈ Z := descending_mem Z rfl j
  obtain ⟨s, hs, hz⟩ := Finset.mem_image.mp hj
  have hsB := Finset.mem_Ioo.mp (hT hs)
  have hrow := B.core_row_crossing_count M hM T hT s hs
  have hcol := B.core_col_crossing_count M hM T hT s hs
  rw [hz] at hrow hcol
  rw [hrow, hcol]
  have he : s - 1 + (s + 1) = 2 * s := by omega
  rw [he, pow_mul]
  have htwo : (-1 : ℤˣ) ^ 2 = 1 := by decide
  rw [htwo, one_pow]

/-- The lowest component is exactly the core function, without an unresolved deletion unit. -/
theorem restoredParent_lowest_component (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) :
    MvPolynomial.homogeneousComponent (M + 1) (B.restoredParent M hM T hT).schur =
      (B.core M hM T).schur := by
  let C := B.core M hM T
  let Z := B.commonBetas T
  have hZ := B.commonBetas_available M hM T hT
  have hr := C.available_disjoint_rows Z hZ
  have hc := C.available_disjoint_cols Z hZ
  let D := B.restoredParent M hM T hT
  have er : D.rowSet = C.rowSet ∪ Z := C.restore_rowSet _ _ _ _
  have ec : D.colSet = C.colSet ∪ Z := C.restore_colSet _ _ _ _
  have he := (C.restoration_first_coefficients (B.core_zeroFree M hM T) Z hr hc D er ec).1
  rw [ordinaryComponent_eq_homogeneousComponent] at he
  have hs : C.deletionSign Z hr hc D er ec = 1 :=
    B.restoredParent_deletionSign_one M hM T hT
  rw [hs] at he
  simpa only [Units.val_one, Int.cast_one, one_mul] using he

/-- Every component below the displayed core order vanishes on the actual restored parent. -/
theorem restoredParent_component_below (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) (d : ℕ) (hd : d < M + 1) :
    MvPolynomial.homogeneousComponent d (B.restoredParent M hM T hT).schur = 0 := by
  let C := B.core M hM T
  let Z := B.commonBetas T
  have hZ := B.commonBetas_available M hM T hT
  have hr := C.available_disjoint_rows Z hZ
  have hc := C.available_disjoint_cols Z hZ
  let D := B.restoredParent M hM T hT
  have er : D.rowSet = C.rowSet ∪ Z := C.restore_rowSet _ _ _ _
  have ec : D.colSet = C.colSet ∪ Z := C.restore_colSet _ _ _ _
  rw [← ordinaryComponent_eq_homogeneousComponent]
  exact C.restoration_coeff_below (B.core_zeroFree M hM T) Z hr hc D er ec d hd

end SkewClassInflation.BoundaryParameters
