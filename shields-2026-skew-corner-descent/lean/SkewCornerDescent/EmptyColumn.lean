/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.EmptyHorizontal

/-!
# Empty column composition in literal cell coordinates

Supports `shields-2026-skew-corner-descent.tex`, «The full-window boundary»
(`lem:boundary-full-window`).

The antitransposed normalized row is a column with increasing content. Its composition
with the legal horizontal empty mark uses the vertical displacement `vH E - eCell`.
No separate illegal vertical empty mark is introduced.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- The normalized column with one cell on each of its increasing content diagonals. -/
def verticalColumn (m : ℕ) : Diagram := antitranspose (horizontalRow m)

/-- Literal column membership, including its orientation. -/
theorem mem_verticalColumn {m : ℕ} {x : ℤ × ℤ} :
    x ∈ verticalColumn m ↔ x.2 = 0 ∧ 0 ≤ -x.1 ∧ -x.1 < m := by
  simp only [verticalColumn, mem_antitranspose, mem_horizontalRow, neg_eq_zero]

/-- The normalized column is connected skew for every positive length. -/
theorem verticalColumn_isConnectedSkew {m : ℕ} (hm : 1 ≤ m) :
    IsConnectedSkew (verticalColumn m) :=
  isConnectedSkew_antitranspose (isConnectedSkew_horizontalRow hm)

/-- Column cells use the actual vertical empty-overlap displacement. -/
theorem emptyMarkH_origin_verticalColumn (E : Diagram) {m : ℕ} {x : ℤ × ℤ}
    (hx : x ∈ verticalColumn m) :
    (emptyMarkH E).origin (verticalColumn m) x = (-x.1) • (vH E - eCell) := by
  have hx0 := (mem_verticalColumn.mp hx).1
  simp only [MarkedInner.origin, emptyMarkH, content, hx0, zero_sub,
    smul_sub, neg_smul, sub_neg_eq_add]

/-- The actual empty column composition is the complete union of vertical-reading copies. -/
theorem compose_empty_verticalColumn (E : Diagram) {m : ℕ} (hm : 1 ≤ m) :
    (emptyMarkH E).compose (verticalColumn m) =
      (Finset.range m).biUnion fun j => translate ((j : ℤ) • (vH E - eCell)) E := by
  have hne := (verticalColumn_isConnectedSkew hm).2.1
  ext x
  rw [MarkedInner.compose_of_ordinary hne
    (by simp [emptyMarkH, AttachCase.IsMixed])]
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨d, hd, hx⟩
    obtain ⟨hd0, hdl, hdu⟩ := mem_verticalColumn.mp hd
    refine ⟨(-d.1).toNat, by omega, ?_⟩
    rw [emptyMarkH_origin_verticalColumn E hd] at hx
    simpa only [emptyMarkH, Int.toNat_of_nonneg hdl] using hx
  · rintro ⟨j, hj, hx⟩
    have hd : (-(j : ℤ), 0) ∈ verticalColumn m :=
      mem_verticalColumn.mpr ⟨rfl, by omega, by omega⟩
    refine ⟨(-(j : ℤ), 0), hd, ?_⟩
    rw [emptyMarkH_origin_verticalColumn E hd]
    simpa only [emptyMarkH, neg_neg] using hx

/-- The literal row outer has exactly the prescribed number of cells. -/
theorem horizontalRow_card (m : ℕ) : (horizontalRow m).card = m := by
  rw [horizontalRow, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),
    Int.card_Ico]
  simp only [sub_zero, Int.toNat_natCast]

/-- The literal column outer has exactly the prescribed number of cells. -/
theorem verticalColumn_card (m : ℕ) : (verticalColumn m).card = m := by
  have hinj : Function.Injective (fun x : ℤ × ℤ => (-x.2, -x.1)) := by
    intro x y h
    have hrow := congrArg Prod.snd h
    have hcol := congrArg Prod.fst h
    exact Prod.ext (neg_injective hrow) (neg_injective hcol)
  rw [verticalColumn, antitranspose, Finset.card_image_of_injective _ hinj,
    horizontalRow_card]

end SkewCornerDescent
