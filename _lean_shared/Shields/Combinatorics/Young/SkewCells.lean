/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Intervals
import Shields.Combinatorics.Young.JacobiTrudi

/-!
# The cells of a skew shape, and its rows and columns as words

A skew shape `λ / μ` lying inside `m` rows, and the bounded tableaux of one.  Everything
here is stated at every `m`, and the base cases that instantiate it at `m = 2` are
`Shields.Combinatorics.Young.LGVTableauTwo` for the shape and
`Shields.Combinatorics.Young.LGVOddTableauTwo` for its conjugate.

## Main results

* **The cells split by row.**  A skew cell sits in its own row between the two row lengths
  (`Shields.mem_skewCells_row_of_mem`), and a shape with no row beyond the `m`-th has all
  its cells in rows below `m`, so the cells are the disjoint union of the row segments
  `Ico μ_i λ_i` (`Shields.skewCells_eq_biUnion`) and a product over them splits into those
  rows (`Shields.prod_skewCells_rows`).
* **The conjugate splits by column.**  `Shields.mem_skewCells_transpose` reads a cell of
  `λ' / ν'` off the original shape, and `Shields.prod_skewCells_transpose_cols` is the
  matching splitting.
* **A row is a word.**  Row `i` of a bounded skew tableau, re-indexed from its first skew
  cell, is a one-row bounded tableau (`Shields.rowWord`): the row condition of `SkewSSYT`
  is the row condition of `BoundedSSYT (rect 1 m) b`, and the column condition is vacuous
  on one row.
* **A column of the conjugate is a word.**  `Shields.eColWord` is the transposed reading,
  and there it is the column condition that survives and the row condition that goes
  vacuous.

These are what put `Shields.pathOfWord` and `Shields.ePathOfWord` at the disposal of a
skew shape.

## Tags

semistandard tableau, skew Schur function, Young diagram, conjugate partition
-/

namespace Shields

open Finset

/-! ## The rows of a skew shape -/

section Rows

variable {b : ℕ} {lam mu : YoungDiagram}

/-- The columns a skew cell can occupy in its own row. -/
theorem mem_skewCells_row_of_mem {i j : ℕ} (h : (i, j) ∈ skewCells lam mu) :
    mu.rowLen i ≤ j ∧ j < lam.rowLen i := by
  obtain ⟨hlam, hnmu⟩ := mem_skewCells.mp h
  refine ⟨?_, YoungDiagram.mem_iff_lt_rowLen.mp hlam⟩
  by_contra hc
  exact hnmu (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))

/-- With no row beyond the `m`-th, every skew cell is in a row below `m`. -/
theorem lt_of_mem_skewCells {m : ℕ} (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) {i j : ℕ}
    (h : (i, j) ∈ skewCells lam mu) : i < m := by
  by_contra hc
  have h2 := (mem_skewCells_row_of_mem h).2
  rw [hrow i (by omega)] at h2
  omega

/-- The skew cells are the disjoint union of the row segments `Ico μ_i λ_i`. -/
theorem skewCells_eq_biUnion {m : ℕ} (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    skewCells lam mu = (Finset.range m).biUnion fun i =>
      ({i} : Finset ℕ) ×ˢ Finset.Ico (mu.rowLen i) (lam.rowLen i) := by
  ext c
  obtain ⟨i, j⟩ := c
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico]
  constructor
  · intro hc
    obtain ⟨h1, h2⟩ := mem_skewCells_row_of_mem hc
    exact ⟨i, lt_of_mem_skewCells hrow hc, rfl, h1, h2⟩
  · rintro ⟨i', -, hi, h1, h2⟩
    subst hi
    exact mem_skewCells.mpr ⟨YoungDiagram.mem_iff_lt_rowLen.mpr h2,
      fun hc => absurd (YoungDiagram.mem_iff_lt_rowLen.mp hc) (by omega)⟩

/-- A product over the skew cells splits into its rows. -/
theorem prod_skewCells_rows {m : ℕ} {M : Type*} [CommMonoid M]
    (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) (f : ℕ → ℕ → M) :
    ∏ c ∈ skewCells lam mu, f c.1 c.2
      = ∏ i ∈ Finset.range m, ∏ j ∈ Finset.Ico (mu.rowLen i) (lam.rowLen i), f i j := by
  rw [skewCells_eq_biUnion hrow, Finset.prod_biUnion]
  · exact Finset.prod_congr rfl fun i _ => by
      rw [Finset.prod_product', Finset.prod_singleton]
  · intro i₁ _ i₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    rw [Finset.mem_product, Finset.mem_singleton] at hc₁ hc₂
    exact hne (hc₁.1.symm.trans hc₂.1)

/-- The `j`-th cell of row `i` of `lam / mu`, counted from the first one. -/
theorem mem_skewCells_row (hmu : mu ≤ lam) (i : ℕ) {j : ℕ}
    (hj : j < lam.rowLen i - mu.rowLen i) : (i, mu.rowLen i + j) ∈ skewCells lam mu := by
  have h := rowLen_mono hmu i
  refine mem_skewCells.mpr ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), fun hc => ?_⟩
  exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hc) (by omega)

/-- Entries weakly increase along a row of the skew shape. -/
theorem skewRow_mono (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) (i : ℕ) {j₁ j₂ : ℕ}
    (hj : j₁ ≤ j₂) (hj₂ : j₂ < lam.rowLen i - mu.rowLen i) :
    T.1 i (mu.rowLen i + j₁) ≤ T.1 i (mu.rowLen i + j₂) := by
  rcases eq_or_lt_of_le hj with rfl | hlt
  · exact le_rfl
  · have h := rowLen_mono hmu i
    refine T.1.row_weak (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)) fun hc => ?_
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hc) (by omega)

/-- Row `i` of a bounded skew tableau as a one-row word of length
`λ_i - μ_i`. -/
def rowWord (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) (i : ℕ) :
    BoundedSSYT (rect 1 (lam.rowLen i - mu.rowLen i)) b :=
  ⟨{ entry := fun i' j' =>
       if i' = 0 ∧ j' < lam.rowLen i - mu.rowLen i then T.1 i (mu.rowLen i + j') else 0
     row_weak' := by
       intro i' j₁ j₂ hj hcell
       obtain ⟨hi', hj₂⟩ := mem_rect.mp hcell
       rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, hj₂⟩]
       exact skewRow_mono hmu T i hj.le hj₂
     col_strict' := by
       intro i₁ i₂ j' hi hcell
       exact absurd (mem_rect.mp hcell).1 (by omega)
     zeros' := by
       intro i' j' hcell
       exact if_neg fun hc => hcell (mem_rect.mpr ⟨by omega, hc.2⟩) },
   by
     intro i' j' hcell
     obtain ⟨hi', hj'⟩ := mem_rect.mp hcell
     change (if i' = 0 ∧ j' < lam.rowLen i - mu.rowLen i then T.1 i (mu.rowLen i + j') else 0) < b
     rw [if_pos ⟨by omega, hj'⟩]
     exact T.lt_of_mem_cells (mem_skewCells_row hmu i hj')⟩

theorem rowWord_apply (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) (i : ℕ) {j : ℕ}
    (hj : j < lam.rowLen i - mu.rowLen i) :
    rowWord hmu T i 0 j = T.1 i (mu.rowLen i + j) := by
  change (if (0 : ℕ) = 0 ∧ j < lam.rowLen i - mu.rowLen i then T.1 i (mu.rowLen i + j) else 0)
      = T.1 i (mu.rowLen i + j)
  rw [if_pos ⟨rfl, hj⟩]

theorem rowWord_mono (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) (i : ℕ) {j₁ j₂ : ℕ}
    (hj : j₁ ≤ j₂) (hj₂ : j₂ < lam.rowLen i - mu.rowLen i) :
    rowWord hmu T i 0 j₁ ≤ rowWord hmu T i 0 j₂ := by
  rw [rowWord_apply hmu T i (by omega : j₁ < lam.rowLen i - mu.rowLen i),
    rowWord_apply hmu T i hj₂]
  exact skewRow_mono hmu T i hj hj₂

end Rows

/-! ## The columns of the conjugate shape -/

section Columns

variable {a : ℕ} {lam nu : YoungDiagram}

theorem mem_transpose_iff_lt_rowLen {mu : YoungDiagram} {i j : ℕ} :
    (j, i) ∈ mu.transpose ↔ j < mu.rowLen i := by
  rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen]

/-- A cell of the conjugate skew shape, read on the original: `(j, i)` is a cell
of `λ' / ν'` exactly when abscissa `j` lies in row `i` of `λ / ν`. -/
theorem mem_skewCells_transpose {i j : ℕ} :
    (j, i) ∈ skewCells lam.transpose nu.transpose ↔ nu.rowLen i ≤ j ∧ j < lam.rowLen i := by
  rw [mem_skewCells, mem_transpose_iff_lt_rowLen, mem_transpose_iff_lt_rowLen]
  omega

/-- With no row of `λ` beyond the `m`-th, every cell of `λ' / ν'` is in a column
below `m`. -/
theorem lt_of_mem_skewCells_transpose {m : ℕ} (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) {i j : ℕ}
    (h : (j, i) ∈ skewCells lam.transpose nu.transpose) : i < m := by
  by_contra hc
  have h2 := (mem_skewCells_transpose.mp h).2
  rw [hrow i (by omega)] at h2
  omega

/-- The cells of `λ' / ν'` are the disjoint union of the column segments
`Ico ν_i λ_i`. -/
theorem skewCells_transpose_eq_biUnion {m : ℕ} (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    skewCells lam.transpose nu.transpose = (Finset.range m).biUnion fun i =>
      Finset.Ico (nu.rowLen i) (lam.rowLen i) ×ˢ ({i} : Finset ℕ) := by
  ext c
  obtain ⟨j, i⟩ := c
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico]
  constructor
  · intro hc
    obtain ⟨h1, h2⟩ := mem_skewCells_transpose.mp hc
    exact ⟨i, lt_of_mem_skewCells_transpose hrow hc, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨i', -, ⟨h1, h2⟩, hi⟩
    subst hi
    exact mem_skewCells_transpose.mpr ⟨h1, h2⟩

/-- A product over the cells of `λ' / ν'` splits into its columns. -/
theorem prod_skewCells_transpose_cols {m : ℕ} {M : Type*} [CommMonoid M]
    (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) (f : ℕ → ℕ → M) :
    ∏ c ∈ skewCells lam.transpose nu.transpose, f c.1 c.2
      = ∏ i ∈ Finset.range m, ∏ j ∈ Finset.Ico (nu.rowLen i) (lam.rowLen i), f j i := by
  rw [skewCells_transpose_eq_biUnion hrow, Finset.prod_biUnion]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_product']
    simp only [Finset.prod_singleton]
  · intro i₁ _ i₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    rw [Finset.mem_product, Finset.mem_singleton] at hc₁ hc₂
    exact hne (hc₁.2.symm.trans hc₂.2)

/-- The `j`-th cell of column `i` of `λ' / ν'`, counted from the first one. -/
theorem mem_skewCells_transpose_col (i : ℕ) {j : ℕ}
    (hj : j < lam.rowLen i - nu.rowLen i) :
    (nu.rowLen i + j, i) ∈ skewCells lam.transpose nu.transpose :=
  mem_skewCells_transpose.mpr ⟨by omega, by omega⟩

/-- Entries increase strictly down a column of `λ' / ν'`. -/
theorem eSkewCol_strict (T : BoundedSkewSSYT lam.transpose nu.transpose a) (i : ℕ)
    {j₁ j₂ : ℕ} (hj : j₁ < j₂) (hj₂ : j₂ < lam.rowLen i - nu.rowLen i) :
    T.1 (nu.rowLen i + j₁) i < T.1 (nu.rowLen i + j₂) i :=
  T.1.col_strict (by omega) (mem_transpose_iff_lt_rowLen.mpr (by omega))
    (fun hc => absurd (mem_transpose_iff_lt_rowLen.mp hc) (by omega))

/-- Column `i` of a bounded tableau of `λ' / ν'` as a one-column word of length
`λ_i - ν_i`. -/
def eColWord (a : ℕ) (lam nu : YoungDiagram)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) (i : ℕ) :
    BoundedSSYT (rect (lam.rowLen i - nu.rowLen i) 1) a :=
  ⟨{ entry := fun j i' =>
       if i' = 0 ∧ j < lam.rowLen i - nu.rowLen i then T.1 (nu.rowLen i + j) i else 0
     row_weak' := by
       intro j i₁ i₂ hi hcell
       exact absurd (mem_rect.mp hcell).2 (by omega)
     col_strict' := by
       intro j₁ j₂ i' hj hcell
       obtain ⟨hj₂, hi'⟩ := mem_rect.mp hcell
       rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, hj₂⟩]
       exact eSkewCol_strict T i hj hj₂
     zeros' := by
       intro j i' hcell
       exact if_neg fun hc => hcell (mem_rect.mpr ⟨hc.2, by omega⟩) },
   by
     intro j i' hcell
     obtain ⟨hj, hi'⟩ := mem_rect.mp hcell
     change (if i' = 0 ∧ j < lam.rowLen i - nu.rowLen i then T.1 (nu.rowLen i + j) i else 0) < a
     rw [if_pos ⟨by omega, hj⟩]
     exact T.lt_of_mem_cells (mem_skewCells_transpose_col i hj)⟩

theorem eColWord_apply (T : BoundedSkewSSYT lam.transpose nu.transpose a) (i : ℕ) {j : ℕ}
    (hj : j < lam.rowLen i - nu.rowLen i) :
    eColWord a lam nu T i j 0 = T.1 (nu.rowLen i + j) i := by
  change (if (0 : ℕ) = 0 ∧ j < lam.rowLen i - nu.rowLen i then T.1 (nu.rowLen i + j) i else 0)
      = T.1 (nu.rowLen i + j) i
  rw [if_pos ⟨rfl, hj⟩]

theorem eColWord_mono (T : BoundedSkewSSYT lam.transpose nu.transpose a) (i : ℕ) {j₁ j₂ : ℕ}
    (hj : j₁ ≤ j₂) (hj₂ : j₂ < lam.rowLen i - nu.rowLen i) :
    eColWord a lam nu T i j₁ 0 ≤ eColWord a lam nu T i j₂ 0 :=
  boundedSSYT_col_mono _ hj hj₂

end Columns


/-! ### Axiom footprint -/

/-- info: 'Shields.prod_skewCells_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_skewCells_rows

/-- info: 'Shields.prod_skewCells_transpose_cols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_skewCells_transpose_cols

/-- info: 'Shields.rowWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowWord

/-- info: 'Shields.eColWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eColWord

end Shields
