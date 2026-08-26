/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Intervals
import Shields.Combinatorics.Young.LGVPaths

namespace Shields

open Finset

section TwoRows

variable {b : ℕ} {lam mu : YoungDiagram}

/-! ## Cells of a two-row skew shape

A skew cell sits in its row between the two row lengths, and a shape with no
row beyond the second has all its cells in rows `0` and `1`.
-/

/-- The columns a skew cell can occupy in its own row. -/
theorem mem_skewCells_row_of_mem {i j : ℕ} (h : (i, j) ∈ skewCells lam mu) :
    mu.rowLen i ≤ j ∧ j < lam.rowLen i := by
  obtain ⟨hlam, hnmu⟩ := mem_skewCells.mp h
  refine ⟨?_, YoungDiagram.mem_iff_lt_rowLen.mp hlam⟩
  by_contra hc
  exact hnmu (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))

/-- With no row beyond the second, every skew cell is in row `0` or row `1`. -/
theorem lt_two_of_mem_skewCells (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) {i j : ℕ}
    (h : (i, j) ∈ skewCells lam mu) : i < 2 := by
  by_contra hc
  have h2 := (mem_skewCells_row_of_mem h).2
  rw [hrow i (by omega)] at h2
  omega

/-- The `j`-th cell of row `i` of `lam / mu`, counted from the first one. -/
theorem mem_skewCells_row (hmu : mu ≤ lam) (i : ℕ) {j : ℕ}
    (hj : j < lam.rowLen i - mu.rowLen i) : (i, mu.rowLen i + j) ∈ skewCells lam mu := by
  have h := rowLen_mono hmu i
  refine mem_skewCells.mpr ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), fun hc => ?_⟩
  exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hc) (by omega)

/-! ## A row of a skew tableau is a word

Row `i` of a bounded skew tableau, re-indexed from its first skew cell, is a
one-row bounded tableau: the row condition of `SkewSSYT` is the row condition of
`BoundedSSYT (rect 1 m) b`, and the column condition is vacuous on one row.
This is what puts `Shields.pathOfWord` at the disposal of a skew shape.
-/

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

/-! ## The paths of a tableau

Each row of the tableau is run through `pathOfWord`, at the source the
Jacobi--Trudi shift prescribes: `μ_0 + 1` for row `0` and `μ_1` for row `1`.
-/

/-- The pair of paths a bounded skew tableau of a two-row shape traces. -/
noncomputable def pathsOfSkew (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) :
    (ℕ → ℕ) × (ℕ → ℕ) :=
  (pathOfWord b (mu.rowLen 0 + 1) (lam.rowLen 0 - mu.rowLen 0) (rowWord hmu T 0),
   pathOfWord b (mu.rowLen 1) (lam.rowLen 1 - mu.rowLen 1) (rowWord hmu T 1))

theorem pathsOfSkew_fst_mem (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) :
    (pathsOfSkew hmu T).1 ∈ hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) := by
  have h := rowLen_mono hmu 0
  have hmem := pathOfWord_mem b (mu.rowLen 0 + 1) (lam.rowLen 0 - mu.rowLen 0) (rowWord hmu T 0)
  rwa [show mu.rowLen 0 + 1 + (lam.rowLen 0 - mu.rowLen 0) = lam.rowLen 0 + 1 by omega] at hmem

theorem pathsOfSkew_snd_mem (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) :
    (pathsOfSkew hmu T).2 ∈ hPaths b (mu.rowLen 1) (lam.rowLen 1) := by
  have h := rowLen_mono hmu 1
  have hmem := pathOfWord_mem b (mu.rowLen 1) (lam.rowLen 1 - mu.rowLen 1) (rowWord hmu T 1)
  rwa [show mu.rowLen 1 + (lam.rowLen 1 - mu.rowLen 1) = lam.rowLen 1 by omega] at hmem

/-- A letter of row `0` below `i` puts its abscissa behind the path at height
`i`: the counting set of a weakly increasing word is an initial segment. -/
theorem lt_pathsOfSkew_fst (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) {i j : ℕ}
    (hj : j < lam.rowLen 0 - mu.rowLen 0) (hlt : T.1 0 (mu.rowLen 0 + j) < i) :
    mu.rowLen 0 + 1 + j < (pathsOfSkew hmu T).1 i := by
  have hsub : Finset.range (j + 1)
      ⊆ (Finset.range (lam.rowLen 0 - mu.rowLen 0)).filter
          fun j' => rowWord hmu T 0 0 j' < i := by
    intro j' hj'
    rw [Finset.mem_range] at hj'
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    refine lt_of_le_of_lt (rowWord_mono hmu T 0 (by omega : j' ≤ j) hj) ?_
    rw [rowWord_apply hmu T 0 hj]
    exact hlt
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  change mu.rowLen 0 + 1 + j < mu.rowLen 0 + 1 + _
  omega

/-- A letter of row `1` at or above `i` stops the path of that row at its
abscissa. -/
theorem pathsOfSkew_snd_le (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) {i j : ℕ}
    (hle : i ≤ T.1 1 (mu.rowLen 1 + j)) :
    (pathsOfSkew hmu T).2 i ≤ mu.rowLen 1 + j := by
  have hsub : ((Finset.range (lam.rowLen 1 - mu.rowLen 1)).filter
      fun j' => rowWord hmu T 1 0 j' < i) ⊆ Finset.range j := by
    intro j' hj'
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    rw [Finset.mem_range]
    by_contra hcon
    have hmono := rowWord_mono hmu T 1 (by omega : j ≤ j') hj'.1
    rw [rowWord_apply hmu T 1 (by omega : j < lam.rowLen 1 - mu.rowLen 1)] at hmono
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  change mu.rowLen 1 + _ ≤ mu.rowLen 1 + j
  omega

/-- **Column strictness is separation.**  The two paths of a bounded skew
tableau stay a full step apart: row `1` has left height `i + 1` before row `0`
reaches height `i`.  This is the converse of `lt_of_not_crosses`. -/
theorem lt_pathsOfSkew (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) (i : ℕ) :
    (pathsOfSkew hmu T).2 (i + 1) < (pathsOfSkew hmu T).1 i := by
  have hmu01 : mu.rowLen 1 ≤ mu.rowLen 0 := mu.rowLen_anti 0 1 (by omega)
  have hlam01 : lam.rowLen 1 ≤ lam.rowLen 0 := lam.rowLen_anti 0 1 (by omega)
  have h0 : mu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hmu 0
  have h1 : mu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hmu 1
  have hqb := hPaths_le (pathsOfSkew_fst_mem hmu T) i
  have hrb := hPaths_le (pathsOfSkew_snd_mem hmu T) (i + 1)
  by_contra hcon
  rw [Nat.not_lt] at hcon
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, (pathsOfSkew hmu T).1 i = j₀ + 1 :=
    ⟨(pathsOfSkew hmu T).1 i - 1, by omega⟩
  have ha : i ≤ T.1 0 j₀ := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    have hstep := lt_pathsOfSkew_fst hmu T (j := j₀ - mu.rowLen 0) (by omega)
      (by rw [show mu.rowLen 0 + (j₀ - mu.rowLen 0) = j₀ by omega]; exact hlt)
    omega
  have hb : T.1 1 j₀ ≤ i := by
    by_contra hgt
    rw [Nat.not_le] at hgt
    have hstep := pathsOfSkew_snd_le hmu T (i := i + 1) (j := j₀ - mu.rowLen 1)
      (by rw [show mu.rowLen 1 + (j₀ - mu.rowLen 1) = j₀ by omega]; omega)
    omega
  have hcol : T.1 0 j₀ < T.1 1 j₀ :=
    T.1.col_strict (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      fun hc => absurd (YoungDiagram.mem_iff_lt_rowLen.mp hc) (by omega)
  omega

theorem not_crosses_pathsOfSkew (hmu : mu ≤ lam) (T : BoundedSkewSSYT lam mu b) :
    ¬ Crosses b (pathsOfSkew hmu T).1 (pathsOfSkew hmu T).2 := by
  rintro ⟨k, hk⟩
  obtain ⟨-, hk1, -⟩ := mem_crossSet.mp hk
  exact absurd (lt_pathsOfSkew hmu T k) (by omega)

/-! ## The tableau of a non-crossing pair

The cell `(0, j)` reads the letter the first path writes at abscissa `j + 1`,
the cell `(1, j)` the letter the second writes at `j`.  Rows increase weakly
because letters do; columns increase strictly because the pair never meets.
-/

/-- The filling of `lam / mu` read off a pair of paths. -/
noncomputable def skewEntry (b : ℕ) (lam mu : YoungDiagram) (x : (ℕ → ℕ) × (ℕ → ℕ))
    (i j : ℕ) : ℕ :=
  if (i, j) ∈ skewCells lam mu then
    if i = 0 then pathLetter b (mu.rowLen 0 + 1) x.1 (j - mu.rowLen 0)
    else pathLetter b (mu.rowLen 1) x.2 (j - mu.rowLen 1)
  else 0

theorem skewEntry_zero (x : (ℕ → ℕ) × (ℕ → ℕ)) {j : ℕ} (h : (0, j) ∈ skewCells lam mu) :
    skewEntry b lam mu x 0 j = pathLetter b (mu.rowLen 0 + 1) x.1 (j - mu.rowLen 0) := by
  rw [skewEntry, if_pos h, if_pos rfl]

theorem skewEntry_one (x : (ℕ → ℕ) × (ℕ → ℕ)) {j : ℕ} (h : (1, j) ∈ skewCells lam mu) :
    skewEntry b lam mu x 1 j = pathLetter b (mu.rowLen 1) x.2 (j - mu.rowLen 1) := by
  rw [skewEntry, if_pos h, if_neg (by omega : ¬ (1 : ℕ) = 0)]

theorem skewEntry_of_notMem (x : (ℕ → ℕ) × (ℕ → ℕ)) {i j : ℕ}
    (h : (i, j) ∉ skewCells lam mu) : skewEntry b lam mu x i j = 0 :=
  if_neg h

/-- **The column of a two-row filling increases strictly.**  The letter the
right-hand path writes at `j + 1` is below the one the left-hand path writes at
`j`, because the two are separated by a full step. -/
theorem skewEntry_col_strict {x : (ℕ → ℕ) × (ℕ → ℕ)}
    (hq : x.1 ∈ hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ hPaths b (mu.rowLen 1) (lam.rowLen 1)) (hnc : ¬ Crosses b x.1 x.2) {j : ℕ}
    (hc₀ : (0, j) ∈ skewCells lam mu) (hc₁ : (1, j) ∈ skewCells lam mu) :
    skewEntry b lam mu x 0 j < skewEntry b lam mu x 1 j := by
  have hmu01 : mu.rowLen 1 ≤ mu.rowLen 0 := mu.rowLen_anti 0 1 (by omega)
  obtain ⟨hj0, hj0'⟩ := mem_skewCells_row_of_mem hc₀
  obtain ⟨hj1, hj1'⟩ := mem_skewCells_row_of_mem hc₁
  rw [skewEntry_zero x hc₀, skewEntry_one x hc₁]
  have hBb : pathLetter b (mu.rowLen 1) x.2 (j - mu.rowLen 1) < b :=
    pathLetter_lt_height hr (by omega)
  have hjr : j < x.2 (pathLetter b (mu.rowLen 1) x.2 (j - mu.rowLen 1) + 1) := by
    have h := (pathLetter_lt_iff hr
      (show pathLetter b (mu.rowLen 1) x.2 (j - mu.rowLen 1) + 1 ≤ b by omega)).mp
      (Nat.lt_succ_self _)
    omega
  have hsep := lt_of_not_crosses hq hr (by omega) hnc
    (pathLetter b (mu.rowLen 1) x.2 (j - mu.rowLen 1)) hBb
  exact (pathLetter_lt_iff hq (show pathLetter b (mu.rowLen 1) x.2 (j - mu.rowLen 1) ≤ b
    by omega)).mpr (by omega)

/-- The bounded skew tableau a non-crossing pair of paths carries. -/
noncomputable def skewOfPaths (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0)
    {x : (ℕ → ℕ) × (ℕ → ℕ)} (hq : x.1 ∈ hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ hPaths b (mu.rowLen 1) (lam.rowLen 1)) (hnc : ¬ Crosses b x.1 x.2) :
    BoundedSkewSSYT lam mu b :=
  ⟨{ entry := skewEntry b lam mu x
     row_weak' := by
       intro i j₁ j₂ hj hlam hnmu
       have hc₁ : (i, j₁) ∈ skewCells lam mu :=
         mem_skewCells.mpr ⟨lam.up_left_mem le_rfl hj.le hlam, hnmu⟩
       have hc₂ : (i, j₂) ∈ skewCells lam mu :=
         mem_skewCells.mpr ⟨hlam, notMem_of_col_le hj.le hnmu⟩
       have hi := lt_two_of_mem_skewCells hrow hc₁
       interval_cases i
       · rw [skewEntry_zero x hc₁, skewEntry_zero x hc₂]
         exact pathLetter_mono _ _ _ (by omega)
       · rw [skewEntry_one x hc₁, skewEntry_one x hc₂]
         exact pathLetter_mono _ _ _ (by omega)
     col_strict' := by
       intro i₁ i₂ j hi hlam hnmu
       have hc₂ : (i₂, j) ∈ skewCells lam mu :=
         mem_skewCells.mpr ⟨hlam, notMem_of_row_le hi.le hnmu⟩
       have hi₂ := lt_two_of_mem_skewCells hrow hc₂
       obtain rfl : i₂ = 1 := by omega
       obtain rfl : i₁ = 0 := by omega
       have hc₁ : (0, j) ∈ skewCells lam mu :=
         mem_skewCells.mpr ⟨lam.up_left_mem (by omega) le_rfl hlam, hnmu⟩
       exact skewEntry_col_strict hq hr hnc hc₁ hc₂
     zeros' := fun hc => skewEntry_of_notMem x hc },
   by
     intro i j hcell
     have hi := lt_two_of_mem_skewCells hrow hcell
     obtain ⟨hj, hj'⟩ := mem_skewCells_row_of_mem hcell
     change skewEntry b lam mu x i j < b
     interval_cases i
     · rw [skewEntry_zero x hcell]
       exact pathLetter_lt_height hq (by omega)
     · rw [skewEntry_one x hcell]
       exact pathLetter_lt_height hr (by omega)⟩

theorem skewOfPaths_apply (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0)
    {x : (ℕ → ℕ) × (ℕ → ℕ)} (hq : x.1 ∈ hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ hPaths b (mu.rowLen 1) (lam.rowLen 1)) (hnc : ¬ Crosses b x.1 x.2) (i j : ℕ) :
    (skewOfPaths hrow hq hr hnc).1 i j = skewEntry b lam mu x i j :=
  rfl

/-! ## The two round trips -/

/-- A one-row word whose letters are those of a path traces that path back. -/
theorem pathOfWord_eq_of_entry {s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ hPaths b s (s + m))
    (T : BoundedSSYT (rect 1 m) b) (h : ∀ j, j < m → T 0 j = pathLetter b s q j) :
    pathOfWord b s m T = q := by
  rw [← pathOfWord_wordOfPath hq]
  funext i
  have hset : ((Finset.range m).filter fun j => T 0 j < i)
      = (Finset.range m).filter fun j => wordOfPath b s m q hq 0 j < i := by
    ext j
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hj, hlt⟩
      refine ⟨hj, ?_⟩
      rw [wordOfPath_apply hq, if_pos ⟨rfl, Finset.mem_range.mp hj⟩,
        ← h j (Finset.mem_range.mp hj)]
      exact hlt
    · rintro ⟨hj, hlt⟩
      rw [wordOfPath_apply hq, if_pos ⟨rfl, Finset.mem_range.mp hj⟩] at hlt
      refine ⟨hj, ?_⟩
      rw [h j (Finset.mem_range.mp hj)]
      exact hlt
  change s + ((Finset.range m).filter fun j => T 0 j < i).card
      = s + ((Finset.range m).filter fun j => wordOfPath b s m q hq 0 j < i).card
  rw [hset]

/-- Paths to tableau and back. -/
theorem pathsOfSkew_skewOfPaths (hmu : mu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0)
    {x : (ℕ → ℕ) × (ℕ → ℕ)} (hq : x.1 ∈ hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ hPaths b (mu.rowLen 1) (lam.rowLen 1)) (hnc : ¬ Crosses b x.1 x.2) :
    pathsOfSkew hmu (skewOfPaths hrow hq hr hnc) = x := by
  have h0 : mu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hmu 0
  have h1 : mu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hmu 1
  have hq' : x.1 ∈ hPaths b (mu.rowLen 0 + 1)
      (mu.rowLen 0 + 1 + (lam.rowLen 0 - mu.rowLen 0)) := by
    rwa [show mu.rowLen 0 + 1 + (lam.rowLen 0 - mu.rowLen 0) = lam.rowLen 0 + 1 by omega]
  have hr' : x.2 ∈ hPaths b (mu.rowLen 1) (mu.rowLen 1 + (lam.rowLen 1 - mu.rowLen 1)) := by
    rwa [show mu.rowLen 1 + (lam.rowLen 1 - mu.rowLen 1) = lam.rowLen 1 by omega]
  refine Prod.ext ?_ ?_
  · refine pathOfWord_eq_of_entry hq' _ fun j hj => ?_
    rw [rowWord_apply hmu _ 0 hj, skewOfPaths_apply,
      skewEntry_zero x (mem_skewCells_row hmu 0 hj),
      show mu.rowLen 0 + j - mu.rowLen 0 = j by omega]
  · refine pathOfWord_eq_of_entry hr' _ fun j hj => ?_
    rw [rowWord_apply hmu _ 1 hj, skewOfPaths_apply,
      skewEntry_one x (mem_skewCells_row hmu 1 hj),
      show mu.rowLen 1 + j - mu.rowLen 1 = j by omega]

/-- Tableau to paths and back. -/
theorem skewOfPaths_pathsOfSkew (hmu : mu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0)
    (T : BoundedSkewSSYT lam mu b) {hq hr hnc} :
    skewOfPaths (x := pathsOfSkew hmu T) hrow hq hr hnc = T := by
  refine BoundedSkewSSYT.ext fun i j => ?_
  change skewEntry b lam mu (pathsOfSkew hmu T) i j = T.1 i j
  by_cases hcell : (i, j) ∈ skewCells lam mu
  · have hi := lt_two_of_mem_skewCells hrow hcell
    obtain ⟨hj, hj'⟩ := mem_skewCells_row_of_mem hcell
    have hmu0 : mu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hmu 0
    have hmu1 : mu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hmu 1
    interval_cases i
    · rw [skewEntry_zero _ hcell]
      change pathLetter b (mu.rowLen 0 + 1)
        (pathOfWord b (mu.rowLen 0 + 1) (lam.rowLen 0 - mu.rowLen 0) (rowWord hmu T 0))
        (j - mu.rowLen 0) = _
      rw [pathLetter_pathOfWord _ (show j - mu.rowLen 0 < lam.rowLen 0 - mu.rowLen 0 by omega),
        rowWord_apply hmu T 0 (by omega), show mu.rowLen 0 + (j - mu.rowLen 0) = j by omega]
    · rw [skewEntry_one _ hcell]
      change pathLetter b (mu.rowLen 1)
        (pathOfWord b (mu.rowLen 1) (lam.rowLen 1 - mu.rowLen 1) (rowWord hmu T 1))
        (j - mu.rowLen 1) = _
      rw [pathLetter_pathOfWord _ (show j - mu.rowLen 1 < lam.rowLen 1 - mu.rowLen 1 by omega),
        rowWord_apply hmu T 1 (by omega), show mu.rowLen 1 + (j - mu.rowLen 1) = j by omega]
  · rw [skewEntry_of_notMem _ hcell]
    exact (T.zeros hcell).symm

/-! ## Weights

The product over the skew cells splits into the two rows, and each row is the
weight of its path: `pathWeight_eq_prod_letters` reads a path weight as the
product over its letters, which is what the row of the tableau holds.
-/

theorem prod_skewCells_two_rows {M : Type*} [CommMonoid M]
    (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) (f : ℕ → ℕ → M) :
    ∏ c ∈ skewCells lam mu, f c.1 c.2
      = (∏ j ∈ Finset.Ico (mu.rowLen 0) (lam.rowLen 0), f 0 j)
        * ∏ j ∈ Finset.Ico (mu.rowLen 1) (lam.rowLen 1), f 1 j := by
  have hsplit : skewCells lam mu
      = (({0} : Finset ℕ) ×ˢ Finset.Ico (mu.rowLen 0) (lam.rowLen 0))
        ∪ (({1} : Finset ℕ) ×ˢ Finset.Ico (mu.rowLen 1) (lam.rowLen 1)) := by
    ext c
    obtain ⟨i, j⟩ := c
    rw [Finset.mem_union, Finset.mem_product, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_singleton, Finset.mem_Ico, Finset.mem_Ico]
    constructor
    · intro hc
      obtain ⟨hj1, hj2⟩ := mem_skewCells_row_of_mem hc
      have hi := lt_two_of_mem_skewCells hrow hc
      interval_cases i
      · exact Or.inl ⟨rfl, hj1, hj2⟩
      · exact Or.inr ⟨rfl, hj1, hj2⟩
    · rintro (⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩) <;>
        exact mem_skewCells.mpr ⟨YoungDiagram.mem_iff_lt_rowLen.mpr h2,
          fun hc => absurd (YoungDiagram.mem_iff_lt_rowLen.mp hc) (by omega)⟩
  have hdisj : Disjoint (({0} : Finset ℕ) ×ˢ Finset.Ico (mu.rowLen 0) (lam.rowLen 0))
      (({1} : Finset ℕ) ×ˢ Finset.Ico (mu.rowLen 1) (lam.rowLen 1)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rw [Finset.mem_product, Finset.mem_singleton] at hc1 hc2
    exact absurd (hc1.1.symm.trans hc2.1) (by omega)
  rw [hsplit, Finset.prod_union hdisj, Finset.prod_product', Finset.prod_product',
    Finset.prod_singleton, Finset.prod_singleton]

variable {R : Type*} [CommRing R]

/-- The weight of a non-crossing pair is the weight of the tableau it carries. -/
theorem prod_skewCells_eq_pathWeight (hmu : mu ≤ lam)
    (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) (β : ℕ → R) {x : (ℕ → ℕ) × (ℕ → ℕ)}
    (hq : x.1 ∈ hPaths b (mu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ hPaths b (mu.rowLen 1) (lam.rowLen 1)) :
    pathWeight b β x.1 * pathWeight b β x.2
      = ∏ c ∈ skewCells lam mu, β (skewEntry b lam mu x c.1 c.2) := by
  have h0 : mu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hmu 0
  have h1 : mu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hmu 1
  have hq' : x.1 ∈ hPaths b (mu.rowLen 0 + 1)
      (mu.rowLen 0 + 1 + (lam.rowLen 0 - mu.rowLen 0)) := by
    rwa [show mu.rowLen 0 + 1 + (lam.rowLen 0 - mu.rowLen 0) = lam.rowLen 0 + 1 by omega]
  have hr' : x.2 ∈ hPaths b (mu.rowLen 1) (mu.rowLen 1 + (lam.rowLen 1 - mu.rowLen 1)) := by
    rwa [show mu.rowLen 1 + (lam.rowLen 1 - mu.rowLen 1) = lam.rowLen 1 by omega]
  rw [prod_skewCells_two_rows hrow fun i j => β (skewEntry b lam mu x i j),
    pathWeight_eq_prod_letters hq' β, pathWeight_eq_prod_letters hr' β,
    Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [skewEntry_zero x (mem_skewCells_row hmu 0 (Finset.mem_range.mp hj)),
      show mu.rowLen 0 + j - mu.rowLen 0 = j by omega]
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [skewEntry_one x (mem_skewCells_row hmu 1 (Finset.mem_range.mp hj)),
      show mu.rowLen 1 + j - mu.rowLen 1 = j by omega]

end TwoRows

/-! ## The identity

`NonCrossingIsSkewSchur` is now a theorem: the two constructions are mutually
inverse and weight-preserving, so the non-crossing pairs and the tableaux of
`λ / μ` have the same generating function.
-/

section Identity

variable {R : Type*} [CommRing R]

/-- **Residue one, discharged.**  For a pair of shapes with `λ` inside two rows,
the non-crossing pairs of paths carry the total weight of the semistandard
tableaux of `λ / μ`. -/
theorem nonCrossingIsSkewSchur (b : ℕ) (β : ℕ → R) : NonCrossingIsSkewSchur b β := by
  intro lam mu hmu hrow
  rw [skewSchur]
  refine Finset.sum_bij'
    (fun x hx => skewOfPaths (x := x) hrow
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
      (Finset.mem_filter.mp hx).2)
    (fun T _ => pathsOfSkew hmu T) (fun x _ => Finset.mem_univ _) (fun T _ => ?_)
    (fun x hx => ?_) (fun T _ => skewOfPaths_pathsOfSkew hmu hrow T) (fun x hx => ?_)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨pathsOfSkew_fst_mem hmu T, pathsOfSkew_snd_mem hmu T⟩, not_crosses_pathsOfSkew hmu T⟩
  · exact pathsOfSkew_skewOfPaths hmu hrow _ _ _
  · exact prod_skewCells_eq_pathWeight hmu hrow β
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2

/-- **The `2 × 2` Jacobi--Trudi determinant over the even alphabet.**  For `λ`
inside two rows it is the skew Schur polynomial `s_{λ/μ}(β_0, …, β_{b-1})`. -/
theorem jacobiTrudiDet_two_eq_skewSchur {b : ℕ} (β : ℕ → R) (lam mu : YoungDiagram)
    (hmu : mu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet (fun m => completeHom b m β) lam mu 2 = skewSchur lam mu b β := by
  rw [jacobiTrudiDet_two_eq_sum_nonCrossing, nonCrossingIsSkewSchur b β lam mu hmu hrow]

/-- **`SkewJacobiTrudi` at two rows and no odd variables**, with no hypothesis
carried: `det [h_{λ_u - μ_v - u + v}]_{u,v ≤ 2} = s_{λ/μ}(β | ∅)`. -/
theorem skewJacobiTrudi_two {b : ℕ} {β α : ℕ → R} (lam mu : YoungDiagram) (hmu : mu ≤ lam)
    (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet (fun m => superHom b 0 m β α) lam mu 2 = superSkewSchur lam mu b 0 β α :=
  skewJacobiTrudi_two_of_nonCrossing (nonCrossingIsSkewSchur b β) lam mu hmu hrow

/-- ** at no odd variables, up to two rows.**  The one-row
case `jacobiTrudiDet_eq_superSkewSchur_of_le_one` and the two-row case together:
for `m ≤ 2` and `λ` inside `m` rows, the Jacobi--Trudi determinant of the
alphabet `d_m = h_m(β)` is `s_{λ/μ}(β | ∅)`.  `LGVTableauM` removes the row
bound — `jacobiTrudiDet_eq_superSkewSchur_even` is this statement at every `m` —
so what `SkewJacobiTrudi` still asks for beyond it is the odd alphabet, whose
paths are a different geometry. -/
theorem jacobiTrudiDet_eq_superSkewSchur_of_le_two {b : ℕ} {β α : ℕ → R} {d : ℕ → R}
    (hd : ∀ m, d m = superHom b 0 m β α) {lam mu : YoungDiagram} {m : ℕ} (hm : m ≤ 2)
    (hmu : mu ≤ lam) (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet d lam mu m = superSkewSchur lam mu b 0 β α := by
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · exact jacobiTrudiDet_eq_superSkewSchur_of_le_one hd (by omega) hmu hrow
  · obtain rfl : m = 2 := by omega
    rw [funext hd]
    exact skewJacobiTrudi_two lam mu hmu hrow

/-! ## Non-vacuity

The smallest instance the two-row case decides, where the crossing cancellation
actually fires: on the column `λ = (1, 1)` in two even variables the identity
reads `h_1^2 - h_2 h_0 = β_0 β_1`.
-/

theorem jacobiTrudiDet_two_column (β : ℕ → R) :
    jacobiTrudiDet (fun m => completeHom 2 m β) (rect 2 1) ⊥ 2 = β 0 * β 1 := by
  rw [jacobiTrudiDet_two_eq_skewSchur β (rect 2 1) ⊥ bot_le
      (fun i hi => rowLen_rect_of_le (by omega)),
    skewSchur_bot, schur_rect, pow_one, Finset.prod_range_succ, Finset.prod_range_one]

end Identity

end Shields
