/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVOddBranching

/-!
# The tableau bijection for the odd alphabet, at two columns

`Shields.Combinatorics.Young.LGVOddPaths` builds the odd path model and leaves one residue,
`Shields.NonMeetingIsSkewSchurTranspose`: that the non-meeting pairs of odd paths carry the weight
of the tableaux of the **conjugate** skew shape `λ' / ν'`.  This module discharges it.  It is the
odd counterpart of `Shields.nonCrossingIsSkewSchur`, with the geometry swapped.

* **The dictionary is by columns.**  Column `i` of `λ' / ν'` is the word of the path of row `i` of
  `λ / ν`, read at the sources the Jacobi--Trudi shift prescribes, `ν_0 + 1` for `i = 0` and `ν_1`
  for `i = 1`.  The cell `(j, i)` of the conjugate shape carries the letter that path writes at
  abscissa `j + 1 - i`.  `Shields.eColWord` is that reading and `Shields.eSkewEntry` its inverse.
* **Point disjointness is the row condition, and it is weak.**  Two odd paths sharing no lattice
  point satisfy `r i < q i` at *every* height (`Shields.lt_of_not_eMeets`), one step weaker than
  the even model's `r (i+1) < q i`; after the shift that reads `T j 0 ≤ T j 1`, the weak increase
  along a row of `λ' / ν'`.  Conversely a row-weak filling forces that separation
  (`Shields.lt_ePathsOfSkew`).
* **Strict increase down a column is the unit step.**  `Shields.pathLetter_strictMono` makes the
  letters of an odd path strictly increase, which is `col_strict` on the conjugate shape.  This is
  where the two geometries part company: the even word is a row, and its transposed statement
  would be false.

## Main results

* `Shields.nonMeetingIsSkewSchurTranspose` -- the bijection, at every `a` and `α`, over any
  commutative ring, with no hypothesis carried.
* `Shields.sum_nonMeeting_mixed_eq_superSkewSchur_uncond` -- consequently the super branching rule
  at two rows is **unconditional**: for a pair of shapes with `λ` inside two rows, the
  non-intersecting pairs of mixed paths carry `superSkewSchur lam mu b a β α`.  Both tableau
  bijections the splice consumes are now theorems, so nothing between the mixed path model and the
  two-row branching identity is assumed.

## Implementation notes

The skew Jacobi--Trudi identity itself is untouched here.  What still stands between the branching
identity and it is the cancellation for the *mixed* crossing predicate
(`Shields.Combinatorics.Young.LGVMixed`) and, at more than two rows, the correspondence between
non-intersecting `m`-families and tableaux
(`Shields.Combinatorics.Young.LGVOddTableau`).

## Tags

Lindström-Gessel-Viennot, semistandard tableau, conjugate partition, skew Schur function, super
Schur function
-/

namespace Shields

open Finset

/-! ## Cells of a conjugate skew shape

A cell of `λ' / ν'` is a cell of `λ / ν` with its coordinates exchanged, so it
is pinned by the row lengths of the original pair.  When `λ` has no row beyond
the second, the conjugate shape has no column beyond the second.
-/

section Cells

variable {lam nu : YoungDiagram}

theorem mem_transpose_iff_lt_rowLen {mu : YoungDiagram} {i j : ℕ} :
    (j, i) ∈ mu.transpose ↔ j < mu.rowLen i := by
  rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen]

/-- A cell of the conjugate skew shape, read on the original: `(j, i)` is a cell
of `λ' / ν'` exactly when abscissa `j` lies in row `i` of `λ / ν`. -/
theorem mem_skewCells_transpose {i j : ℕ} :
    (j, i) ∈ skewCells lam.transpose nu.transpose ↔ nu.rowLen i ≤ j ∧ j < lam.rowLen i := by
  rw [mem_skewCells, mem_transpose_iff_lt_rowLen, mem_transpose_iff_lt_rowLen]
  omega

/-- With no row of `λ` beyond the second, every cell of `λ' / ν'` is in column
`0` or column `1`. -/
theorem lt_two_of_mem_skewCells_transpose (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) {i j : ℕ}
    (h : (j, i) ∈ skewCells lam.transpose nu.transpose) : i < 2 := by
  by_contra hc
  have h2 := (mem_skewCells_transpose.mp h).2
  rw [hrow i (by omega)] at h2
  omega

/-- The `j`-th cell of column `i` of `λ' / ν'`, counted from the first one. -/
theorem mem_skewCells_transpose_col (i : ℕ) {j : ℕ}
    (hj : j < lam.rowLen i - nu.rowLen i) :
    (nu.rowLen i + j, i) ∈ skewCells lam.transpose nu.transpose :=
  mem_skewCells_transpose.mpr ⟨by omega, by omega⟩

end Cells

/-! ## A column of a conjugate skew tableau is a word

Column `i` of a bounded tableau of `λ' / ν'`, re-indexed from its first skew
cell, is a one-column bounded tableau: the column condition of `SkewSSYT` is the
column condition of `BoundedSSYT (rect m 1) a`, and the row condition is vacuous
on a shape of one column.  This is what puts `Shields.ePathOfWord` at the
disposal of a conjugate shape.
-/

section ColWord

variable {a : ℕ} {lam nu : YoungDiagram}

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

end ColWord

/-! ## The paths of a conjugate tableau

Each column of the tableau is run through `ePathOfWord`, at the source the
Jacobi--Trudi shift prescribes: `ν_0 + 1` for column `0` and `ν_1` for
column `1`.
-/

section Paths

variable {a : ℕ} {lam nu : YoungDiagram}

/-- The pair of odd paths a bounded tableau of `λ' / ν'` traces. -/
noncomputable def ePathsOfSkew (a : ℕ) (lam nu : YoungDiagram)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (ePathOfWord a (nu.rowLen 0 + 1) (lam.rowLen 0 - nu.rowLen 0) (eColWord a lam nu T 0),
   ePathOfWord a (nu.rowLen 1) (lam.rowLen 1 - nu.rowLen 1) (eColWord a lam nu T 1))

theorem ePathsOfSkew_fst_mem (hnu : nu ≤ lam)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) :
    (ePathsOfSkew a lam nu T).1 ∈ ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1) := by
  have h := rowLen_mono hnu 0
  have hmem := ePathOfWord_mem a (nu.rowLen 0 + 1) (lam.rowLen 0 - nu.rowLen 0)
    (eColWord a lam nu T 0)
  rwa [show nu.rowLen 0 + 1 + (lam.rowLen 0 - nu.rowLen 0) = lam.rowLen 0 + 1 by omega] at hmem

theorem ePathsOfSkew_snd_mem (hnu : nu ≤ lam)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) :
    (ePathsOfSkew a lam nu T).2 ∈ ePaths a (nu.rowLen 1) (lam.rowLen 1) := by
  have h := rowLen_mono hnu 1
  have hmem := ePathOfWord_mem a (nu.rowLen 1) (lam.rowLen 1 - nu.rowLen 1)
    (eColWord a lam nu T 1)
  rwa [show nu.rowLen 1 + (lam.rowLen 1 - nu.rowLen 1) = lam.rowLen 1 by omega] at hmem

/-- A letter of column `0` below `i` puts its abscissa behind the path at height
`i`: the counting set of a strictly increasing word is an initial segment. -/
theorem lt_ePathsOfSkew_fst (T : BoundedSkewSSYT lam.transpose nu.transpose a) {i j : ℕ}
    (hj : j < lam.rowLen 0 - nu.rowLen 0) (hlt : T.1 (nu.rowLen 0 + j) 0 < i) :
    nu.rowLen 0 + 1 + j < (ePathsOfSkew a lam nu T).1 i := by
  have hsub : Finset.range (j + 1)
      ⊆ (Finset.range (lam.rowLen 0 - nu.rowLen 0)).filter
          fun j' => eColWord a lam nu T 0 j' 0 < i := by
    intro j' hj'
    rw [Finset.mem_range] at hj'
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    refine lt_of_le_of_lt (eColWord_mono T 0 (by omega : j' ≤ j) hj) ?_
    rw [eColWord_apply T 0 hj]
    exact hlt
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  change nu.rowLen 0 + 1 + j < nu.rowLen 0 + 1 + _
  omega

/-- A letter of column `1` at or above `i` stops the path of that column at its
abscissa. -/
theorem ePathsOfSkew_snd_le (T : BoundedSkewSSYT lam.transpose nu.transpose a) {i j : ℕ}
    (hle : i ≤ T.1 (nu.rowLen 1 + j) 1) : (ePathsOfSkew a lam nu T).2 i ≤ nu.rowLen 1 + j := by
  have hsub : ((Finset.range (lam.rowLen 1 - nu.rowLen 1)).filter
      fun j' => eColWord a lam nu T 1 j' 0 < i) ⊆ Finset.range j := by
    intro j' hj'
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    rw [Finset.mem_range]
    by_contra hcon
    have hmono := eColWord_mono T 1 (by omega : j ≤ j') hj'.1
    rw [eColWord_apply T 1 (by omega : j < lam.rowLen 1 - nu.rowLen 1)] at hmono
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  change nu.rowLen 1 + _ ≤ nu.rowLen 1 + j
  omega

/-- **The weak row condition is point disjointness.**  The two odd paths of a
bounded tableau of `λ' / ν'` stay strictly ordered at every height.  Unlike the
even model this needs no gap of a full step: the paths are points, so ordering
alone is disjointness.  This is the converse of `lt_of_not_eMeets`. -/
theorem lt_ePathsOfSkew (hnu : nu ≤ lam) (T : BoundedSkewSSYT lam.transpose nu.transpose a)
    (i : ℕ) : (ePathsOfSkew a lam nu T).2 i < (ePathsOfSkew a lam nu T).1 i := by
  have hnu01 : nu.rowLen 1 ≤ nu.rowLen 0 := nu.rowLen_anti 0 1 (by omega)
  have hlam01 : lam.rowLen 1 ≤ lam.rowLen 0 := lam.rowLen_anti 0 1 (by omega)
  have h0 : nu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hnu 0
  have h1 : nu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hnu 1
  have hqb := hPaths_le (ePaths_mem (ePathsOfSkew_fst_mem hnu T)) i
  have hrb := hPaths_le (ePaths_mem (ePathsOfSkew_snd_mem hnu T)) i
  by_contra hcon
  rw [Nat.not_lt] at hcon
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, (ePathsOfSkew a lam nu T).1 i = j₀ + 1 :=
    ⟨(ePathsOfSkew a lam nu T).1 i - 1, by omega⟩
  have ha : i ≤ T.1 j₀ 0 := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    have hstep := lt_ePathsOfSkew_fst T (j := j₀ - nu.rowLen 0) (by omega)
      (by rw [show nu.rowLen 0 + (j₀ - nu.rowLen 0) = j₀ by omega]; exact hlt)
    omega
  have hb : T.1 j₀ 1 < i := by
    by_contra hgt
    rw [Nat.not_lt] at hgt
    have hstep := ePathsOfSkew_snd_le T (i := i) (j := j₀ - nu.rowLen 1)
      (by rw [show nu.rowLen 1 + (j₀ - nu.rowLen 1) = j₀ by omega]; exact hgt)
    omega
  have hrw : T.1 j₀ 0 ≤ T.1 j₀ 1 :=
    T.1.row_weak (by omega : (0 : ℕ) < 1) (mem_transpose_iff_lt_rowLen.mpr (by omega))
      (fun hc => absurd (mem_transpose_iff_lt_rowLen.mp hc) (by omega))
  omega

theorem not_eMeets_ePathsOfSkew (hnu : nu ≤ lam)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) :
    ¬ EMeets a (ePathsOfSkew a lam nu T).1 (ePathsOfSkew a lam nu T).2 := by
  rintro ⟨k, hk⟩
  exact absurd (lt_ePathsOfSkew hnu T k) (by rw [(mem_eMeetSet.mp hk).2]; omega)

end Paths

/-! ## The tableau of a non-meeting pair

The cell `(j, 0)` reads the letter the first path writes at abscissa `j + 1`,
the cell `(j, 1)` the letter the second writes at `j`.  Columns increase
strictly because the letters of an odd path do; rows increase weakly because the
pair never shares a point.
-/

section Entry

variable {a : ℕ} {lam nu : YoungDiagram}

/-- The filling of `λ' / ν'` read off a pair of odd paths. -/
noncomputable def eSkewEntry (a : ℕ) (lam nu : YoungDiagram) (x : (ℕ → ℕ) × (ℕ → ℕ))
    (j i : ℕ) : ℕ :=
  if (j, i) ∈ skewCells lam.transpose nu.transpose then
    if i = 0 then pathLetter a (nu.rowLen 0 + 1) x.1 (j - nu.rowLen 0)
    else pathLetter a (nu.rowLen 1) x.2 (j - nu.rowLen 1)
  else 0

theorem eSkewEntry_zero (x : (ℕ → ℕ) × (ℕ → ℕ)) {j : ℕ}
    (h : (j, 0) ∈ skewCells lam.transpose nu.transpose) :
    eSkewEntry a lam nu x j 0 = pathLetter a (nu.rowLen 0 + 1) x.1 (j - nu.rowLen 0) := by
  rw [eSkewEntry, if_pos h, if_pos rfl]

theorem eSkewEntry_one (x : (ℕ → ℕ) × (ℕ → ℕ)) {j : ℕ}
    (h : (j, 1) ∈ skewCells lam.transpose nu.transpose) :
    eSkewEntry a lam nu x j 1 = pathLetter a (nu.rowLen 1) x.2 (j - nu.rowLen 1) := by
  rw [eSkewEntry, if_pos h, if_neg (by omega : ¬ (1 : ℕ) = 0)]

theorem eSkewEntry_of_notMem (x : (ℕ → ℕ) × (ℕ → ℕ)) {i j : ℕ}
    (h : (j, i) ∉ skewCells lam.transpose nu.transpose) : eSkewEntry a lam nu x j i = 0 :=
  if_neg h

/-- **The row of a two-column filling increases weakly.**  The letter the
left-hand path writes at `j + 1` is at most the one the right-hand path writes
at `j`, because point disjointness orders the two profiles at every height —
including the height at which the right-hand path passes `j`. -/
theorem eSkewEntry_row_weak {x : (ℕ → ℕ) × (ℕ → ℕ)}
    (hq : x.1 ∈ ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ ePaths a (nu.rowLen 1) (lam.rowLen 1)) (hnm : ¬ EMeets a x.1 x.2) {j : ℕ}
    (hc₀ : (j, 0) ∈ skewCells lam.transpose nu.transpose)
    (hc₁ : (j, 1) ∈ skewCells lam.transpose nu.transpose) :
    eSkewEntry a lam nu x j 0 ≤ eSkewEntry a lam nu x j 1 := by
  have hnu01 : nu.rowLen 1 ≤ nu.rowLen 0 := nu.rowLen_anti 0 1 (by omega)
  obtain ⟨hj0, hj0'⟩ := mem_skewCells_transpose.mp hc₀
  obtain ⟨hj1, hj1'⟩ := mem_skewCells_transpose.mp hc₁
  rw [eSkewEntry_zero x hc₀, eSkewEntry_one x hc₁]
  have hMa : pathLetter a (nu.rowLen 1) x.2 (j - nu.rowLen 1) < a :=
    pathLetter_lt_height (ePaths_mem hr) (by omega)
  have hjr : j < x.2 (pathLetter a (nu.rowLen 1) x.2 (j - nu.rowLen 1) + 1) := by
    have h := (pathLetter_lt_iff (ePaths_mem hr)
      (show pathLetter a (nu.rowLen 1) x.2 (j - nu.rowLen 1) + 1 ≤ a by omega)).mp
      (Nat.lt_succ_self _)
    omega
  have hsep := lt_of_not_eMeets hq hr (by omega) hnm
    (pathLetter a (nu.rowLen 1) x.2 (j - nu.rowLen 1) + 1) (by omega)
  have hlt := (pathLetter_lt_iff (ePaths_mem hq)
    (show pathLetter a (nu.rowLen 1) x.2 (j - nu.rowLen 1) + 1 ≤ a by omega)).mpr
    (show nu.rowLen 0 + 1 + (j - nu.rowLen 0)
        < x.1 (pathLetter a (nu.rowLen 1) x.2 (j - nu.rowLen 1) + 1) by omega)
  omega

/-- **The column of a filling read off an odd path increases strictly.**  This
is the unit step of the odd model: `pathLetter_strictMono`. -/
theorem eSkewEntry_col_strict {x : (ℕ → ℕ) × (ℕ → ℕ)} (hnu : nu ≤ lam)
    (hq : x.1 ∈ ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ ePaths a (nu.rowLen 1) (lam.rowLen 1)) {i j₁ j₂ : ℕ} (hi : i < 2)
    (hj : j₁ < j₂) (hc₁ : (j₁, i) ∈ skewCells lam.transpose nu.transpose)
    (hc₂ : (j₂, i) ∈ skewCells lam.transpose nu.transpose) :
    eSkewEntry a lam nu x j₁ i < eSkewEntry a lam nu x j₂ i := by
  have h0 : nu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hnu 0
  have h1 : nu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hnu 1
  obtain ⟨hj₁, hj₁'⟩ := mem_skewCells_transpose.mp hc₁
  obtain ⟨hj₂, hj₂'⟩ := mem_skewCells_transpose.mp hc₂
  interval_cases i
  · rw [eSkewEntry_zero x hc₁, eSkewEntry_zero x hc₂]
    refine pathLetter_strictMono (m := lam.rowLen 0 - nu.rowLen 0) ?_ (by omega) (by omega)
    rwa [show nu.rowLen 0 + 1 + (lam.rowLen 0 - nu.rowLen 0) = lam.rowLen 0 + 1 by omega]
  · rw [eSkewEntry_one x hc₁, eSkewEntry_one x hc₂]
    refine pathLetter_strictMono (m := lam.rowLen 1 - nu.rowLen 1) ?_ (by omega) (by omega)
    rwa [show nu.rowLen 1 + (lam.rowLen 1 - nu.rowLen 1) = lam.rowLen 1 by omega]

/-- The bounded tableau of the conjugate shape that a non-meeting pair of odd
paths carries. -/
noncomputable def eSkewOfPaths (hnu : nu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0)
    {x : (ℕ → ℕ) × (ℕ → ℕ)} (hq : x.1 ∈ ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ ePaths a (nu.rowLen 1) (lam.rowLen 1)) (hnm : ¬ EMeets a x.1 x.2) :
    BoundedSkewSSYT lam.transpose nu.transpose a :=
  ⟨{ entry := eSkewEntry a lam nu x
     row_weak' := by
       intro j i₁ i₂ hi hlam hnnu
       have hi₂ : i₂ < 2 := by
         by_contra hc
         have hlt := mem_transpose_iff_lt_rowLen.mp hlam
         rw [hrow i₂ (by omega)] at hlt
         omega
       obtain rfl : i₂ = 1 := by omega
       obtain rfl : i₁ = 0 := by omega
       have hj1 : j < lam.rowLen 1 := mem_transpose_iff_lt_rowLen.mp hlam
       have hj0 : nu.rowLen 0 ≤ j := by
         by_contra hc
         exact hnnu (mem_transpose_iff_lt_rowLen.mpr (by omega))
       have hnu01 : nu.rowLen 1 ≤ nu.rowLen 0 := nu.rowLen_anti 0 1 (by omega)
       have hlam01 : lam.rowLen 1 ≤ lam.rowLen 0 := lam.rowLen_anti 0 1 (by omega)
       exact eSkewEntry_row_weak hq hr hnm (mem_skewCells_transpose.mpr ⟨hj0, by omega⟩)
         (mem_skewCells_transpose.mpr ⟨by omega, hj1⟩)
     col_strict' := by
       intro j₁ j₂ i hj hlam hnnu
       have hi : i < 2 := by
         by_contra hc
         have hlt := mem_transpose_iff_lt_rowLen.mp hlam
         rw [hrow i (by omega)] at hlt
         omega
       have hj₂' : j₂ < lam.rowLen i := mem_transpose_iff_lt_rowLen.mp hlam
       have hj₁ : nu.rowLen i ≤ j₁ := by
         by_contra hc
         exact hnnu (mem_transpose_iff_lt_rowLen.mpr (by omega))
       exact eSkewEntry_col_strict hnu hq hr hi hj
         (mem_skewCells_transpose.mpr ⟨hj₁, by omega⟩)
         (mem_skewCells_transpose.mpr ⟨by omega, hj₂'⟩)
     zeros' := fun hc => eSkewEntry_of_notMem x hc },
   by
     intro j i hcell
     have hi := lt_two_of_mem_skewCells_transpose hrow hcell
     obtain ⟨hj, hj'⟩ := mem_skewCells_transpose.mp hcell
     change eSkewEntry a lam nu x j i < a
     interval_cases i
     · rw [eSkewEntry_zero x hcell]
       exact pathLetter_lt_height (ePaths_mem hq) (by omega)
     · rw [eSkewEntry_one x hcell]
       exact pathLetter_lt_height (ePaths_mem hr) (by omega)⟩

theorem eSkewOfPaths_apply (hnu : nu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0)
    {x : (ℕ → ℕ) × (ℕ → ℕ)} (hq : x.1 ∈ ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ ePaths a (nu.rowLen 1) (lam.rowLen 1)) (hnm : ¬ EMeets a x.1 x.2) (j i : ℕ) :
    (eSkewOfPaths hnu hrow hq hr hnm).1 j i = eSkewEntry a lam nu x j i :=
  rfl

end Entry

/-! ## The two round trips -/

section RoundTrips

variable {a : ℕ} {lam nu : YoungDiagram}

/-- Two one-column words agreeing on their cells trace the same odd path. -/
theorem ePathOfWord_congr {m s : ℕ} (T T' : BoundedSSYT (rect m 1) a)
    (h : ∀ j, j < m → T j 0 = T' j 0) : ePathOfWord a s m T = ePathOfWord a s m T' := by
  funext i
  have hset : ((Finset.range m).filter fun j => T j 0 < i)
      = (Finset.range m).filter fun j => T' j 0 < i := by
    ext j
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hj, hlt⟩
      exact ⟨hj, by rwa [← h j (Finset.mem_range.mp hj)]⟩
    · rintro ⟨hj, hlt⟩
      exact ⟨hj, by rwa [h j (Finset.mem_range.mp hj)]⟩
  change s + ((Finset.range m).filter fun j => T j 0 < i).card
      = s + ((Finset.range m).filter fun j => T' j 0 < i).card
  rw [hset]

/-- A one-column word whose letters are those of an odd path traces that path
back. -/
theorem ePathOfWord_eq_of_entry {s m : ℕ} {q : ℕ → ℕ} (hq : q ∈ ePaths a s (s + m))
    (T : BoundedSSYT (rect m 1) a) (h : ∀ j, j < m → T j 0 = pathLetter a s q j) :
    ePathOfWord a s m T = q := by
  rw [← ePathOfWord_eWordOfPath hq]
  exact ePathOfWord_congr T _ fun j hj => by
    rw [h j hj, eWordOfPath_apply, if_pos ⟨rfl, hj⟩]

/-- Paths to tableau and back. -/
theorem ePathsOfSkew_eSkewOfPaths (hnu : nu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0)
    {x : (ℕ → ℕ) × (ℕ → ℕ)} (hq : x.1 ∈ ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ ePaths a (nu.rowLen 1) (lam.rowLen 1)) (hnm : ¬ EMeets a x.1 x.2) :
    ePathsOfSkew a lam nu (eSkewOfPaths hnu hrow hq hr hnm) = x := by
  have h0 : nu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hnu 0
  have h1 : nu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hnu 1
  have hq' : x.1 ∈ ePaths a (nu.rowLen 0 + 1)
      (nu.rowLen 0 + 1 + (lam.rowLen 0 - nu.rowLen 0)) := by
    rwa [show nu.rowLen 0 + 1 + (lam.rowLen 0 - nu.rowLen 0) = lam.rowLen 0 + 1 by omega]
  have hr' : x.2 ∈ ePaths a (nu.rowLen 1) (nu.rowLen 1 + (lam.rowLen 1 - nu.rowLen 1)) := by
    rwa [show nu.rowLen 1 + (lam.rowLen 1 - nu.rowLen 1) = lam.rowLen 1 by omega]
  refine Prod.ext ?_ ?_
  · refine ePathOfWord_eq_of_entry hq' _ fun j hj => ?_
    rw [eColWord_apply _ 0 hj, eSkewOfPaths_apply,
      eSkewEntry_zero x (mem_skewCells_transpose_col 0 hj),
      show nu.rowLen 0 + j - nu.rowLen 0 = j by omega]
  · refine ePathOfWord_eq_of_entry hr' _ fun j hj => ?_
    rw [eColWord_apply _ 1 hj, eSkewOfPaths_apply,
      eSkewEntry_one x (mem_skewCells_transpose_col 1 hj),
      show nu.rowLen 1 + j - nu.rowLen 1 = j by omega]

/-- Tableau to paths and back. -/
theorem eSkewOfPaths_ePathsOfSkew (hnu : nu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0)
    (T : BoundedSkewSSYT lam.transpose nu.transpose a) {hq hr hnm} :
    eSkewOfPaths (x := ePathsOfSkew a lam nu T) hnu hrow hq hr hnm = T := by
  refine BoundedSkewSSYT.ext fun j i => ?_
  change eSkewEntry a lam nu (ePathsOfSkew a lam nu T) j i = T.1 j i
  by_cases hcell : (j, i) ∈ skewCells lam.transpose nu.transpose
  · have hi := lt_two_of_mem_skewCells_transpose hrow hcell
    obtain ⟨hj, hj'⟩ := mem_skewCells_transpose.mp hcell
    have h0 : nu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hnu 0
    have h1 : nu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hnu 1
    interval_cases i
    · rw [eSkewEntry_zero _ hcell]
      change pathLetter a (nu.rowLen 0 + 1)
        (ePathOfWord a (nu.rowLen 0 + 1) (lam.rowLen 0 - nu.rowLen 0) (eColWord a lam nu T 0))
        (j - nu.rowLen 0) = _
      rw [pathLetter_ePathOfWord _ (show j - nu.rowLen 0 < lam.rowLen 0 - nu.rowLen 0 by omega),
        eColWord_apply T 0 (by omega), show nu.rowLen 0 + (j - nu.rowLen 0) = j by omega]
    · rw [eSkewEntry_one _ hcell]
      change pathLetter a (nu.rowLen 1)
        (ePathOfWord a (nu.rowLen 1) (lam.rowLen 1 - nu.rowLen 1) (eColWord a lam nu T 1))
        (j - nu.rowLen 1) = _
      rw [pathLetter_ePathOfWord _ (show j - nu.rowLen 1 < lam.rowLen 1 - nu.rowLen 1 by omega),
        eColWord_apply T 1 (by omega), show nu.rowLen 1 + (j - nu.rowLen 1) = j by omega]
  · rw [eSkewEntry_of_notMem _ hcell]
    exact (T.zeros hcell).symm

end RoundTrips

/-! ## Weights

The product over the cells of `λ' / ν'` splits into its two columns, and each
column is the weight of its path: `pathWeight_eq_prod_letters` reads a path
weight as the product over its letters, which is what the column of the tableau
holds.
-/

section Weights

variable {a : ℕ} {lam nu : YoungDiagram}

theorem prod_skewCells_transpose_two_cols {M : Type*} [CommMonoid M]
    (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) (f : ℕ → ℕ → M) :
    ∏ c ∈ skewCells lam.transpose nu.transpose, f c.1 c.2
      = (∏ j ∈ Finset.Ico (nu.rowLen 0) (lam.rowLen 0), f j 0)
        * ∏ j ∈ Finset.Ico (nu.rowLen 1) (lam.rowLen 1), f j 1 := by
  have hsplit : skewCells lam.transpose nu.transpose
      = (Finset.Ico (nu.rowLen 0) (lam.rowLen 0) ×ˢ ({0} : Finset ℕ))
        ∪ (Finset.Ico (nu.rowLen 1) (lam.rowLen 1) ×ˢ ({1} : Finset ℕ)) := by
    ext c
    obtain ⟨j, i⟩ := c
    rw [Finset.mem_union, Finset.mem_product, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_singleton, Finset.mem_Ico, Finset.mem_Ico]
    constructor
    · intro hc
      obtain ⟨hj1, hj2⟩ := mem_skewCells_transpose.mp hc
      have hi := lt_two_of_mem_skewCells_transpose hrow hc
      interval_cases i
      · exact Or.inl ⟨⟨hj1, hj2⟩, rfl⟩
      · exact Or.inr ⟨⟨hj1, hj2⟩, rfl⟩
    · rintro (⟨⟨h1, h2⟩, rfl⟩ | ⟨⟨h1, h2⟩, rfl⟩) <;>
        exact mem_skewCells_transpose.mpr ⟨h1, h2⟩
  have hdisj : Disjoint (Finset.Ico (nu.rowLen 0) (lam.rowLen 0) ×ˢ ({0} : Finset ℕ))
      (Finset.Ico (nu.rowLen 1) (lam.rowLen 1) ×ˢ ({1} : Finset ℕ)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rw [Finset.mem_product, Finset.mem_singleton] at hc1 hc2
    exact absurd (hc1.2.symm.trans hc2.2) (by omega)
  rw [hsplit, Finset.prod_union hdisj, Finset.prod_product', Finset.prod_product']
  simp only [Finset.prod_singleton]

variable {R : Type*} [CommRing R]

/-- The weight of a non-meeting pair of odd paths is the weight of the tableau
of the conjugate shape it carries. -/
theorem prod_skewCells_transpose_eq_pathWeight (hnu : nu ≤ lam)
    (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) (α : ℕ → R) {x : (ℕ → ℕ) × (ℕ → ℕ)}
    (hq : x.1 ∈ ePaths a (nu.rowLen 0 + 1) (lam.rowLen 0 + 1))
    (hr : x.2 ∈ ePaths a (nu.rowLen 1) (lam.rowLen 1)) :
    pathWeight a α x.1 * pathWeight a α x.2
      = ∏ c ∈ skewCells lam.transpose nu.transpose, α (eSkewEntry a lam nu x c.1 c.2) := by
  have h0 : nu.rowLen 0 ≤ lam.rowLen 0 := rowLen_mono hnu 0
  have h1 : nu.rowLen 1 ≤ lam.rowLen 1 := rowLen_mono hnu 1
  have hq' : x.1 ∈ hPaths a (nu.rowLen 0 + 1)
      (nu.rowLen 0 + 1 + (lam.rowLen 0 - nu.rowLen 0)) := by
    rw [show nu.rowLen 0 + 1 + (lam.rowLen 0 - nu.rowLen 0) = lam.rowLen 0 + 1 by omega]
    exact ePaths_mem hq
  have hr' : x.2 ∈ hPaths a (nu.rowLen 1) (nu.rowLen 1 + (lam.rowLen 1 - nu.rowLen 1)) := by
    rw [show nu.rowLen 1 + (lam.rowLen 1 - nu.rowLen 1) = lam.rowLen 1 by omega]
    exact ePaths_mem hr
  rw [prod_skewCells_transpose_two_cols hrow fun j i => α (eSkewEntry a lam nu x j i),
    pathWeight_eq_prod_letters hq' α, pathWeight_eq_prod_letters hr' α,
    Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [eSkewEntry_zero x (mem_skewCells_transpose_col 0 (Finset.mem_range.mp hj)),
      show nu.rowLen 0 + j - nu.rowLen 0 = j by omega]
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [eSkewEntry_one x (mem_skewCells_transpose_col 1 (Finset.mem_range.mp hj)),
      show nu.rowLen 1 + j - nu.rowLen 1 = j by omega]

end Weights

/-! ## The identity, and what it closes

`NonMeetingIsSkewSchurTranspose` is now a theorem: the two constructions are
mutually inverse and weight-preserving, so the non-meeting pairs of odd paths
and the tableaux of `λ' / ν'` have the same generating function.
-/

section Identity

variable {R : Type*} [CommRing R]

/-- **The odd tableau bijection.**  For a pair of shapes with `λ` inside two
rows, the non-meeting pairs of odd paths carry the total weight of the
semistandard tableaux of the conjugate skew shape `λ' / ν'`.  This is the odd
counterpart of `nonCrossingIsSkewSchur`, and it holds at every `a` and `α` over
any commutative ring. -/
theorem nonMeetingIsSkewSchurTranspose (a : ℕ) (α : ℕ → R) :
    NonMeetingIsSkewSchurTranspose a α := by
  intro lam nu hnu hrow
  rw [skewSchur]
  refine Finset.sum_bij'
    (fun x hx => eSkewOfPaths (x := x) hnu hrow
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
      (Finset.mem_filter.mp hx).2)
    (fun T _ => ePathsOfSkew a lam nu T) (fun x _ => Finset.mem_univ _) (fun T _ => ?_)
    (fun x hx => ?_) (fun T _ => eSkewOfPaths_ePathsOfSkew hnu hrow T) (fun x hx => ?_)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨ePathsOfSkew_fst_mem hnu T, ePathsOfSkew_snd_mem hnu T⟩, not_eMeets_ePathsOfSkew hnu T⟩
  · exact ePathsOfSkew_eSkewOfPaths hnu hrow _ _ _
  · exact prod_skewCells_transpose_eq_pathWeight hnu hrow α
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2

/-- **the super branching rule at two rows, unconditionally.**  Both tableau
bijections the splice of `Shields.LGVOdd` consumes are theorems — the even
one is `nonCrossingIsSkewSchur`, the odd one is `nonMeetingIsSkewSchurTranspose`
— so the non-intersecting pairs of mixed paths carry the branching sum
`superSkewSchur lam mu b a β α` with no hypothesis beyond the shape.

This is `SkewJT.sum_nonMeeting_mixed_eq_superSkewSchur_of_odd` with its last
hypothesis discharged. -/
theorem sum_nonMeeting_mixed_eq_superSkewSchur_uncond {b a : ℕ} {β α : ℕ → R}
    (lam mu : YoungDiagram) (hmu : mu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) :
    ∑ x ∈ (mixedPaths b a (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
            mixedPaths b a (mu.rowLen 1) (lam.rowLen 1)).filter
              fun x => ¬ MixedMeets b a x.1 x.2,
        mixedWeight b a β α x.1 * mixedWeight b a β α x.2
      = superSkewSchur lam mu b a β α :=
  sum_nonMeeting_mixed_eq_superSkewSchur_of_odd (nonMeetingIsSkewSchurTranspose a α)
    lam mu hmu hrow

/-! ## Non-vacuity

The smallest instance where the odd cancellation fires, evaluated.
-/

/-- On the column `λ = (1, 1)` the conjugate shape is the row `(2)`, so the
`2 × 2` determinant over the odd alphabet is a *complete* homogeneous
polynomial: `e_1^2 - e_2 e_0 = h_2(α_0, …, α_{a-1})`.  The transpose is what
carries the elementary alphabet to the complete one, which is why the even
statement of `nonCrossingIsSkewSchur` cannot be read here with the shapes left
alone. -/
theorem elemDet_two_column (a : ℕ) (α : ℕ → R) :
    jacobiTrudiDet (fun m => elemHom a m α) (rect 2 1) ⊥ 2 = completeHom a 2 α := by
  have hbot : (⊥ : YoungDiagram).transpose = ⊥ := by
    ext c
    simp
  rw [elemDet_two_eq_sum_nonMeeting,
    nonMeetingIsSkewSchurTranspose a α (rect 2 1) ⊥ bot_le
      (fun i hi => rowLen_rect_of_le (by omega)),
    transpose_rect, hbot, completeHom]

end Identity

end Shields
