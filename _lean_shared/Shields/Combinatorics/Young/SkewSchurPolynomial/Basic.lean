/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Shields.Combinatorics.Young.SchurPolynomial
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

/-!
# Skew Young diagrams, skew tableaux, and the skew Schur polynomial

Mathlib has no skew Young diagram and no skew Schur polynomial.  This file supplies them, over
the one-alphabet straight-shape theory of `Shields.Combinatorics.Young.SchurPolynomial`, and
closes with the interval of Young diagrams the Berele--Regev branching sum in
`Shields.Combinatorics.Young.SkewSchurPolynomial.Super` runs over.

## Main definitions

* `Shields.skewCells`, `Shields.SkewSSYT`, `Shields.BoundedSkewSSYT`: the skew diagram
  `lam.cells \ mu.cells`, its semistandard fillings, and those with entries `< n`, with a
  `Fintype` instance.  A skew row and a skew column are each an interval, so both order
  conditions need only their endpoints: `mu` is a lower set, so `(i, j₁) ∉ mu` already gives
  `(i, j₂) ∉ mu` for `j₁ ≤ j₂`.
* `Shields.skewSchur`: the skew Schur polynomial `s_{λ/μ}(x_0, …, x_{n-1})`, the generating
  function of `BoundedSkewSSYT` weighted by `∏` over the skew cells.
* `Shields.youngIcc`: the Young diagrams `nu` with `mu ⊆ nu ⊆ lam`, as a `Finset`.  Mathlib has
  no `LocallyFiniteOrder` on `YoungDiagram`, so it is built from injectivity of `cells`.

## Main statements

* `Shields.skewSchur_pos_iff`: over `ℝ` with positive variables, `s_{λ/μ}` is positive exactly
  when every column of `lam/mu` has height at most `n`.  The witness for the positive half is
  `skewHighestWeight`, whose entry at `(i, j)` is `i - mu.colLen j`.  This is the hook
  criterion at zero odd variables.
* `Shields.skewColLen_transpose`: conjugation turns the column bound on
  `lam.transpose / nu.transpose` into the row bound on `lam / nu`, so the second factor of the
  branching sum needs no separate argument.

## Tags

Schur polynomial, skew Schur, Young diagram, semistandard tableau
-/

namespace Shields

open Finset

/-! ## Skew shapes

A skew diagram is a pair of Young diagrams, its cells the set difference.  The
containment `mu ≤ lam` is not part of the definition and is assumed only where
it is used.
-/

/-- The cells of the skew diagram `lam / mu`. -/
def skewCells (lam mu : YoungDiagram) : Finset (ℕ × ℕ) := lam.cells \ mu.cells

@[simp]
theorem mem_skewCells {lam mu : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ skewCells lam mu ↔ c ∈ lam ∧ c ∉ mu := by
  simp [skewCells, YoungDiagram.mem_cells]

theorem skewCells_bot (lam : YoungDiagram) : skewCells lam ⊥ = lam.cells := by
  ext c
  simp

theorem skewCells_eq_empty_iff {lam mu : YoungDiagram} :
    skewCells lam mu = ∅ ↔ lam ≤ mu := by
  rw [skewCells, Finset.sdiff_eq_empty_iff_subset, YoungDiagram.cells_subset_iff]

/-- A Young diagram is a lower set, so a cell missing from `mu` stays missing
below it in its column. -/
theorem notMem_of_row_le {mu : YoungDiagram} {i i' j : ℕ} (h : i ≤ i')
    (hi : (i, j) ∉ mu) : (i', j) ∉ mu := fun hc => hi (mu.up_left_mem h le_rfl hc)

/-- A Young diagram is a lower set, so a cell missing from `mu` stays missing to
the right of it in its row. -/
theorem notMem_of_col_le {mu : YoungDiagram} {i j j' : ℕ} (h : j ≤ j')
    (hj : (i, j) ∉ mu) : (i, j') ∉ mu := fun hc => hj (mu.up_left_mem le_rfl h hc)

/-- The height of column `j` of `lam / mu`. -/
def skewColLen (lam mu : YoungDiagram) (j : ℕ) : ℕ := lam.colLen j - mu.colLen j

/-- The length of row `i` of `lam / mu`. -/
def skewRowLen (lam mu : YoungDiagram) (i : ℕ) : ℕ := lam.rowLen i - mu.rowLen i

/-- Conjugating a skew shape exchanges its column heights with its row lengths.
This is what lets the second factor of the branching formula, a skew Schur
function of the conjugate shape, be governed by the row lengths of `lam / nu`. -/
theorem skewColLen_transpose (lam mu : YoungDiagram) (i : ℕ) :
    skewColLen lam.transpose mu.transpose i = skewRowLen lam mu i := by
  simp [skewColLen, skewRowLen, YoungDiagram.colLen_transpose]

/-- A nonempty skew shape has a column of positive height. -/
theorem exists_skewColLen_pos {lam mu : YoungDiagram} (h : skewCells lam mu ≠ ∅) :
    ∃ j, 0 < skewColLen lam mu j := by
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr h
  obtain ⟨hlam, hmu⟩ := mem_skewCells.mp hc
  refine ⟨c.2, ?_⟩
  have h1 : c.1 < lam.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.mp hlam
  have h2 : ¬ c.1 < mu.colLen c.2 := fun h => hmu (YoungDiagram.mem_iff_lt_colLen.mpr h)
  simp only [skewColLen]
  omega

/-! ## Semistandard tableaux of a skew shape

The row and column conditions are stated exactly as Mathlib states them for a
straight shape, with the extra clause that the *first* of the two cells is
outside `mu`.  That clause propagates to the second cell by `notMem_of_row_le`
and `notMem_of_col_le`, so both cells are in the skew shape.
-/

/-- A semistandard Young tableau of the skew shape `lam / mu`: a filling by
naturals, weakly increasing along rows, strictly increasing down columns, and
zero off the skew cells. -/
structure SkewSSYT (lam mu : YoungDiagram) where
  /-- The entry at `(i, j)`. -/
  entry : ℕ → ℕ → ℕ
  /-- Entries weakly increase along a row of the skew shape. -/
  row_weak' : ∀ {i j₁ j₂ : ℕ}, j₁ < j₂ → (i, j₂) ∈ lam → (i, j₁) ∉ mu →
    entry i j₁ ≤ entry i j₂
  /-- Entries strictly increase down a column of the skew shape. -/
  col_strict' : ∀ {i₁ i₂ j : ℕ}, i₁ < i₂ → (i₂, j) ∈ lam → (i₁, j) ∉ mu →
    entry i₁ j < entry i₂ j
  /-- The filling vanishes off the skew shape. -/
  zeros' : ∀ {i j : ℕ}, (i, j) ∉ skewCells lam mu → entry i j = 0

namespace SkewSSYT

variable {lam mu : YoungDiagram}

instance instFunLike : FunLike (SkewSSYT lam mu) ℕ (ℕ → ℕ) where
  coe := SkewSSYT.entry
  coe_injective T T' h := by
    cases T
    cases T'
    congr

theorem row_weak (T : SkewSSYT lam mu) {i j₁ j₂ : ℕ} (hj : j₁ < j₂)
    (hlam : (i, j₂) ∈ lam) (hmu : (i, j₁) ∉ mu) : T i j₁ ≤ T i j₂ :=
  T.row_weak' hj hlam hmu

theorem col_strict (T : SkewSSYT lam mu) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hlam : (i₂, j) ∈ lam) (hmu : (i₁, j) ∉ mu) : T i₁ j < T i₂ j :=
  T.col_strict' hi hlam hmu

theorem zeros (T : SkewSSYT lam mu) {i j : ℕ} (h : (i, j) ∉ skewCells lam mu) :
    T i j = 0 :=
  T.zeros' h

@[ext]
theorem ext {T T' : SkewSSYT lam mu} (h : ∀ i j, T i j = T' i j) : T = T' :=
  DFunLike.ext T T' fun _ => funext fun _ => h _ _

/-- Along a column of the skew shape, an entry exceeds a higher one by at least
the row gap.  Iterating `col_strict`, as `SemistandardYoungTableau` does on a
straight shape. -/
theorem entry_add_sub_le (T : SkewSSYT lam mu) (i j : ℕ) (hmu : (i, j) ∉ mu) :
    ∀ i' : ℕ, i ≤ i' → (i', j) ∈ lam → T i j + (i' - i) ≤ T i' j := by
  intro i' hi
  induction i', hi using Nat.le_induction with
  | base => intro _; simp
  | succ i' hii' ih =>
    intro hcell
    have hcell' : (i', j) ∈ lam := lam.up_left_mem (Nat.le_succ i') le_rfl hcell
    have h1 := ih hcell'
    have h2 : T i' j < T (i' + 1) j :=
      T.col_strict (Nat.lt_succ_self i') hcell (notMem_of_row_le hii' hmu)
    omega

/-- A skew cell in row `i` of column `j` carries an entry of at least
`i - mu.colLen j`: the skew part of the column starts at row `mu.colLen j`, and
the entries from there down are strictly increasing. -/
theorem sub_colLen_le_entry (T : SkewSSYT lam mu) {i j : ℕ}
    (hcell : (i, j) ∈ skewCells lam mu) : i - mu.colLen j ≤ T i j := by
  obtain ⟨hlam, hmu⟩ := mem_skewCells.mp hcell
  have htop : (mu.colLen j, j) ∉ mu := fun hc =>
    absurd (YoungDiagram.mem_iff_lt_colLen.mp hc) (lt_irrefl _)
  have hle : mu.colLen j ≤ i := by
    by_contra h
    exact hmu (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
  have := T.entry_add_sub_le (mu.colLen j) j htop i hle hlam
  omega

end SkewSSYT

/-! ## Bounded skew tableaux and their finiteness -/

/-- The semistandard tableaux of skew shape `lam / mu` whose entries on the skew
cells are all `< n`: those contributing to a skew Schur polynomial in the `n`
variables `x 0, …, x (n-1)`.

As in `Shields.BoundedSSYT` the bound is imposed on the skew cells only, so
that an empty skew shape keeps its one tableau at `n = 0`. -/
def BoundedSkewSSYT (lam mu : YoungDiagram) (n : ℕ) : Type :=
  {T : SkewSSYT lam mu // ∀ i j, (i, j) ∈ skewCells lam mu → T i j < n}

namespace BoundedSkewSSYT

variable {lam mu : YoungDiagram} {n : ℕ}

instance : CoeFun (BoundedSkewSSYT lam mu n) fun _ => ℕ → ℕ → ℕ where
  coe T := T.1

theorem ext {T T' : BoundedSkewSSYT lam mu n} (h : ∀ i j, T i j = T' i j) : T = T' :=
  Subtype.ext (SkewSSYT.ext h)

theorem lt_of_mem_cells (T : BoundedSkewSSYT lam mu n) {c : ℕ × ℕ}
    (hc : c ∈ skewCells lam mu) : T c.1 c.2 < n :=
  T.2 c.1 c.2 hc

theorem zeros (T : BoundedSkewSSYT lam mu n) {i j : ℕ}
    (h : (i, j) ∉ skewCells lam mu) : T i j = 0 :=
  T.1.zeros h

/-- A bounded skew tableau is determined by its restriction to the skew cells,
and that restriction is a map `skewCells lam mu → Fin n`. -/
theorem restrict_injective (lam mu : YoungDiagram) (n : ℕ) :
    Function.Injective fun (T : BoundedSkewSSYT lam mu n) (c : skewCells lam mu) =>
      (⟨T c.1.1 c.1.2, T.lt_of_mem_cells c.2⟩ : Fin n) := by
  intro T T' h
  refine BoundedSkewSSYT.ext fun i j => ?_
  by_cases hc : (i, j) ∈ skewCells lam mu
  · exact congrArg Fin.val (congrFun h ⟨(i, j), hc⟩)
  · rw [T.zeros hc, T'.zeros hc]

noncomputable instance instFintype (lam mu : YoungDiagram) (n : ℕ) :
    Fintype (BoundedSkewSSYT lam mu n) :=
  Fintype.ofInjective _ (restrict_injective lam mu n)

/-- Every column of `lam / mu` is at most `n` tall once a bounded skew tableau
exists: the bottom cell of column `j` is a skew cell whose entry is at least the
column height minus one, and at the same time less than `n`. -/
theorem skewColLen_le (T : BoundedSkewSSYT lam mu n) (j : ℕ) :
    skewColLen lam mu j ≤ n := by
  by_cases h : lam.colLen j ≤ mu.colLen j
  · simp only [skewColLen]; omega
  · have hlam : (lam.colLen j - 1, j) ∈ lam :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hmu : (lam.colLen j - 1, j) ∉ mu := fun hc =>
      absurd (YoungDiagram.mem_iff_lt_colLen.mp hc) (by omega)
    have hcell : (lam.colLen j - 1, j) ∈ skewCells lam mu := mem_skewCells.mpr ⟨hlam, hmu⟩
    have h1 : lam.colLen j - 1 - mu.colLen j ≤ T.1 (lam.colLen j - 1) j :=
      T.1.sub_colLen_le_entry hcell
    have h2 : T.1 (lam.colLen j - 1) j < n := T.lt_of_mem_cells hcell
    simp only [skewColLen]
    omega

/-- The skew analogue of `highestWeight`: fill the skew cell `(i, j)` with
`i - mu.colLen j`, so that each column of the skew shape reads `0, 1, 2, …` from
its top.  It is entry-bounded by `n` exactly when every column of `lam / mu` has
height at most `n`. -/
def skewHighestWeight (lam mu : YoungDiagram) (n : ℕ)
    (h : ∀ j, skewColLen lam mu j ≤ n) : BoundedSkewSSYT lam mu n := by
  refine ⟨{ entry := fun i j => if (i, j) ∈ skewCells lam mu then i - mu.colLen j else 0
            row_weak' := ?_, col_strict' := ?_, zeros' := ?_ }, ?_⟩
  · intro i j₁ j₂ hj hlam hmu
    have hc₂ : (i, j₂) ∈ skewCells lam mu :=
      mem_skewCells.mpr ⟨hlam, notMem_of_col_le hj.le hmu⟩
    have hc₁ : (i, j₁) ∈ skewCells lam mu :=
      mem_skewCells.mpr ⟨lam.up_left_mem le_rfl hj.le hlam, hmu⟩
    rw [if_pos hc₁, if_pos hc₂]
    have := mu.colLen_anti j₁ j₂ hj.le
    omega
  · intro i₁ i₂ j hi hlam hmu
    have hc₁ : (i₁, j) ∈ skewCells lam mu :=
      mem_skewCells.mpr ⟨lam.up_left_mem hi.le le_rfl hlam, hmu⟩
    have hc₂ : (i₂, j) ∈ skewCells lam mu :=
      mem_skewCells.mpr ⟨hlam, notMem_of_row_le hi.le hmu⟩
    rw [if_pos hc₁, if_pos hc₂]
    have hge : mu.colLen j ≤ i₁ := by
      by_contra hlt
      exact hmu (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
    omega
  · intro i j hc
    exact if_neg hc
  · intro i j hc
    change (if (i, j) ∈ skewCells lam mu then i - mu.colLen j else 0) < n
    rw [if_pos hc]
    obtain ⟨hlam, hmu⟩ := mem_skewCells.mp hc
    have h1 : i < lam.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hlam
    have h2 : mu.colLen j ≤ i := by
      by_contra hlt
      exact hmu (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
    have h3 := h j
    simp only [skewColLen] at h3
    omega

/-- On an empty skew shape the zero filling is a tableau: the column condition
has contradictory hypotheses there. -/
def ofEmpty (lam mu : YoungDiagram) (n : ℕ) (h : skewCells lam mu = ∅) :
    BoundedSkewSSYT lam mu n :=
  ⟨{ entry := fun _ _ => 0
     row_weak' := fun _ _ _ => le_rfl
     col_strict' := by
       intro i₁ i₂ j hi hlam hmu
       have : (i₁, j) ∈ skewCells lam mu :=
         mem_skewCells.mpr ⟨lam.up_left_mem hi.le le_rfl hlam, hmu⟩
       rw [h] at this
       exact absurd this (Finset.notMem_empty _)
     zeros' := fun _ => rfl },
   by intro i j hc; rw [h] at hc; exact absurd hc (Finset.notMem_empty _)⟩

/-- An empty skew shape has exactly one bounded tableau, whatever the bound. -/
theorem eq_of_skewCells_eq_empty (h : skewCells lam mu = ∅)
    (T T' : BoundedSkewSSYT lam mu n) : T = T' := by
  refine BoundedSkewSSYT.ext fun i j => ?_
  have hc : (i, j) ∉ skewCells lam mu := by rw [h]; exact Finset.notMem_empty _
  rw [T.zeros hc, T'.zeros hc]

end BoundedSkewSSYT

/-! ## The skew Schur polynomial -/

variable {R : Type*} [CommSemiring R]

/-- The skew Schur polynomial of shape `lam / mu` in the `n` variables
`x 0, …, x (n-1)`, the generating function of the semistandard tableaux of that
skew shape with entries `< n`:

`skewSchur lam mu n x = ∑_T ∏_{(i,j) ∈ lam/mu} x (T i j)`.

At `mu = ⊥` this is `Shields.schur`; see `skewSchur_bot`. -/
noncomputable def skewSchur (lam mu : YoungDiagram) (n : ℕ) (x : ℕ → R) : R :=
  ∑ T : BoundedSkewSSYT lam mu n, ∏ c ∈ skewCells lam mu, x (T c.1 c.2)

/-- A bounded tableau of skew shape `lam / ⊥` is a bounded tableau of straight
shape `lam`: the `∉ ⊥` clauses in the skew row and column conditions are
vacuous, and `skewCells lam ⊥ = lam.cells`.  Both directions keep the same
`entry` function, so the round trips are definitional. -/
def boundedSkewSSYTBotEquiv (lam : YoungDiagram) (n : ℕ) :
    BoundedSkewSSYT lam ⊥ n ≃ BoundedSSYT lam n where
  toFun T :=
    ⟨⟨T.1.entry,
        fun hj hcell => T.1.row_weak hj hcell (YoungDiagram.notMem_bot _),
        fun hi hcell => T.1.col_strict hi hcell (YoungDiagram.notMem_bot _),
        fun hc => T.1.zeros fun hx => hc (mem_skewCells.mp hx).1⟩,
      fun _ _ hcell => T.2 _ _ (mem_skewCells.mpr ⟨hcell, YoungDiagram.notMem_bot _⟩)⟩
  invFun T :=
    ⟨⟨T.1.entry,
        fun hj hcell _ => T.1.row_weak hj hcell,
        fun hi hcell _ => T.1.col_strict hi hcell,
        fun hc => T.1.zeros fun hx =>
          hc (mem_skewCells.mpr ⟨hx, YoungDiagram.notMem_bot _⟩)⟩,
      fun _ _ hcell => T.2 _ _ (mem_skewCells.mp hcell).1⟩
  left_inv _ := by apply BoundedSkewSSYT.ext; intro _ _; rfl
  right_inv _ := by apply BoundedSSYT.ext; intro _ _; rfl

/-- The straight shape is the skew shape over `⊥`, and the two generating
functions agree. -/
theorem skewSchur_bot (lam : YoungDiagram) (n : ℕ) (x : ℕ → R) :
    skewSchur lam ⊥ n x = schur lam n x := by
  refine Fintype.sum_equiv (boundedSkewSSYTBotEquiv lam n) _ _ fun T =>
    Finset.prod_congr (skewCells_bot lam) fun _ _ => rfl

theorem skewSchur_nonneg {lam mu : YoungDiagram} {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, i < n → 0 ≤ x i) : 0 ≤ skewSchur lam mu n x :=
  Finset.sum_nonneg fun T _ =>
    Finset.prod_nonneg fun _c hc => hx _ (T.lt_of_mem_cells hc)

/-- The vanishing half of the hook criterion at zero odd variables.  A column of
`lam / mu` taller than `n` cannot be filled by strictly increasing entries below
`n`, so the index set of the sum is empty. -/
theorem skewSchur_eq_zero_of_lt_skewColLen {lam mu : YoungDiagram} {n j : ℕ}
    (x : ℕ → R) (h : n < skewColLen lam mu j) : skewSchur lam mu n x = 0 := by
  have : IsEmpty (BoundedSkewSSYT lam mu n) :=
    ⟨fun T => absurd (T.skewColLen_le j) (by omega)⟩
  rw [skewSchur, Finset.univ_eq_empty, Finset.sum_empty]

/-- The positivity half of the hook criterion at zero odd variables. -/
theorem skewSchur_pos {lam mu : YoungDiagram} {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, i < n → 0 < x i) (h : ∀ j, skewColLen lam mu j ≤ n) :
    0 < skewSchur lam mu n x := by
  refine Finset.sum_pos (fun T _ => ?_)
    ⟨BoundedSkewSSYT.skewHighestWeight lam mu n h, mem_univ _⟩
  exact Finset.prod_pos fun c hc => hx _ (T.lt_of_mem_cells hc)

/-- **The hook criterion at zero odd variables.**  With positive variables,
`s_{lam/mu}(x_0, …, x_{n-1}) > 0` exactly when every column of `lam / mu` has
height at most `n`: a skew Schur function in `b` variables is nonzero exactly when
every column of its skew diagram has height at most `b`. -/
theorem skewSchur_pos_iff {lam mu : YoungDiagram} {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, i < n → 0 < x i) :
    0 < skewSchur lam mu n x ↔ ∀ j, skewColLen lam mu j ≤ n := by
  refine ⟨fun hpos j => ?_, skewSchur_pos hx⟩
  by_contra hj
  exact absurd (skewSchur_eq_zero_of_lt_skewColLen x (by omega : n < skewColLen lam mu j))
    (ne_of_gt hpos)

/-- The conjugate form: with positive variables, the skew Schur function of the
conjugate shape in `n` variables is positive exactly when every *row* of
`lam / mu` has length at most `n`. -/
theorem skewSchur_transpose_pos_iff {lam mu : YoungDiagram} {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, i < n → 0 < x i) :
    0 < skewSchur lam.transpose mu.transpose n x ↔ ∀ i, skewRowLen lam mu i ≤ n := by
  rw [skewSchur_pos_iff hx]
  exact ⟨fun h i => (skewColLen_transpose lam mu i) ▸ h i,
    fun h j => (skewColLen_transpose lam mu j) ▸ h j⟩

/-- An empty skew shape has a single, empty tableau, so its skew Schur function
is `1`. -/
theorem skewSchur_of_le {lam mu : YoungDiagram} (n : ℕ) (x : ℕ → R) (h : lam ≤ mu) :
    skewSchur lam mu n x = 1 := by
  have hc : skewCells lam mu = ∅ := skewCells_eq_empty_iff.mpr h
  have huniv : (Finset.univ : Finset (BoundedSkewSSYT lam mu n)) =
      {BoundedSkewSSYT.ofEmpty lam mu n hc} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨mem_univ _, fun T _ => BoundedSkewSSYT.eq_of_skewCells_eq_empty hc T _⟩
  rw [skewSchur, huniv, Finset.sum_singleton]
  refine Finset.prod_eq_one fun c hcc => ?_
  rw [hc] at hcc
  exact absurd hcc (Finset.notMem_empty c)

/-! ## The interval of Young diagrams between two shapes

The branching formula sums over `mu ⊆ nu ⊆ lam`.  Mathlib has no
`LocallyFiniteOrder` on `YoungDiagram`, so the index set is built by hand: the
`cells` map is injective and lands in `lam.cells.powerset`.
-/

theorem cells_injective : Function.Injective YoungDiagram.cells := by
  intro a b h
  obtain ⟨ca, pa⟩ := a
  obtain ⟨cb, pb⟩ := b
  simp only at h
  subst h
  rfl

theorem finite_between (mu lam : YoungDiagram) :
    {nu : YoungDiagram | mu ≤ nu ∧ nu ≤ lam}.Finite := by
  refine Set.Finite.of_finite_image ?_ cells_injective.injOn
  refine Set.Finite.subset (lam.cells.powerset : Finset (Finset (ℕ × ℕ))).finite_toSet ?_
  rintro s ⟨nu, ⟨-, hnu⟩, rfl⟩
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (YoungDiagram.cells_subset_iff.mpr hnu))

/-- The Young diagrams `nu` with `mu ⊆ nu ⊆ lam`, as a `Finset`. -/
noncomputable def youngIcc (mu lam : YoungDiagram) : Finset YoungDiagram :=
  (finite_between mu lam).toFinset

@[simp]
theorem mem_youngIcc {mu lam nu : YoungDiagram} :
    nu ∈ youngIcc mu lam ↔ mu ≤ nu ∧ nu ≤ lam := by
  simp [youngIcc]

end Shields
