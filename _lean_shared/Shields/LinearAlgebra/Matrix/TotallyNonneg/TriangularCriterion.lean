/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.DesnanotJacobi
import Shields.LinearAlgebra.Matrix.Determinant.SnocBorder
import Shields.Order.Monotone.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# The triangular criterion: initial-block minors decide all of them

For a lower-triangular matrix, positivity of every minor taken against an **initial** block of
columns forces positivity of every minor whose rows dominate its columns.  This is the triangular
criterion, and the file proves it together with the two determinant identities it runs on.

## Main results

* `Shields.det_submatrix_eq_zero_of_row_lt_col`: a minor of a lower-triangular matrix whose rows
  fail to dominate its columns at some position vanishes.
* `Shields.minor_three_term`: the three-term minor identity for a lower-triangular unit-diagonal
  matrix, at an arbitrary column family.  Deleting the interior row of a strictly monotone row
  family relates that minor to the two end deletions.
* `Shields.detT`, `Shields.det_detT`: the transposed embedding.  `Aᵗ` sits in the bottom-left
  block of a lower-triangular unit-diagonal matrix, so a minor there is a minor of `A` with its
  rows and columns exchanged.
* `Shields.minor_three_term_col`: the same identity with the **column** family deleted, for an
  arbitrary matrix, obtained from the previous two.
* `Shields.det_consecutive_pos`: a minor against a **consecutive** column block is positive as
  soon as every minor against an initial block is.
* `Shields.det_pos_of_no_gap`: the base case of the dispersion induction -- a column family with
  no gap is a consecutive block.
* `Shields.det_pos_of_initialPosOn`, `Shields.det_pos_of_initialPos`: the criterion itself, in a
  windowed and an unrestricted form.

## Implementation notes

The identity that the induction on the column set needs deletes a column, and Desnanot--Jacobi
deletes rows and columns at the border.  Rather than redo the border computation, `detT` transposes
by embedding: minors of the embedded matrix are minors of `A` with the two index families
exchanged, so the row deletion of `minor_three_term` becomes the column deletion of
`minor_three_term_col`.  The embedding is over an arbitrary commutative ring and the triangularity
hypotheses hold for it by construction, which is why `minor_three_term_col` needs none.

The induction is double: on the size of the index sets, and inside that on the **dispersion** of
the column set, via `Shields.exists_insert_of_gap`.  One of the four minors the identity produces
is only nonnegative -- it vanishes as soon as its rows stop dominating its columns -- and the
identity absorbs exactly that.

Indices are `ℕ`-valued families `Fin k → ℕ` on a matrix indexed by `ℕ`, rather than `Fin n`
selections, because the induction changes the ambient size.

Mathlib has no total-positivity criterion of any kind at the pinned revision, and no Neville
elimination or bidiagonal factorization; a totally-nonnegative class is in flight as
`feat(LinearAlgebra): totally nonnegative matrices` (#41813), with none of these results.

## References

* [A. Pinkus, *Totally Positive Matrices*][Pinkus2010], Thm. 2.8
* [S. M. Fallat and C. R. Johnson, *Totally Nonnegative Matrices*][Fallat2011], Lem. 3.3.4

## Tags

total positivity, totally nonnegative, minor, triangular matrix, Desnanot--Jacobi, dispersion
-/

namespace Shields

open Matrix

variable {R : Type*} [CommRing R]

/-! ### A minor that fails to dominate -/

/-- A minor of a lower-triangular matrix whose rows fail to dominate its columns
at some position vanishes: the rows at or before that position meet the columns
at or after it in a zero block too large for any permutation to avoid.

Not the same statement as `Shields.det_submatrix_eq_zero_of_lt`, which is its mirror
image -- upper triangular, a finite index type, and the column below the row.  The suffix
`_of_row_lt_col` says which side the hypothesis is on. -/
theorem det_submatrix_eq_zero_of_row_lt_col {k : ℕ} {T : Matrix ℕ ℕ R}
    (hT : ∀ i j, i < j → T i j = 0)
    {ρ σ : Fin k → ℕ} (hρ : StrictMono ρ) (hσ : Monotone σ)
    {a₀ : Fin k} (ha₀ : ρ a₀ < σ a₀) :
    (T.submatrix ρ σ).det = 0 := by
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun π _ => ?_
  obtain ⟨a, ha⟩ : ∃ a : Fin k, (T.submatrix ρ σ) (π a) a = 0 := by
    by_contra hc
    push Not at hc
    -- Every factor nonzero forces `σ a ≤ ρ (π a)` for all `a`.
    have hall : ∀ a : Fin k, σ a ≤ ρ (π a) := by
      intro a
      by_contra hlt
      push Not at hlt
      exact hc a (by simpa [Matrix.submatrix_apply] using hT _ _ hlt)
    -- Then `π` injects `Ici a₀` into `Ioi a₀`, which is one element smaller.
    have hmaps : ∀ a ∈ Finset.Ici a₀, π a ∈ Finset.Ioi a₀ := by
      intro a ha'
      have hale : a₀ ≤ a := Finset.mem_Ici.mp ha'
      have h3 : ρ a₀ < ρ (π a) := lt_of_lt_of_le ha₀ ((hσ hale).trans (hall a))
      exact Finset.mem_Ioi.mpr (hρ.lt_iff_lt.mp h3)
    have hcard := Finset.card_le_card_of_injOn π hmaps
      (fun a _ b _ hab => π.injective hab)
    rw [Fin.card_Ici, Fin.card_Ioi] at hcard
    have := a₀.isLt
    omega
  exact smul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ a) ha)

/-- `Fin.snoc` against a shifted index: dropping the FIRST entry of a snoc-tuple snocs the
shifted tuple.  Mathlib carries the `castSucc` companion as `Fin.snoc_comp_castSucc` and not
this one. -/
theorem snoc_comp_succ {α : Sort*} {n : ℕ} (f : Fin (n + 1) → α) (x : α) :
    (Fin.snoc f x : Fin (n + 2) → α) ∘ Fin.succ = Fin.snoc (f ∘ Fin.succ) x := by
  funext b
  induction b using Fin.lastCases with
  | last =>
      simp only [Function.comp_apply,
        show (Fin.last n).succ = Fin.last (n + 1) from rfl, Fin.snoc_last]
  | cast j =>
      simp only [Function.comp_apply,
        show (j.castSucc : Fin (n + 1)).succ = (j.succ : Fin (n + 1)).castSucc from
          (Fin.succ_castSucc j).symm, Fin.snoc_castSucc]

/-- `Fin.snoc` against the interior positions: `i ↦ i.castSucc.succ` never reaches the last
index, so a snoc-tuple read there is the shifted tuple. -/
theorem snoc_comp_castSucc_succ {α : Sort*} {n : ℕ} (f : Fin (n + 1) → α) (x : α) :
    (Fin.snoc f x : Fin (n + 2) → α) ∘ (fun i : Fin n => i.castSucc.succ) = f ∘ Fin.succ := by
  funext j
  simp only [Function.comp_apply,
    show (j.castSucc : Fin (n + 1)).succ = (j.succ : Fin (n + 1)).castSucc from
      (Fin.succ_castSucc j).symm, Fin.snoc_castSucc]

/-- `Fin.succAbove` at an interior position leaves the last index last. -/
theorem succAbove_succ_last {m : ℕ} (l : Fin m) :
    (l.castSucc.succ).succAbove (Fin.last m) = Fin.last (m + 1) := by
  rw [Fin.succAbove_succ_of_lt _ _ (Fin.castSucc_lt_last l)]
  rfl

/-- `Fin.snoc` of a family with one interior entry moved to the end, read from the second index
on: the same construction one size down, at the shifted family.  The `castSucc` and interior
companions are `Fin.snoc_comp_castSucc` and `Shields.snoc_comp_castSucc_succ`. -/
theorem snoc_succAbove_comp_succ {α : Type*} {m : ℕ} (r : Fin (m + 2) → α) (l : Fin m) :
    (Fin.snoc (r ∘ (l.castSucc.succ).succAbove) (r (l.castSucc.succ)) : Fin (m + 2) → α)
        ∘ Fin.succ
      = Fin.snoc ((r ∘ Fin.succ) ∘ (l.castSucc).succAbove) ((r ∘ Fin.succ) l.castSucc) := by
  rw [snoc_comp_succ]
  congr 1
  funext j
  simp only [Function.comp_apply, Fin.succ_succAbove_succ]

/-! ### The three-term identity at an arbitrary column family -/

/-- **The three-term identity, deleting a row.**  For a lower-triangular matrix with unit
diagonal, the minor on a strictly monotone row family `r` with the interior row `l + 1`
deleted, against an arbitrary column family `σ`, is expressed by the minors with the first
row deleted and with the last row deleted.  It is Desnanot--Jacobi on the square matrix whose
rows are `r` with the interior row moved to the end and whose columns are `σ` with `r (m+1)`
appended; triangularity and the unit diagonal are what evaluate that added column. -/
theorem minor_three_term {A : Matrix ℕ ℕ R}
    (hlow : ∀ i j : ℕ, i < j → A i j = 0) (hdiag : ∀ i : ℕ, A i i = 1)
    {m : ℕ} (r : Fin (m + 2) → ℕ) (hr : StrictMono r) (σ : Fin (m + 1) → ℕ)
    (l : Fin m) :
    (A.submatrix (r ∘ (l.castSucc.succ).succAbove) σ).det
        * (A.submatrix ((r ∘ Fin.succ) ∘ Fin.castSucc) (σ ∘ Fin.succ)).det
      = (A.submatrix (r ∘ Fin.succ) σ).det
          * (A.submatrix ((r ∘ (l.castSucc.succ).succAbove) ∘ Fin.castSucc) (σ ∘ Fin.succ)).det
        + (A.submatrix (r ∘ Fin.castSucc) σ).det
            * (A.submatrix ((r ∘ (l.castSucc.succ).succAbove) ∘ Fin.succ) (σ ∘ Fin.succ)).det := by
  have hsA_last := succAbove_succ_last l
  -- Desnanot--Jacobi on the matrix with rows `r` and columns `0, …, m, r (m+1)`
  have hDJ := desnanot_jacobi (A.submatrix
    (Fin.snoc (r ∘ (l.castSucc.succ).succAbove) (r (l.castSucc.succ)))
    (Fin.snoc σ (r (Fin.last (m + 1)))))
  simp only [Matrix.submatrix_submatrix] at hDJ
  -- the row and column maps of the four terms and the interior block
  rw [Fin.snoc_comp_castSucc, Fin.snoc_comp_castSucc, snoc_succAbove_comp_succ r l,
    snoc_comp_succ σ (r (Fin.last (m + 1))),
    snoc_comp_castSucc_succ (r ∘ (l.castSucc.succ).succAbove) (r (l.castSucc.succ)),
    snoc_comp_castSucc_succ σ (r (Fin.last (m + 1)))] at hDJ
  -- the two rows-out-of-order terms, and the three border collapses
  rw [det_submatrix_snoc_succAbove A r _ (l.castSucc.succ),
    det_submatrix_snoc_succAbove A (r ∘ Fin.succ) _ l.castSucc,
    det_submatrix_snoc_succAbove A (r ∘ Fin.succ) _ l.castSucc] at hDJ
  rw [det_submatrix_border hlow hdiag r rfl (fun j => hr (Fin.castSucc_lt_last j)),
    det_submatrix_border hlow hdiag (r ∘ Fin.succ)
      (show (r ∘ Fin.succ) (Fin.last m) = r (Fin.last (m + 1)) from rfl)
      (fun j => hr (by
        rw [Fin.lt_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
        exact Nat.succ_lt_succ j.isLt)),
    det_submatrix_border hlow hdiag (r ∘ (l.castSucc.succ).succAbove)
      (by rw [Function.comp_apply, hsA_last])
      (fun j => hr (by
        rw [← hsA_last]
        exact Fin.succAbove_lt_succAbove_iff.mpr (Fin.castSucc_lt_last j)))] at hDJ
  -- the signs on the two sides agree
  have hexp : ((l.castSucc.succ : Fin (m + 2)) : ℕ) + (m + 1)
      = ((l.castSucc : Fin (m + 1)) : ℕ) + m + 2 := by
    simp only [Fin.val_succ, Fin.val_castSucc]; omega
  rw [hexp, pow_add, show ((-1 : R)) ^ (2 : ℕ) = 1 from by norm_num, mul_one] at hDJ
  have hXX : ((-1 : R) ^ (((l.castSucc : Fin (m + 1)) : ℕ) + m))
      * ((-1 : R) ^ (((l.castSucc : Fin (m + 1)) : ℕ) + m)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have key := congrArg (fun z : R =>
    ((-1 : R) ^ (((l.castSucc : Fin (m + 1)) : ℕ) + m)) * z) hDJ
  simp only [mul_sub, ← mul_assoc, hXX, one_mul] at key
  linear_combination -key



/-! ### From row deletion to column deletion

`minor_three_term` deletes a **row**.  The induction on the column set needs the identity that
deletes a **column**, and the identity itself holds for an arbitrary matrix -- the triangularity
in `minor_three_term` only serves to make one column of the bordered matrix a basis vector.
Rather than redo the border, embed `Aᵗ` in the bottom-left block of a lower-triangular
unit-diagonal matrix: minors there are minors of `A` with rows and columns exchanged, so the row
deletion becomes a column deletion. -/

section Embed

/-- `Aᵗ` in the bottom-left block of a lower-triangular unit-diagonal matrix: row `n + c` against
column `r` carries `A r c`. -/
def detT (A : Matrix ℕ ℕ R) (n : ℕ) : Matrix ℕ ℕ R :=
  Matrix.of fun i j => if i = j then 1 else if n ≤ i ∧ j < n then A j (i - n) else 0

theorem detT_low (A : Matrix ℕ ℕ R) (n : ℕ) : ∀ i j : ℕ, i < j → detT A n i j = 0 := by
  intro i j hij
  have h1 : ¬ (i = j) := by omega
  have h2 : ¬ (n ≤ i ∧ j < n) := by omega
  simp [detT, h1, h2]

theorem detT_diag (A : Matrix ℕ ℕ R) (n : ℕ) : ∀ i : ℕ, detT A n i i = 1 := by
  intro i; simp [detT]

/-- The transfer: a minor of the embedding is the minor of `A` with rows and columns exchanged. -/
theorem det_detT (A : Matrix ℕ ℕ R) {n k : ℕ} (C : Fin k → ℕ) (Rw : Fin k → ℕ)
    (hRw : ∀ b, Rw b < n) :
    ((detT A n).submatrix (fun a => n + C a) Rw).det = (A.submatrix Rw C).det := by
  have hEq : (detT A n).submatrix (fun a => n + C a) Rw = (A.submatrix Rw C).transpose := by
    ext a b
    have h1 : ¬ (n + C a = Rw b) := by have := hRw b; omega
    have h2 : n ≤ n + C a ∧ Rw b < n := ⟨Nat.le_add_right _ _, hRw b⟩
    simp only [Matrix.submatrix_apply, detT, Matrix.of_apply, if_neg h1, if_pos h2,
      Matrix.transpose_apply, Nat.add_sub_cancel_left]
  rw [hEq, Matrix.det_transpose]

/-- **The three-term identity, deleting a column.**  For an arbitrary matrix, a strictly monotone
column family `γ` of length `m+2` and any row family `ρ` of length `m+1`: the minor that deletes an
interior column is determined by those that delete the first and the last, against the minors one
size down that drop the first row. -/
theorem minor_three_term_col (A : Matrix ℕ ℕ R) {m : ℕ} (γ : Fin (m + 2) → ℕ)
    (hγ : StrictMono γ) (ρ : Fin (m + 1) → ℕ) (l : Fin m) :
    (A.submatrix ρ (γ ∘ (l.castSucc.succ).succAbove)).det
        * (A.submatrix (ρ ∘ Fin.succ) ((γ ∘ Fin.succ) ∘ Fin.castSucc)).det
      = (A.submatrix ρ (γ ∘ Fin.succ)).det
          * (A.submatrix (ρ ∘ Fin.succ) ((γ ∘ (l.castSucc.succ).succAbove) ∘ Fin.castSucc)).det
        + (A.submatrix ρ (γ ∘ Fin.castSucc)).det
            * (A.submatrix (ρ ∘ Fin.succ) ((γ ∘ (l.castSucc.succ).succAbove) ∘ Fin.succ)).det := by
  set n : ℕ := (Finset.univ.sup ρ) + 1 with hn
  have hRw : ∀ b, ρ b < n := fun b =>
    hn ▸ Nat.lt_succ_of_le (Finset.le_sup (f := ρ) (Finset.mem_univ b))
  have hRw' : ∀ b : Fin m, (ρ ∘ Fin.succ) b < n := fun b => hRw _
  have hmono : StrictMono (fun a => n + γ a) := fun _ _ hab => Nat.add_lt_add_left (hγ hab) n
  have key := minor_three_term (A := detT A n) (detT_low A n) (detT_diag A n)
    (fun a => n + γ a) hmono ρ l
  -- the six minors of the embedding, each a minor of `A` with its index families exchanged
  rw [← det_detT A _ ρ hRw, ← det_detT A _ (ρ ∘ Fin.succ) hRw', ← det_detT A _ ρ hRw,
    ← det_detT A _ (ρ ∘ Fin.succ) hRw', ← det_detT A _ ρ hRw,
    ← det_detT A _ (ρ ∘ Fin.succ) hRw']
  exact key

end Embed

/-! ### From an initial column block to a consecutive one

The step is a block-triangular split.  Bordering the row set with `0, …, i-1` and the column set
with the same indices makes the top-right block vanish -- a lower-triangular matrix has zeros
above the diagonal, and those rows sit above those columns -- so the bordered minor, which is a
minor against an *initial* block, factors as the leading principal minor times the one wanted. -/

section Consecutive

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Every minor against an initial column block is positive. -/
def InitialPos (A : Matrix ℕ ℕ R) : Prop :=
  ∀ (k : ℕ) (S : Fin k → ℕ), StrictMono S → 0 < (A.submatrix S (fun b : Fin k => (b : ℕ))).det

/-- The same, but only for row sets inside the window `{0, …, N-1}`.  The criterion needs no
more: every minor the induction visits has its rows inside the original row set together with an
initial block. -/
def InitialPosOn (A : Matrix ℕ ℕ R) (N : ℕ) : Prop :=
  ∀ (k : ℕ) (S : Fin k → ℕ), StrictMono S → (∀ b, S b < N) →
    0 < (A.submatrix S (fun b : Fin k => (b : ℕ))).det

/-- The bordered row family: `0, …, i-1` followed by `S`. -/
private def borderRows {k : ℕ} (i : ℕ) (S : Fin k → ℕ) (a : Fin (i + k)) : ℕ :=
  if h : (a : ℕ) < i then (a : ℕ) else S ⟨(a : ℕ) - i, by have := a.isLt; omega⟩

private theorem borderRows_left {k : ℕ} (i : ℕ) (S : Fin k → ℕ) {a : Fin (i + k)}
    (h : (a : ℕ) < i) : borderRows i S a = (a : ℕ) := by
  simp [borderRows, h]

private theorem borderRows_right {k : ℕ} (i : ℕ) (S : Fin k → ℕ) {a : Fin (i + k)}
    (h : ¬ (a : ℕ) < i) : borderRows i S a = S ⟨(a : ℕ) - i, by have := a.isLt; omega⟩ := by
  simp [borderRows, h]

private theorem borderRows_castAdd {k : ℕ} (i : ℕ) (S : Fin k → ℕ) (c : Fin i) :
    borderRows i S (Fin.castAdd k c) = (c : ℕ) := by
  rw [borderRows_left i S (by simp)]
  simp

private theorem borderRows_natAdd {k : ℕ} (i : ℕ) (S : Fin k → ℕ) (c : Fin k) :
    borderRows i S (Fin.natAdd i c) = S c := by
  rw [borderRows_right i S (by simp)]
  congr 1
  exact Fin.ext (by simp)

private theorem strictMono_borderRows {k : ℕ} (i : ℕ) {S : Fin k → ℕ} (hS : StrictMono S)
    (hdom : ∀ b : Fin k, i + (b : ℕ) ≤ S b) : StrictMono (borderRows i S) := by
  intro a b hab
  rw [Fin.lt_def] at hab
  by_cases ha : (a : ℕ) < i
  · rw [borderRows_left i S ha]
    by_cases hb : (b : ℕ) < i
    · rw [borderRows_left i S hb]; exact hab
    · rw [borderRows_right i S hb]
      have h1 := hdom ⟨(b : ℕ) - i, by have := b.isLt; omega⟩
      omega
  · rw [borderRows_right i S ha]
    have hb : ¬ (b : ℕ) < i := by omega
    rw [borderRows_right i S hb]
    exact hS (by rw [Fin.lt_def]; simp only; omega)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **The block-triangular split.**  Bordering both index families with `0, …, i-1` makes the
top-right block vanish -- a lower-triangular matrix has zeros above the diagonal, and those rows
sit above those columns -- so the bordered minor factors as the leading principal minor times the
minor against the consecutive block. -/
private theorem det_borderRows {A : Matrix ℕ ℕ R} (hlow : ∀ i j : ℕ, i < j → A i j = 0)
    {k : ℕ} (i : ℕ) (S : Fin k → ℕ) :
    (A.submatrix (borderRows i S) (fun b : Fin (i + k) => (b : ℕ))).det
      = (A.submatrix (fun c : Fin i => (c : ℕ)) (fun c : Fin i => (c : ℕ))).det
        * (A.submatrix S (fun b : Fin k => i + (b : ℕ))).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  have hblocks : (A.submatrix (borderRows i S) (fun b : Fin (i + k) => (b : ℕ))).submatrix
        finSumFinEquiv finSumFinEquiv
      = Matrix.fromBlocks
          (A.submatrix (fun c : Fin i => (c : ℕ)) (fun c : Fin i => (c : ℕ))) 0
          (A.submatrix S (fun c : Fin i => (c : ℕ)))
          (A.submatrix S (fun b : Fin k => i + (b : ℕ))) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, borderRows_castAdd, borderRows_natAdd, Matrix.zero_apply,
        Fin.val_natAdd, Fin.val_castAdd]
    exact hlow _ _ (by have := a.isLt; omega)
  rw [hblocks, Matrix.det_fromBlocks_zero₁₂]

/-- **The consecutive-column step.**  With every initial-block minor positive, every minor against
a consecutive column block `i, …, i+k-1` is positive, provided the rows dominate. -/
theorem det_consecutive_pos {A : Matrix ℕ ℕ R} (hlow : ∀ i j : ℕ, i < j → A i j = 0)
    {N : ℕ} (hInit : InitialPosOn A N) {k : ℕ} (i : ℕ) (S : Fin k → ℕ) (hS : StrictMono S)
    (hdom : ∀ b : Fin k, i + (b : ℕ) ≤ S b) (hSN : ∀ b, S b < N) (hiN : i ≤ N) :
    0 < (A.submatrix S (fun b : Fin k => i + (b : ℕ))).det := by
  have hbN : ∀ b : Fin (i + k), borderRows i S b < N := by
    intro b
    by_cases hb : (b : ℕ) < i
    · rw [borderRows_left i S hb]
      omega
    · rw [borderRows_right i S hb]
      exact hSN _
  have hborder : 0 < (A.submatrix (borderRows i S) (fun b : Fin (i + k) => (b : ℕ))).det :=
    hInit _ _ (strictMono_borderRows i hS hdom) hbN
  have hlead : 0 < (A.submatrix (fun c : Fin i => (c : ℕ)) (fun c : Fin i => (c : ℕ))).det :=
    hInit _ _ (fun a b hab => by simpa using hab) (fun c => by have := c.isLt; omega)
  rw [det_borderRows hlow i S] at hborder
  nlinarith [hborder, hlead]

/-- **The dispersion base case.**  A strictly monotone column family with no gap is a
consecutive block starting at `C 0`, which is what `det_consecutive_pos` asks for. -/
theorem det_pos_of_no_gap {A : Matrix ℕ ℕ R} (hlow : ∀ i j : ℕ, i < j → A i j = 0)
    {N : ℕ} (hInit : InitialPosOn A N) {m : ℕ} (S C : Fin (m + 1) → ℕ)
    (hS : StrictMono S) (hC : StrictMono C) (hdom : ∀ b, C b ≤ S b) (hSN : ∀ b, S b < N)
    (hgap : ∀ j : Fin m, C j.succ ≤ C j.castSucc + 1) :
    0 < (A.submatrix S C).det := by
  have hC0 : ∀ b : Fin (m + 1), C b = C 0 + (b : ℕ) := by
    have hcons := eq_consecutive_of_no_gap C hC fun j => by have := hgap j; omega
    intro b
    have h : C b = (b : ℕ) + C 0 := congrFun hcons b
    omega
  have heq : (fun b : Fin (m + 1) => C 0 + (b : ℕ)) = C := funext fun b => (hC0 b).symm
  rw [← heq]
  refine det_consecutive_pos hlow hInit (C 0) S hS (fun b => by rw [← hC0 b]; exact hdom b) hSN ?_
  have h0 := hdom 0
  have h1 := hSN 0
  omega

end Consecutive

/-! ### The criterion

Pinkus, Thm. 2.8: for a lower-triangular matrix, positivity of every minor
against an initial column block forces positivity of every minor whose rows dominate its columns.
The induction is on the size and on the **dispersion** of the column set: a column set with a gap
is one longer with an interior entry deleted (`exists_insert_of_gap`), the three-term
identity relates that deletion to the deletions of the two ends, and both of those have smaller
dispersion.  One of the four minors on the right is only nonnegative -- it vanishes when its rows
stop dominating its columns -- which is exactly what the identity can absorb. -/

section Criterion

variable [LinearOrder R] [IsStrictOrderedRing R]

private theorem val_le_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (i : ℕ) ≤ (p.succAbove i : ℕ) := by
  rcases lt_or_ge i.castSucc p with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
    omega

/-- The inserted family of `Shields.exists_insert_of_gap` is dominated wherever `C` is: it takes
at position `b.castSucc` a value `C` takes no earlier than `b`. -/
private theorem insert_dom {m : ℕ} {C S : Fin (m + 1) → ℕ} {j : Fin m} {γ : Fin (m + 2) → ℕ}
    (hγ : StrictMono γ) (hγC : γ ∘ (j.castSucc.succ).succAbove = C) (hdom : ∀ b, C b ≤ S b)
    (b : Fin (m + 1)) : γ b.castSucc ≤ S b := by
  have hval : γ ((j.castSucc.succ).succAbove b) = C b := congrFun hγC b
  have hle : γ b.castSucc ≤ γ ((j.castSucc.succ).succAbove b) :=
    hγ.monotone (by rw [Fin.le_def, Fin.val_castSucc]; exact val_le_succAbove _ b)
  have := hdom b
  omega

/-- Dropping either end of the inserted family shortens its span.  The insertion agrees with `C`
at both ends, and each of the two deletions gives one of them up. -/
private theorem insert_dispersion_lt {m : ℕ} {C : Fin (m + 1) → ℕ} {j : Fin m}
    {γ : Fin (m + 2) → ℕ} (hγ : StrictMono γ) (hγC : γ ∘ (j.castSucc.succ).succAbove = C) :
    (γ ∘ Fin.castSucc) (Fin.last m) - (γ ∘ Fin.castSucc) 0 < C (Fin.last m) - C 0
      ∧ (γ ∘ Fin.succ) (Fin.last m) - (γ ∘ Fin.succ) 0 < C (Fin.last m) - C 0 := by
  have hsAlast := succAbove_succ_last j
  have hγ0 : γ 0 = C 0 := by rw [← hγC]; simp
  have hγlast : γ (Fin.last (m + 1)) = C (Fin.last m) := by rw [← hγC]; simp [hsAlast]
  have hcl : γ (Fin.castSucc (Fin.last m)) < C (Fin.last m) := by
    rw [← hγlast]
    exact hγ (by rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last, Fin.val_last]; omega)
  have hs0 : C 0 < γ (Fin.succ 0) := by
    rw [← hγ0]; exact hγ (by rw [Fin.lt_def, Fin.val_succ]; simp)
  have hm1 : C 0 ≤ γ (Fin.castSucc (Fin.last m)) := by
    rw [← hγ0]; exact hγ.monotone (Fin.zero_le _)
  have hm2 : γ (Fin.succ 0) ≤ C (Fin.last m) := by
    rw [← hγlast]; exact hγ.monotone (Fin.le_last _)
  simp only [Function.comp_apply,
    show (Fin.castSucc (0 : Fin (m + 1)) : Fin (m + 2)) = 0 from rfl,
    show (Fin.succ (Fin.last m) : Fin (m + 2)) = Fin.last (m + 1) from rfl, hγ0, hγlast]
  omega

/-- **The dispersion step.**  With the criterion known one size down, and known at this size for
column families of strictly smaller dispersion, a family carrying a gap is positive.  Insert the
missing column: the three-term identity writes the minor at the deleted column against the
minors at the two ends, both of smaller dispersion.  One of the four minors it produces is only
nonnegative -- it vanishes as soon as its rows stop dominating its columns -- and that is
exactly what the identity absorbs. -/
private theorem det_pos_of_gap {A : Matrix ℕ ℕ R} (hlow : ∀ i j : ℕ, i < j → A i j = 0)
    {N m sp : ℕ}
    (ih : ∀ S C : Fin m → ℕ, StrictMono S → StrictMono C → (∀ b, C b ≤ S b) →
      (∀ b, S b < N) → 0 < (A.submatrix S C).det)
    (ihsp : ∀ S C : Fin (m + 1) → ℕ, StrictMono S → StrictMono C → (∀ b, C b ≤ S b) →
      (∀ b, S b < N) → C (Fin.last m) - C 0 < sp → 0 < (A.submatrix S C).det)
    (S C : Fin (m + 1) → ℕ) (hS : StrictMono S) (hC : StrictMono C) (hdom : ∀ b, C b ≤ S b)
    (hSN : ∀ b, S b < N) (hsp : C (Fin.last m) - C 0 ≤ sp)
    (j : Fin m) (hj : C j.castSucc + 1 < C j.succ) :
    0 < (A.submatrix S C).det := by
  obtain ⟨γ, hγ, hγC⟩ := exists_insert_of_gap C hC j hj
  obtain ⟨hd1, hd2⟩ := insert_dispersion_lt hγ hγC
  have hSs : StrictMono (S ∘ Fin.succ) := hS.comp Fin.strictMono_succ
  have hγs : StrictMono (γ ∘ Fin.succ) := hγ.comp Fin.strictMono_succ
  have hSN' : ∀ b : Fin m, (S ∘ Fin.succ) b < N := fun b => hSN _
  have hdomγ : ∀ b : Fin m, γ (Fin.succ (Fin.castSucc b)) ≤ S (Fin.succ b) :=
    fun b => Fin.succ_castSucc b ▸ insert_dom hγ hγC hdom b.succ
  have hL2 : 0 < (A.submatrix (S ∘ Fin.succ) ((γ ∘ Fin.succ) ∘ Fin.castSucc)).det :=
    ih _ _ hSs (hγs.comp Fin.strictMono_castSucc) hdomγ hSN'
  have hR1b : 0 < (A.submatrix (S ∘ Fin.succ) (C ∘ Fin.castSucc)).det := by
    refine ih _ _ hSs (hC.comp Fin.strictMono_castSucc) (fun b => ?_) hSN'
    refine le_trans (hdom b.castSucc) (hS.monotone ?_)
    rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
    omega
  have hR2b : 0 < (A.submatrix (S ∘ Fin.succ) (C ∘ Fin.succ)).det :=
    ih _ _ hSs (hC.comp Fin.strictMono_succ) (fun b => hdom _) hSN'
  have hR2a : 0 < (A.submatrix S (γ ∘ Fin.castSucc)).det :=
    ihsp S _ hS (hγ.comp Fin.strictMono_castSucc) (insert_dom hγ hγC hdom) hSN (by omega)
  have hR1a : 0 ≤ (A.submatrix S (γ ∘ Fin.succ)).det := by
    by_cases hd : ∀ b, (γ ∘ Fin.succ) b ≤ S b
    · exact (ihsp S _ hS hγs hd hSN (by omega)).le
    · push Not at hd
      obtain ⟨b, hb⟩ := hd
      exact le_of_eq (det_submatrix_eq_zero_of_row_lt_col hlow hS hγs.monotone hb).symm
  have hid := minor_three_term_col A γ hγ S j
  rw [hγC] at hid
  nlinarith [hid, hL2, hR1a, hR1b, hR2a, hR2b]

/-- **The criterion at one size, by induction on the dispersion of the column family.**  A
family with no gap is a consecutive block; one with a gap reduces to strictly smaller
dispersion. -/
private theorem det_pos_of_dispersion_le {A : Matrix ℕ ℕ R}
    (hlow : ∀ i j : ℕ, i < j → A i j = 0) {N : ℕ} (hInit : InitialPosOn A N) {m : ℕ}
    (ih : ∀ S C : Fin m → ℕ, StrictMono S → StrictMono C → (∀ b, C b ≤ S b) →
      (∀ b, S b < N) → 0 < (A.submatrix S C).det) :
    ∀ (sp : ℕ) (S C : Fin (m + 1) → ℕ), StrictMono S → StrictMono C → (∀ b, C b ≤ S b) →
      (∀ b, S b < N) → C (Fin.last m) - C 0 ≤ sp → 0 < (A.submatrix S C).det := by
  intro sp
  induction sp using Nat.strong_induction_on with
  | _ sp ihsp =>
    intro S C hS hC hdom hSN hsp
    by_cases hgap : ∃ j : Fin m, C j.castSucc + 1 < C j.succ
    · obtain ⟨j, hj⟩ := hgap
      exact det_pos_of_gap hlow ih
        (fun S' C' h1 h2 h3 h4 h5 => ihsp _ h5 S' C' h1 h2 h3 h4 le_rfl)
        S C hS hC hdom hSN hsp j hj
    · push Not at hgap
      exact det_pos_of_no_gap hlow hInit S C hS hC hdom hSN hgap

/-- **The triangular criterion at an arbitrary column set.**  Every minor against an initial
column block positive forces every dominating minor positive. -/
theorem det_pos_of_initialPosOn {A : Matrix ℕ ℕ R} (hlow : ∀ i j : ℕ, i < j → A i j = 0)
    {N : ℕ} (hInit : InitialPosOn A N) :
    ∀ (k : ℕ) (S C : Fin k → ℕ), StrictMono S → StrictMono C → (∀ b, C b ≤ S b) →
      (∀ b, S b < N) → 0 < (A.submatrix S C).det := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    match k with
    | 0 =>
        intro S C _ _ _ _
        rw [Matrix.det_isEmpty]
        exact zero_lt_one
    | (m + 1) =>
        intro S C hS hC hdom hSN
        exact det_pos_of_dispersion_le hlow hInit (ihk m (by omega)) _ S C hS hC hdom hSN le_rfl

/-- **The unwindowed criterion.**  Taking the window past every index used. -/
theorem det_pos_of_initialPos {A : Matrix ℕ ℕ R} (hlow : ∀ i j : ℕ, i < j → A i j = 0)
    (hInit : InitialPos A) :
    ∀ (k : ℕ) (S C : Fin k → ℕ), StrictMono S → StrictMono C → (∀ b, C b ≤ S b) →
      0 < (A.submatrix S C).det := by
  intro k S C hS hC hdom
  exact det_pos_of_initialPosOn hlow (N := (Finset.univ.sup S) + 1)
    (fun k' S' h' _ => hInit k' S' h') k S C hS hC hdom fun b =>
      Nat.lt_succ_of_le (Finset.le_sup (f := S) (Finset.mem_univ b))

end Criterion


/-! ### Axiom footprint -/

/-- info: 'Shields.det_submatrix_eq_zero_of_row_lt_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_submatrix_eq_zero_of_row_lt_col

/-- info: 'Shields.minor_three_term_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minor_three_term_col

/-- info: 'Shields.det_pos_of_no_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_pos_of_no_gap

/-- info: 'Shields.det_pos_of_initialPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_pos_of_initialPos

end Shields
