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

/-! ### The three-term identity at an arbitrary column family -/

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
  have hcl : ∀ {k : ℕ} (j : Fin k), j.castSucc < Fin.last k := by
    intro k j
    rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last]; exact j.isLt
  have hlt : l.castSucc < Fin.last m := hcl l
  have hsA_last : (l.castSucc.succ).succAbove (Fin.last m) = Fin.last (m + 1) := by
    rw [Fin.succAbove_succ_of_lt _ _ hlt]; rfl
  -- Desnanot--Jacobi on the matrix with rows `r` and columns `0, …, m, r (m+1)`
  have hDJ := desnanot_jacobi (A.submatrix
    (Fin.snoc (r ∘ (l.castSucc.succ).succAbove) (r (l.castSucc.succ)))
    (Fin.snoc σ (r (Fin.last (m + 1)))))
  simp only [Matrix.submatrix_submatrix] at hDJ
  -- the row and column maps of the four terms and the interior block
  have hσc : (Fin.snoc σ (r (Fin.last (m + 1)))
      : Fin (m + 2) → ℕ) ∘ Fin.castSucc = σ := by
    funext b; simp only [Function.comp_apply, Fin.snoc_castSucc]
  have hσs : (Fin.snoc σ (r (Fin.last (m + 1)))
      : Fin (m + 2) → ℕ) ∘ Fin.succ
      = Fin.snoc (σ ∘ Fin.succ) (r (Fin.last (m + 1))) := by
    funext b
    induction b using Fin.lastCases with
    | last =>
        have h1 : (Fin.last m).succ = Fin.last (m + 1) := rfl
        simp only [Function.comp_apply, h1, Fin.snoc_last]
    | cast j =>
        have h1 : (j.castSucc : Fin (m + 1)).succ = (j.succ : Fin (m + 1)).castSucc :=
          (Fin.succ_castSucc j).symm
        simp only [Function.comp_apply, h1, Fin.snoc_castSucc]
  have hσi : (Fin.snoc σ (r (Fin.last (m + 1)))
      : Fin (m + 2) → ℕ) ∘ (fun i : Fin m => i.castSucc.succ)
      = σ ∘ Fin.succ := by
    funext j
    have h1 : (j.castSucc : Fin (m + 1)).succ = (j.succ : Fin (m + 1)).castSucc :=
      (Fin.succ_castSucc j).symm
    simp only [Function.comp_apply, h1, Fin.snoc_castSucc]
  have hρc : (Fin.snoc (r ∘ (l.castSucc.succ).succAbove) (r (l.castSucc.succ))
      : Fin (m + 2) → ℕ) ∘ Fin.castSucc = r ∘ (l.castSucc.succ).succAbove := by
    funext b; simp only [Function.comp_apply, Fin.snoc_castSucc]
  have hρs : (Fin.snoc (r ∘ (l.castSucc.succ).succAbove) (r (l.castSucc.succ))
      : Fin (m + 2) → ℕ) ∘ Fin.succ
      = Fin.snoc ((r ∘ Fin.succ) ∘ (l.castSucc).succAbove) ((r ∘ Fin.succ) l.castSucc) := by
    funext b
    induction b using Fin.lastCases with
    | last =>
        have h1 : (Fin.last m).succ = Fin.last (m + 1) := rfl
        simp only [Function.comp_apply, h1, Fin.snoc_last]
    | cast j =>
        have h1 : (j.castSucc : Fin (m + 1)).succ = (j.succ : Fin (m + 1)).castSucc :=
          (Fin.succ_castSucc j).symm
        simp only [Function.comp_apply, h1, Fin.snoc_castSucc, Fin.succ_succAbove_succ]
  have hρi : (Fin.snoc (r ∘ (l.castSucc.succ).succAbove) (r (l.castSucc.succ))
      : Fin (m + 2) → ℕ) ∘ (fun i : Fin m => i.castSucc.succ)
      = (r ∘ (l.castSucc.succ).succAbove) ∘ Fin.succ := by
    funext j
    have h1 : (j.castSucc : Fin (m + 1)).succ = (j.succ : Fin (m + 1)).castSucc :=
      (Fin.succ_castSucc j).symm
    simp only [Function.comp_apply, h1, Fin.snoc_castSucc]
  rw [hρc, hσc, hρs, hσs, hρi, hσi] at hDJ
  -- the two rows-out-of-order terms, and the three border collapses
  rw [det_submatrix_snoc_succAbove A r _ (l.castSucc.succ),
    det_submatrix_snoc_succAbove A (r ∘ Fin.succ) _ l.castSucc,
    det_submatrix_snoc_succAbove A (r ∘ Fin.succ) _ l.castSucc] at hDJ
  rw [det_submatrix_border hlow hdiag r rfl (fun j => hr (hcl j)),
    det_submatrix_border hlow hdiag (r ∘ Fin.succ)
      (show (r ∘ Fin.succ) (Fin.last m) = r (Fin.last (m + 1)) from rfl)
      (fun j => hr (by
        rw [Fin.lt_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
        exact Nat.succ_lt_succ j.isLt)),
    det_submatrix_border hlow hdiag (r ∘ (l.castSucc.succ).succAbove)
      (by rw [Function.comp_apply, hsA_last])
      (fun j => hr (by
        rw [← hsA_last]
        exact Fin.succAbove_lt_succAbove_iff.mpr (hcl j)))] at hDJ
  -- the signs on the two sides agree
  have hexp : ((l.castSucc.succ : Fin (m + 2)) : ℕ) + (m + 1)
      = ((l.castSucc : Fin (m + 1)) : ℕ) + m + 2 := by
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  rw [hexp, pow_add] at hDJ
  have hsq : ((-1 : R)) ^ (2 : ℕ) = 1 := by norm_num
  rw [hsq, mul_one] at hDJ
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
  have hRw : ∀ b, ρ b < n := by
    intro b
    have h := Finset.le_sup (f := ρ) (Finset.mem_univ b)
    rw [hn]
    omega
  have hRw' : ∀ b : Fin m, (ρ ∘ Fin.succ) b < n := fun b => hRw _
  have hmono : StrictMono (fun a => n + γ a) := fun _ _ hab => Nat.add_lt_add_left (hγ hab) n
  have key := minor_three_term (A := detT A n) (detT_low A n) (detT_diag A n)
    (fun a => n + γ a) hmono ρ l
  have e1 : ((detT A n).submatrix ((fun a => n + γ a) ∘ (l.castSucc.succ).succAbove) ρ).det
      = (A.submatrix ρ (γ ∘ (l.castSucc.succ).succAbove)).det :=
    det_detT A (γ ∘ (l.castSucc.succ).succAbove) ρ hRw
  have e2 : ((detT A n).submatrix (((fun a => n + γ a) ∘ Fin.succ) ∘ Fin.castSucc)
        (ρ ∘ Fin.succ)).det
      = (A.submatrix (ρ ∘ Fin.succ) ((γ ∘ Fin.succ) ∘ Fin.castSucc)).det :=
    det_detT A ((γ ∘ Fin.succ) ∘ Fin.castSucc) (ρ ∘ Fin.succ) hRw'
  have e3 : ((detT A n).submatrix ((fun a => n + γ a) ∘ Fin.succ) ρ).det
      = (A.submatrix ρ (γ ∘ Fin.succ)).det :=
    det_detT A (γ ∘ Fin.succ) ρ hRw
  have e4 : ((detT A n).submatrix
        (((fun a => n + γ a) ∘ (l.castSucc.succ).succAbove) ∘ Fin.castSucc) (ρ ∘ Fin.succ)).det
      = (A.submatrix (ρ ∘ Fin.succ) ((γ ∘ (l.castSucc.succ).succAbove) ∘ Fin.castSucc)).det :=
    det_detT A ((γ ∘ (l.castSucc.succ).succAbove) ∘ Fin.castSucc) (ρ ∘ Fin.succ) hRw'
  have e5 : ((detT A n).submatrix ((fun a => n + γ a) ∘ Fin.castSucc) ρ).det
      = (A.submatrix ρ (γ ∘ Fin.castSucc)).det :=
    det_detT A (γ ∘ Fin.castSucc) ρ hRw
  have e6 : ((detT A n).submatrix
        (((fun a => n + γ a) ∘ (l.castSucc.succ).succAbove) ∘ Fin.succ) (ρ ∘ Fin.succ)).det
      = (A.submatrix (ρ ∘ Fin.succ) ((γ ∘ (l.castSucc.succ).succAbove) ∘ Fin.succ)).det :=
    det_detT A ((γ ∘ (l.castSucc.succ).succAbove) ∘ Fin.succ) (ρ ∘ Fin.succ) hRw'
  rw [e1, e2, e3, e4, e5, e6] at key
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
      dsimp only at h1
      omega
  · rw [borderRows_right i S ha]
    have hb : ¬ (b : ℕ) < i := by omega
    rw [borderRows_right i S hb]
    exact hS (by rw [Fin.lt_def]; simp only; omega)

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
  have hsplit : (A.submatrix (borderRows i S) (fun b : Fin (i + k) => (b : ℕ))).det
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
      rcases a with a | a <;> rcases b with b | b
      · rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
          Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_left,
          borderRows_castAdd]
        simp
      · rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
          finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, borderRows_castAdd,
          Matrix.zero_apply]
        refine hlow _ _ ?_
        have := a.isLt
        simp only [Fin.val_natAdd]
        omega
      · rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
          Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
          borderRows_natAdd]
        simp
      · rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
          Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_right,
          borderRows_natAdd]
        simp
    rw [hblocks, Matrix.det_fromBlocks_zero₁₂]
  have hlead : 0 < (A.submatrix (fun c : Fin i => (c : ℕ)) (fun c : Fin i => (c : ℕ))).det :=
    hInit _ _ (fun a b hab => by simpa using hab) (fun c => by have := c.isLt; omega)
  rw [hsplit] at hborder
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [hborder, hlead]

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
      have inner : ∀ sp : ℕ, ∀ S C : Fin (m + 1) → ℕ, StrictMono S → StrictMono C →
          (∀ b, C b ≤ S b) → (∀ b, S b < N) → C (Fin.last m) - C 0 ≤ sp →
          0 < (A.submatrix S C).det := by
        intro sp
        induction sp using Nat.strong_induction_on with
        | _ sp ihsp =>
          intro S C hS hC hdom hSN hsp
          by_cases hgap : ∃ j : Fin m, C j.castSucc + 1 < C j.succ
          · obtain ⟨j, hj⟩ := hgap
            obtain ⟨γ, hγ, hγC⟩ := exists_insert_of_gap C hC j hj
            -- where the inserted family's two ends sit
            have hsA0 : (j.castSucc.succ).succAbove 0 = 0 := by
              rw [Fin.succAbove_of_castSucc_lt]
              · rfl
              · rw [Fin.lt_def, Fin.val_succ]; simp
            have hsAlast : (j.castSucc.succ).succAbove (Fin.last m) = Fin.last (m + 1) := by
              rw [Fin.succAbove_succ_of_lt]
              · rfl
              · rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last]; exact j.isLt
            have hγ0 : γ 0 = C 0 := by rw [← hγC]; simp [hsA0]
            have hγlast : γ (Fin.last (m + 1)) = C (Fin.last m) := by
              rw [← hγC]; simp [hsAlast]
            -- the inserted family is dominated where it has to be
            have hγval : ∀ b : Fin (m + 1), γ ((j.castSucc.succ).succAbove b) = C b := by
              intro b
              rw [← hγC]
              rfl
            have hdomγ : ∀ b : Fin (m + 1), γ b.castSucc ≤ S b := by
              intro b
              have hle : γ b.castSucc ≤ γ ((j.castSucc.succ).succAbove b) :=
                hγ.monotone (by rw [Fin.le_def, Fin.val_castSucc]; exact val_le_succAbove _ b)
              have := hγval b
              have := hdom b
              omega
            have hdomγ2 : ∀ b : Fin m, γ (Fin.succ (Fin.castSucc b)) ≤ S (Fin.succ b) := by
              intro b
              have hle : γ (Fin.succ (Fin.castSucc b))
                  ≤ γ ((j.castSucc.succ).succAbove (Fin.succ b)) := by
                refine hγ.monotone ?_
                rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
                have h := val_le_succAbove (j.castSucc.succ) (Fin.succ b)
                rw [Fin.val_succ] at h
                omega
              have := hγval (Fin.succ b)
              have := hdom (Fin.succ b)
              omega
            -- strict monotonicity of the five index families
            have hSsucc : StrictMono (S ∘ Fin.succ) := hS.comp Fin.strictMono_succ
            have hγsucc : StrictMono (γ ∘ Fin.succ) := hγ.comp Fin.strictMono_succ
            have hγcast : StrictMono (γ ∘ Fin.castSucc) := hγ.comp Fin.strictMono_castSucc
            have hCcast : StrictMono (C ∘ Fin.castSucc) := hC.comp Fin.strictMono_castSucc
            have hCsucc : StrictMono (C ∘ Fin.succ) := hC.comp Fin.strictMono_succ
            -- the five positive factors and the one merely nonnegative
            have hSsuccN : ∀ b : Fin m, (S ∘ Fin.succ) b < N := fun b => hSN _
            have hL2 : 0 < (A.submatrix (S ∘ Fin.succ) ((γ ∘ Fin.succ) ∘ Fin.castSucc)).det :=
              ihk m (by omega) _ _ hSsucc (hγsucc.comp Fin.strictMono_castSucc) hdomγ2 hSsuccN
            have hR1b : 0 < (A.submatrix (S ∘ Fin.succ) (C ∘ Fin.castSucc)).det := by
              refine ihk m (by omega) _ _ hSsucc hCcast (fun b => ?_) hSsuccN
              refine le_trans (hdom b.castSucc) (hS.monotone ?_)
              rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
              omega
            have hR2b : 0 < (A.submatrix (S ∘ Fin.succ) (C ∘ Fin.succ)).det :=
              ihk m (by omega) _ _ hSsucc hCsucc (fun b => hdom _) hSsuccN
            have hspC : C 0 ≤ C (Fin.last m) := hC.monotone (Fin.zero_le _)
            have hR2a : 0 < (A.submatrix S (γ ∘ Fin.castSucc)).det := by
              refine ihsp ((γ ∘ Fin.castSucc) (Fin.last m) - (γ ∘ Fin.castSucc) 0) ?_ _ _ hS
                hγcast hdomγ hSN le_rfl
              have e2 : (γ ∘ Fin.castSucc) (0 : Fin (m + 1)) = C 0 := by
                change γ (Fin.castSucc (0 : Fin (m + 1))) = C 0
                rw [show (Fin.castSucc (0 : Fin (m + 1)) : Fin (m + 2)) = 0 from rfl, hγ0]
              have h1 : (γ ∘ Fin.castSucc) (Fin.last m) < C (Fin.last m) := by
                rw [← hγlast]
                exact hγ (by rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last, Fin.val_last]; omega)
              have h3 : (γ ∘ Fin.castSucc) (0 : Fin (m + 1))
                  ≤ (γ ∘ Fin.castSucc) (Fin.last m) := hγcast.monotone (Fin.zero_le _)
              omega
            have hR1a : 0 ≤ (A.submatrix S (γ ∘ Fin.succ)).det := by
              by_cases hd : ∀ b, (γ ∘ Fin.succ) b ≤ S b
              · refine le_of_lt (ihsp ((γ ∘ Fin.succ) (Fin.last m) - (γ ∘ Fin.succ) 0) ?_ _ _ hS
                  hγsucc hd hSN le_rfl)
                have e1 : (γ ∘ Fin.succ) (Fin.last m) = C (Fin.last m) := by
                  change γ (Fin.succ (Fin.last m)) = C (Fin.last m)
                  rw [show (Fin.succ (Fin.last m) : Fin (m + 2)) = Fin.last (m + 1) from rfl,
                    hγlast]
                have h1 : C 0 < (γ ∘ Fin.succ) (0 : Fin (m + 1)) := by
                  change C 0 < γ (Fin.succ 0)
                  rw [← hγ0]
                  exact hγ (by rw [Fin.lt_def, Fin.val_succ]; simp)
                have h3 : (γ ∘ Fin.succ) (0 : Fin (m + 1)) ≤ (γ ∘ Fin.succ) (Fin.last m) :=
                  hγsucc.monotone (Fin.zero_le _)
                omega
              · push Not at hd
                obtain ⟨b, hb⟩ := hd
                exact le_of_eq (det_submatrix_eq_zero_of_row_lt_col hlow hS
                  hγsucc.monotone hb).symm
            -- the identity
            have hid := minor_three_term_col A γ hγ S j
            rw [hγC] at hid
            by_contra hcon
            rw [not_lt] at hcon
            nlinarith [hid, hL2, hR1a, hR1b, hR2a, hR2b, hcon]
          · -- no gap: the column set is consecutive
            push Not at hgap
            have hcons := eq_consecutive_of_no_gap C hC fun j => by
              have := hgap j; omega
            have hC0 : ∀ b : Fin (m + 1), C b = C 0 + (b : ℕ) := by
              intro b
              have h : C b = (b : ℕ) + C 0 := congrFun hcons b
              omega
            have heq : (fun b : Fin (m + 1) => C 0 + (b : ℕ)) = C := by
              funext b; exact (hC0 b).symm
            rw [← heq]
            refine det_consecutive_pos hlow hInit (C 0) S hS (fun b => by
              rw [← hC0 b]; exact hdom b) hSN ?_
            have h0 := hdom 0
            have h1 := hSN 0
            omega
      exact fun S C hS hC hdom hSN => inner (C (Fin.last m) - C 0) S C hS hC hdom hSN le_rfl

/-- **The unwindowed criterion.**  Taking the window past every index used. -/
theorem det_pos_of_initialPos {A : Matrix ℕ ℕ R} (hlow : ∀ i j : ℕ, i < j → A i j = 0)
    (hInit : InitialPos A) :
    ∀ (k : ℕ) (S C : Fin k → ℕ), StrictMono S → StrictMono C → (∀ b, C b ≤ S b) →
      0 < (A.submatrix S C).det := by
  intro k S C hS hC hdom
  refine det_pos_of_initialPosOn hlow (N := (Finset.univ.sup S) + 1)
    (fun k' S' h' _ => hInit k' S' h') k S C hS hC hdom fun b => ?_
  have h := Finset.le_sup (f := S) (Finset.mem_univ b)
  omega

end Criterion

end Shields
