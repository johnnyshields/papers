/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Schur polynomials from semistandard Young tableaux

Mathlib carries `YoungDiagram` and `SemistandardYoungTableau` but no Schur polynomials and no
finiteness for tableaux with bounded entries, so there is no object for a positivity statement to be
about. This supplies the object.

## Main definitions

* `Shields.BoundedSSYT`: the semistandard tableaux of shape `μ` whose entries on the cells of `μ`
  are all `< n`, with a `Fintype` instance.
* `Shields.schur`: the Schur polynomial `s_μ(x_0, …, x_{n-1})`, the generating function of
  `BoundedSSYT μ n` weighted by the product over the cells.

## Main results

* `Shields.schur_pos_iff`: over `ℝ` with `x i > 0` for `i < n`, `schur μ n x > 0` if and only if
  every column of `μ` has height at most `n`.
* `Shields.schur_eq_zero_of_lt_colLen`: a column taller than `n` leaves the index set empty, because
  a column is strictly increasing.
* `Shields.schur_rect`: `s_{(k ^ n)}(x_0, …, x_{n-1}) = (x_0 ⋯ x_{n-1}) ^ k` -- the `n`-by-`k`
  rectangle with entries `< n` admits exactly one tableau.

## Implementation notes

**`import Mathlib` is retained deliberately, and the specific list beneath it is exact.** This
file builds against those modules alone.  What the blanket import still carries is the transitive
Mathlib that *consumers* of this file rely on: dropping it here leaves the shared tree green and
breaks a paper that imports it.  Removing it therefore belongs to a pass that sweeps every
consuming tree's imports in the same change, and a Mathlib PR would carry the specific list only.

A tableau vanishes off `μ`, so it is determined by its restriction to `μ.cells`; that restriction
lands in `μ.cells → Fin n`, which is what gives the `Fintype` instance and hence a finite generating
function. Only the values `x i` for `i < n` occur, which is `schur_congr`.

Not proved here: Jacobi--Trudi, the skew case `μ ⊆ λ`, and the supersymmetric two-alphabet function.
Everything below is one alphabet and a straight shape.

## Tags

Schur polynomial, Young diagram, semistandard tableau, symmetric function
-/

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- Along a column, an entry exceeds a higher one by at least the row gap:
`T i j + (i' - i) ≤ T i' j` for `i ≤ i'`.  Iterating `col_strict`. -/
theorem entry_add_sub_le (T : SemistandardYoungTableau μ) (i j : ℕ) :
    ∀ i' : ℕ, i ≤ i' → (i', j) ∈ μ → T i j + (i' - i) ≤ T i' j := by
  intro i' hi
  induction i', hi using Nat.le_induction with
  | base => intro _; simp
  | succ i' hii' ih =>
    intro hcell
    have hcell' : (i', j) ∈ μ := μ.up_left_mem (Nat.le_succ i') le_rfl hcell
    have h1 := ih hcell'
    have h2 : T i' j < T (i' + 1) j := T.col_strict (Nat.lt_succ_self i') hcell
    omega

/-- A cell in row `i` carries an entry of at least `i`: the entries strictly above
it in the same column are `i` distinct naturals, all smaller. -/
theorem le_entry (T : SemistandardYoungTableau μ) {i j : ℕ} (hcell : (i, j) ∈ μ) :
    i ≤ T i j := by
  have h := T.entry_add_sub_le 0 j i (Nat.zero_le i) hcell
  omega

end SemistandardYoungTableau

namespace Shields

open Finset

/-! ## Tableaux with bounded entries, and their finiteness -/

/-- The semistandard Young tableaux of shape `μ` whose entries on the cells of
`μ` are all `< n`.  These are the tableaux that contribute to a Schur polynomial
in the `n` variables `x 0, …, x (n-1)`.

The bound is imposed on the cells only.  A tableau is zero off `μ` by
`SemistandardYoungTableau.zeros`, so bounding there as well would empty the type
at `n = 0` and destroy `schur ⊥ n x = 1`. -/
def BoundedSSYT (μ : YoungDiagram) (n : ℕ) : Type :=
  {T : SemistandardYoungTableau μ // ∀ i j, (i, j) ∈ μ → T i j < n}

namespace BoundedSSYT

variable {μ : YoungDiagram} {n : ℕ}

instance : CoeFun (BoundedSSYT μ n) fun _ => ℕ → ℕ → ℕ where
  coe T := T.1

theorem ext {T T' : BoundedSSYT μ n} (h : ∀ i j, T i j = T' i j) : T = T' :=
  Subtype.ext (SemistandardYoungTableau.ext h)

theorem lt (T : BoundedSSYT μ n) {i j : ℕ} (hcell : (i, j) ∈ μ) : T i j < n :=
  T.2 i j hcell

/-- `lt` in the form a product over `μ.cells` presents it, with the cell a single
variable rather than a pair of them. -/
theorem lt_of_mem_cells (T : BoundedSSYT μ n) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    T c.1 c.2 < n :=
  T.2 c.1 c.2 hc

theorem zeros (T : BoundedSSYT μ n) {i j : ℕ} (hcell : (i, j) ∉ μ) : T i j = 0 :=
  T.1.zeros hcell

/-- A bounded tableau is determined by its restriction to the cells of `μ`, and
that restriction is a map `μ.cells → Fin n`.  Hence there are finitely many. -/
theorem restrict_injective (μ : YoungDiagram) (n : ℕ) :
    Function.Injective fun (T : BoundedSSYT μ n) (c : μ.cells) =>
      (⟨T c.1.1 c.1.2, T.lt_of_mem_cells c.2⟩ : Fin n) := by
  intro T T' h
  refine BoundedSSYT.ext fun i j => ?_
  by_cases hc : (i, j) ∈ μ
  · exact congrArg Fin.val (congrFun h ⟨(i, j), (YoungDiagram.mem_cells _).mpr hc⟩)
  · rw [T.zeros hc, T'.zeros hc]

noncomputable instance instFintype (μ : YoungDiagram) (n : ℕ) :
    Fintype (BoundedSSYT μ n) :=
  Fintype.ofInjective _ (restrict_injective μ n)

/-- Every column of `μ` is at most `n` tall once a bounded tableau exists: the
bottom cell of column `j` sits in row `colLen j - 1`, so its entry is at least
`colLen j - 1` and at the same time less than `n`. -/
theorem colLen_le (T : BoundedSSYT μ n) (j : ℕ) : μ.colLen j ≤ n := by
  rcases Nat.eq_zero_or_pos (μ.colLen j) with h | h
  · omega
  · have hcell : (μ.colLen j - 1, j) ∈ μ :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have h1 := T.1.le_entry hcell
    have h2 := T.lt hcell
    omega

/-- `highestWeight`, which fills row `i` with `i`, is entry-bounded by `n`
exactly when every column of `μ` fits in `n` rows. -/
def highestWeight (μ : YoungDiagram) (n : ℕ) (h : ∀ j, μ.colLen j ≤ n) :
    BoundedSSYT μ n :=
  ⟨SemistandardYoungTableau.highestWeight μ, by
    intro i j hij
    rw [SemistandardYoungTableau.highestWeight_apply, if_pos hij]
    exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp hij) (h j)⟩

@[simp]
theorem highestWeight_apply {h : ∀ j, μ.colLen j ≤ n} {i j : ℕ} :
    highestWeight μ n h i j = if (i, j) ∈ μ then i else 0 :=
  rfl

end BoundedSSYT

/-! ## The Schur polynomial -/

variable {R : Type*} [CommSemiring R]

/-- The Schur polynomial of shape `μ` in the `n` variables `x 0, …, x (n-1)`,
defined as the generating function of the semistandard tableaux of shape `μ`
with entries `< n`:

`schur μ n x = ∑_T ∏_{(i,j) ∈ μ} x (T i j)`.

Only the values `x i` with `i < n` occur; see `schur_congr`. -/
noncomputable def schur (μ : YoungDiagram) (n : ℕ) (x : ℕ → R) : R :=
  ∑ T : BoundedSSYT μ n, ∏ c ∈ μ.cells, x (T c.1 c.2)

theorem schur_congr (μ : YoungDiagram) (n : ℕ) {x y : ℕ → R}
    (h : ∀ i, i < n → x i = y i) : schur μ n x = schur μ n y := by
  refine Finset.sum_congr rfl fun T _ => Finset.prod_congr rfl fun c hc => ?_
  exact h _ (T.lt_of_mem_cells hc)

/-! ## The positivity criterion

The Schur function is positive exactly when no column is taller than the number
of variables.
-/

/-- The vanishing half.  A column taller than `n` cannot be filled by strictly
increasing entries below `n`, so `BoundedSSYT μ n` is empty. -/
theorem isEmpty_boundedSSYT_of_lt_colLen {μ : YoungDiagram} {n j : ℕ}
    (h : n < μ.colLen j) : IsEmpty (BoundedSSYT μ n) :=
  ⟨fun T => absurd (T.colLen_le j) (by omega)⟩

theorem schur_eq_zero_of_lt_colLen {μ : YoungDiagram} {n j : ℕ} (x : ℕ → R)
    (h : n < μ.colLen j) : schur μ n x = 0 := by
  have : IsEmpty (BoundedSSYT μ n) := isEmpty_boundedSSYT_of_lt_colLen h
  rw [schur, Finset.univ_eq_empty, Finset.sum_empty]

theorem schur_nonneg {μ : YoungDiagram} {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, i < n → 0 ≤ x i) : 0 ≤ schur μ n x :=
  Finset.sum_nonneg fun T _ =>
    Finset.prod_nonneg fun _c hc => hx _ (T.lt_of_mem_cells hc)

/-- The positivity half.  With every column of `μ` at most `n` tall and every
variable positive, the sum is over a nonempty set of tableaux — `highestWeight`
is one — and each term is a product of positive numbers. -/
theorem schur_pos {μ : YoungDiagram} {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, i < n → 0 < x i) (h : ∀ j, μ.colLen j ≤ n) : 0 < schur μ n x := by
  refine Finset.sum_pos (fun T _ => ?_) ⟨BoundedSSYT.highestWeight μ n h, mem_univ _⟩
  exact Finset.prod_pos fun c hc => hx _ (T.lt_of_mem_cells hc)

/-- **The positivity criterion on a straight shape.**  With positive variables, `s_μ(x_0, …,
x_{n-1}) > 0` exactly when every column of `μ` has height
at most `n`. -/
theorem schur_pos_iff {μ : YoungDiagram} {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, i < n → 0 < x i) : 0 < schur μ n x ↔ ∀ j, μ.colLen j ≤ n := by
  refine ⟨fun hpos j => ?_, schur_pos hx⟩
  by_contra hj
  exact absurd (schur_eq_zero_of_lt_colLen x (by omega : n < μ.colLen j)) (by
    exact ne_of_gt hpos)

/-- Column heights are antitone, so the whole criterion is decided by the first
column, whose height `μ.colLen 0` is the number of rows of `μ`
(`YoungDiagram.length_rowLens`). -/
theorem forall_colLen_le_iff {μ : YoungDiagram} {n : ℕ} :
    (∀ j, μ.colLen j ≤ n) ↔ μ.colLen 0 ≤ n :=
  ⟨fun h => h 0, fun h j => le_trans (μ.colLen_anti 0 j (Nat.zero_le j)) h⟩

/-- The criterion in row form: the shape has at most `n` rows. -/
theorem schur_pos_iff_rowLens_length {μ : YoungDiagram} {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ i, i < n → 0 < x i) : 0 < schur μ n x ↔ μ.rowLens.length ≤ n := by
  rw [schur_pos_iff hx, forall_colLen_le_iff, YoungDiagram.length_rowLens]

/-! ## The rectangle

On the `n`-by-`k` rectangle with `n` variables the two column bounds of
`SemistandardYoungTableau` meet, leaving a single tableau.
-/

/-- The `n`-by-`k` rectangular Young diagram. -/
def rect (n k : ℕ) : YoungDiagram where
  cells := Finset.range n ×ˢ Finset.range k
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.mem_range] at hb ⊢
    exact ⟨lt_of_le_of_lt hab.1 hb.1, lt_of_le_of_lt hab.2 hb.2⟩

@[simp]
theorem cells_rect (n k : ℕ) : (rect n k).cells = Finset.range n ×ˢ Finset.range k :=
  rfl

@[simp]
theorem mem_rect {n k i j : ℕ} : (i, j) ∈ rect n k ↔ i < n ∧ j < k := by
  simp [rect, ← YoungDiagram.mem_cells]

theorem colLen_rect_of_lt {n k j : ℕ} (hj : j < k) : (rect n k).colLen j = n := by
  have key : ∀ i : ℕ, i < (rect n k).colLen j ↔ i < n := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_rect]
    exact ⟨fun h => h.1, fun h => ⟨h, hj⟩⟩
  rcases lt_trichotomy ((rect n k).colLen j) n with h | h | h
  · exact absurd ((key _).mpr h) (lt_irrefl _)
  · exact h
  · exact absurd ((key n).mp h) (lt_irrefl n)

theorem colLen_rect_le (n k j : ℕ) : (rect n k).colLen j ≤ n := by
  by_cases hj : j < k
  · exact le_of_eq (colLen_rect_of_lt hj)
  · have : (rect n k).colLen j = 0 := by
      by_contra h
      have : (0, j) ∈ rect n k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      exact hj (mem_rect.mp this).2
    omega

/-- On the `n`-by-`k` rectangle, a tableau with entries `< n` has `T i j = i`.
Below, `le_entry`; above, the column-gap bound run to the bottom of the column,
where the entry is still `< n`. -/
theorem entry_rect {n k : ℕ} (T : BoundedSSYT (rect n k) n) {i j : ℕ}
    (hcell : (i, j) ∈ rect n k) : T i j = i := by
  obtain ⟨hi, hj⟩ := mem_rect.mp hcell
  have hbot : (n - 1, j) ∈ rect n k := mem_rect.mpr ⟨by omega, hj⟩
  have hgap := T.1.entry_add_sub_le i j (n - 1) (by omega) hbot
  have hlt := T.lt hbot
  have hge := T.1.le_entry hcell
  omega

/-- The rectangle with entries `< n` admits exactly one tableau, `highestWeight`. -/
theorem boundedSSYT_rect_eq {n k : ℕ} (T T' : BoundedSSYT (rect n k) n) : T = T' := by
  refine BoundedSSYT.ext fun i j => ?_
  by_cases hc : (i, j) ∈ rect n k
  · rw [entry_rect T hc, entry_rect T' hc]
  · rw [T.zeros hc, T'.zeros hc]

/-- **The rectangle.**  `s_{(k^n)}(x_0, …, x_{n-1}) = (x_0 ⋯ x_{n-1})^k`. -/
theorem schur_rect (n k : ℕ) (x : ℕ → R) :
    schur (rect n k) n x = (∏ i ∈ Finset.range n, x i) ^ k := by
  set T₀ : BoundedSSYT (rect n k) n :=
    BoundedSSYT.highestWeight _ n (colLen_rect_le n k) with hT₀
  have huniv : (Finset.univ : Finset (BoundedSSYT (rect n k) n)) = {T₀} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨mem_univ _, fun T _ => boundedSSYT_rect_eq T T₀⟩
  rw [schur, huniv, Finset.sum_singleton]
  calc ∏ c ∈ (rect n k).cells, x (T₀ c.1 c.2)
      = ∏ c ∈ Finset.range n ×ˢ Finset.range k, x c.1 := by
        refine Finset.prod_congr rfl fun c hc => ?_
        rw [entry_rect T₀ ((YoungDiagram.mem_cells c).mp hc)]
    _ = ∏ i ∈ Finset.range n, ∏ _j ∈ Finset.range k, x i :=
        Finset.prod_product' (Finset.range n) (Finset.range k) (fun i _ => x i)
    _ = ∏ i ∈ Finset.range n, x i ^ k := by simp
    _ = (∏ i ∈ Finset.range n, x i) ^ k := Finset.prod_pow _ _ _

/-- The empty diagram is the `k = 0` rectangle, so its Schur polynomial is `1`. -/
theorem schur_bot (n : ℕ) (x : ℕ → R) : schur ⊥ n x = 1 := by
  have h : rect n 0 = ⊥ := by
    ext c
    simp
  rw [← h, schur_rect, pow_zero]

end Shields
