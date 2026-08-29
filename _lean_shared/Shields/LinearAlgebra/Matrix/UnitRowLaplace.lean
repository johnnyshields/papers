/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Common

/-!
# Laplace expansion along unit rows

Mathlib expands a determinant along **one** row (`Matrix.det_succ_row`).  This file supplies the
specialization to a row that is a standard basis vector, its two-row form, and the deletion of
`k` unit rows at once, together with the `q`-expansion of `det(A + qB)` those deletions evaluate.

## Main results

* `Shields.det_of_row_eq_single`: if row `i` of `M` is `e_j`, the expansion at `i` has a single
  surviving term, so `det M = (-1)^{i+j} · det M[î | ĵ]`.
* `Shields.det_of_two_rows_eq_single`: rows `i₀ < i₁` are `e_{j₀}` and `e_{j₁}` with `j₀ < j₁`.
  Deleting the first pair moves the second row and column index down by one **each**, so the
  two shifts cancel in the exponent and the accumulated sign is again `(-1)^{Σ(i + j)}`.
* `Shields.det_of_unitRows`, `Shields.det_of_unitRows_of_card`: `k` unit rows deleted at once.
  The surviving minor is taken on strictly monotone selections avoiding the deleted rows, and
  the sign is again `(-1)^{Σ(ι a + κ a)}`.
* `Shields.det_add_smul_eq_sum`: the `q`-expansion of `det(A + qB)` over row subsets, each
  subset taken from `B` contributing a power of `q` equal to its size.

## Implementation notes

The `q`-expansion of `det(A + qE)` with `E` carrying unit rows has coefficients that are, term
by term, complementary minors of `A`.  Reading them off means deleting a set of unit rows at
once, and the sign cancellation above is why the sign comes out `+1` when the row and column
sets are translates of one another: `Σ(i + (i - c))` is even for a constant shift `c`.

Expanding `det(A + qB)` over row subsets is **not** missing from Mathlib:
`MultilinearMap.map_add_univ` does it for any multilinear map, and `Matrix.detRowAlternating`
is that map in the rows.  `det_add_smul_eq_sum` is that statement in matrix language with the
scalar pulled out, and costs nothing beyond naming.

The `k`-row deletion is the one thing genuinely absent upstream.  The induction peels the
smallest unit row, and `exists_strictMono_succAbove_zero` carries the `succAbove` bookkeeping
that peel needs -- the row and the column family use it identically.  The two-row case is that
induction at `k = 2`, kept because it is where the sign cancellation is visible.

The statement does **not** name the surviving row and column selections -- it asserts only that
they exist, are strictly monotone, and avoid the deleted rows.  That sidesteps having to
present the complement of a `Finset` as an ordered index type, and it is exactly what a
total-nonnegativity hypothesis consumes.  The avoidance clause is what identifies the surviving
minor as a minor of the *other* summand: without it the conclusion is a determinant identity
that carries no sign information.

## Tags

determinant, laplace expansion, minor, unit row, multilinear
-/
namespace Shields

open Matrix

variable {R : Type*} [CommRing R]

/-- **Laplace expansion along a unit row.**  If row `i` of `M` is the standard basis vector
`e_j`, the expansion of `Matrix.det_succ_row` at `i` has a single surviving term. -/
theorem det_of_row_eq_single {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (i j : Fin (n + 1)) (hrow : ∀ k, M i k = if k = j then 1 else 0) :
    M.det = (-1) ^ ((i : ℕ) + (j : ℕ)) * (M.submatrix i.succAbove j.succAbove).det := by
  rw [Matrix.det_succ_row M i, Finset.sum_eq_single j]
  · rw [hrow j, if_pos rfl, mul_one]
  · intro b _ hb
    rw [hrow b, if_neg hb, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **A unit row survives the deletion of another row and its column.**  If row `r` of `M` is
`e_c`, and `r`, `c` are the images of `a`, `b` under deletion at `p`, `q`, then row `a` of the
deleted matrix is `e_b`.  Injectivity of `Fin.succAbove` is what keeps the other entries at
zero. -/
theorem submatrix_succAbove_row_eq_single {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    {p q r c : Fin (N + 1)} {a b : Fin N}
    (hrow : ∀ k, M r k = if k = c then 1 else 0)
    (ha : p.succAbove a = r) (hb : q.succAbove b = c) (k : Fin N) :
    (M.submatrix p.succAbove q.succAbove) a k = if k = b then 1 else 0 := by
  rw [Matrix.submatrix_apply, ha, hrow]
  by_cases hk : k = b
  · rw [if_pos hk, hk, hb, if_pos rfl]
  · refine (if_neg ?_).trans (if_neg hk).symm
    intro hc
    exact hk (Fin.succAbove_right_inj.mp (hc.trans hb.symm))

/-- `succAbove` above the deleted index is `succ`: the surviving index drops by one. -/
theorem val_of_succAbove_eq {n : ℕ} {p : Fin (n + 2)} {a : Fin (n + 1)} {r : Fin (n + 2)}
    (h : p.succAbove a = r) (hpr : p < r) : (r : ℕ) = (a : ℕ) + 1 := by
  rcases lt_or_ge a.castSucc p with hlt | hge
  · rw [Fin.succAbove_of_castSucc_lt _ _ hlt] at h
    exact absurd (h ▸ hlt) (not_lt.mpr hpr.le)
  · rw [Fin.succAbove_of_le_castSucc _ _ hge] at h
    rw [← h]
    rfl

/-- **Laplace expansion along two unit rows.**  Rows `i₀ < i₁` are the unit vectors `e_{j₀}`
and `e_{j₁}` with `j₀ < j₁`.  The sign is `(-1)^{i₀+j₀+i₁+j₁}`: deleting the first pair drops
both the second row index and the second column index by one, and the two drops cancel. -/
theorem det_of_two_rows_eq_single {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    {i₀ i₁ j₀ j₁ : Fin (n + 2)} {a b : Fin (n + 1)} (hi : i₀ < i₁) (hj : j₀ < j₁)
    (h₀ : ∀ k, M i₀ k = if k = j₀ then 1 else 0)
    (h₁ : ∀ k, M i₁ k = if k = j₁ then 1 else 0)
    (ha : i₀.succAbove a = i₁) (hb : j₀.succAbove b = j₁) :
    M.det = (-1) ^ ((i₀ : ℕ) + (j₀ : ℕ) + (i₁ : ℕ) + (j₁ : ℕ))
      * ((M.submatrix i₀.succAbove j₀.succAbove).submatrix a.succAbove b.succAbove).det := by
  have hrow := submatrix_succAbove_row_eq_single M h₁ ha hb
  rw [det_of_row_eq_single M i₀ j₀ h₀,
    det_of_row_eq_single (M.submatrix i₀.succAbove j₀.succAbove) a b hrow, ← mul_assoc]
  have hav : (i₁ : ℕ) = (a : ℕ) + 1 := val_of_succAbove_eq ha hi
  have hbv : (j₁ : ℕ) = (b : ℕ) + 1 := val_of_succAbove_eq hb hj
  have hexp : (i₀ : ℕ) + (j₀ : ℕ) + (i₁ : ℕ) + (j₁ : ℕ)
      = ((i₀ : ℕ) + (j₀ : ℕ) + ((a : ℕ) + (b : ℕ))) + 2 := by omega
  rw [hexp, pow_add, pow_add]
  ring

/-! ## The determinant of a sum, as a sum over row subsets

`MultilinearMap.map_add_univ` already expands a multilinear map of a sum over all subsets of
the coordinates, and `Matrix.detRowAlternating` is that map in the rows.  The two wrappers
below put it in matrix language, with the scalar pulled out: they are the other half of the
Laplace machinery a `q`-expansion needs, and unlike the unit-row deletion they cost nothing
beyond naming.
-/

section AddExpansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The determinant of a sum, expanded over row subsets.**  `det(A + B)` is the sum over
subsets `s` of the determinant of the matrix taking its rows from `A` on `s` and from `B`
off `s`. -/
theorem det_add_eq_sum_piecewise (A B : Matrix ι ι R) :
    (A + B).det = ∑ s : Finset ι, (Matrix.of (s.piecewise (A : ι → ι → R) B)).det :=
  (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).toMultilinearMap.map_add_univ A B

/-- Scaling the rows off `s` by `q` scales the determinant by `q^{|sᶜ|}`: the scaled matrix is
a diagonal matrix times the original. -/
theorem det_piecewise_smul (A B : Matrix ι ι R) (q : R) (s : Finset ι) :
    (Matrix.of (s.piecewise (A : ι → ι → R) (q • B))).det
      = q ^ sᶜ.card * (Matrix.of (s.piecewise (A : ι → ι → R) B)).det := by
  have hmat : Matrix.of (s.piecewise (A : ι → ι → R) (q • B))
      = Matrix.diagonal (fun i => if i ∈ s then (1 : R) else q)
        * Matrix.of (s.piecewise (A : ι → ι → R) B) := by
    ext i j
    rw [Matrix.diagonal_mul]
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  have hprod : (∏ i : ι, if i ∈ s then (1 : R) else q) = q ^ sᶜ.card := by
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 2
    ext i
    simp
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal, hprod]

/-- **The `q`-expansion of `det(A + qB)`.**  Each subset of rows taken from `B` contributes a
power of `q` equal to its size.  With `B` carrying unit rows this is the expansion whose terms
`det_of_row_eq_single` and `det_of_two_rows_eq_single` evaluate. -/
theorem det_add_smul_eq_sum (A B : Matrix ι ι R) (q : R) :
    (A + q • B).det
      = ∑ s : Finset ι, q ^ sᶜ.card * (Matrix.of (s.piecewise (A : ι → ι → R) B)).det := by
  rw [det_add_eq_sum_piecewise A (q • B)]
  exact Finset.sum_congr rfl fun s _ => det_piecewise_smul A B q s

/-- A subset whose complement meets a zero row of `B` contributes nothing. -/
theorem det_piecewise_eq_zero_of_row_zero {A B : Matrix ι ι R} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (hrow : B i = 0) :
    (Matrix.of (s.piecewise (A : ι → ι → R) B)).det = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero i ?_
  intro j
  have hpw : (s.piecewise (A : ι → ι → R) B) i = B i :=
    Finset.piecewise_eq_of_notMem _ _ _ hi
  simp [Matrix.of_apply, hpw, hrow]

end AddExpansion

/-! ## The `k`-row case

Peeling the smallest unit row and recursing.  Each peel drops every remaining row index and
every remaining column index by one, so the shifts cancel in pairs and the accumulated sign is
`(-1)^{Σ(ι a + κ a)}` -- the two-row case above is this induction at `k = 2`.

The surviving row and column selections are **not named**: the statement asserts only that
they exist and are strictly monotone.  That is what a total-nonnegativity hypothesis consumes,
and it is what lets the induction carry composites of `succAbove` instead of having to
identify the complement of a `Finset` as an ordered index type.
-/

section UnitRows

/-- **Peeling the smallest member of a strictly monotone family.**  A strictly monotone
`ν : Fin (k + 1) → Fin (N + 1)` is its smallest member `ν 0` inserted into a strictly monotone
family `ν'` of length `k`, via `succAbove` at that member.  Each `ν' a` sits one below
`ν a.succ`, since every later member is past `ν 0`. -/
theorem exists_strictMono_succAbove_zero {N k : ℕ} {ν : Fin (k + 1) → Fin (N + 1)}
    (hν : StrictMono ν) :
    ∃ ν' : Fin k → Fin N, StrictMono ν' ∧ (∀ a, ((ν' a : ℕ)) + 1 = (ν a.succ : ℕ)) ∧
      ∀ a, (ν 0).succAbove (ν' a) = ν a.succ := by
  have hpos : ∀ a : Fin k, ν 0 < ν a.succ := fun a => hν (Fin.succ_pos a)
  have hne : ∀ a : Fin k, ν a.succ ≠ 0 := fun a =>
    Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) (hpos a))
  have hval : ∀ a, (((ν a.succ).pred (hne a) : Fin N) : ℕ) + 1 = (ν a.succ : ℕ) := by
    intro a
    have := hpos a
    rw [Fin.lt_def] at this
    rw [Fin.val_pred]
    omega
  refine ⟨fun a => (ν a.succ).pred (hne a), fun a b hab => ?_, hval, fun a => ?_⟩
  · change (ν a.succ).pred (hne a) < (ν b.succ).pred (hne b)
    rw [Fin.lt_def]
    have hlt := hν (Fin.succ_lt_succ_iff.mpr hab)
    rw [Fin.lt_def] at hlt
    have ha := hval a
    have hb := hval b
    omega
  · change (ν 0).succAbove ((ν a.succ).pred (hne a)) = ν a.succ
    have hle : ν 0 ≤ ((ν a.succ).pred (hne a)).castSucc := by
      rw [Fin.le_def, Fin.val_castSucc]
      have hv := hval a
      have h2 := hpos a
      rw [Fin.lt_def] at h2
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    exact Fin.succ_pred _ _

/-- **Laplace expansion along `k` unit rows.**  If rows `ι 0 < ⋯ < ι (k-1)` of `M` are the
standard basis vectors `e_{κ 0}, …, e_{κ (k-1)}` with `κ` increasing as well, then `det M` is
`(-1)^{Σ(ι a + κ a)}` times a minor of `M` taken on strictly increasing selections.

In particular the sign is `+1` whenever `κ a = ι a - c` for a constant `c`, since then each
`ι a + κ a` differs from `2 ι a` by `c` and the total is congruent to `k·c` modulo 2 -- for the
mixed staircase `T_{n,2} + qS_n^2`, where `c = 2`, it is always `+1`. -/
theorem det_of_unitRows (m : ℕ) :
    ∀ (k : ℕ) (M : Matrix (Fin (m + k)) (Fin (m + k)) R) (ι κ : Fin k → Fin (m + k)),
      StrictMono ι → StrictMono κ →
      (∀ a c, M (ι a) c = if c = κ a then 1 else 0) →
      ∃ f g : Fin m → Fin (m + k), StrictMono f ∧ StrictMono g ∧ (∀ a b, f a ≠ ι b) ∧
        M.det = (-1) ^ (∑ a, ((ι a : ℕ) + (κ a : ℕ))) * (M.submatrix f g).det := by
  intro k
  induction k with
  | zero =>
      intro M ι κ _ _ _
      exact ⟨id, id, strictMono_id, strictMono_id, fun _ b => b.elim0, by simp⟩
  | succ k ih =>
      intro M ι κ hι hκ hrow
      -- the tails of the two families, peeled at their smallest members
      obtain ⟨ι', hι'mono, hι'val, hιsucc⟩ := exists_strictMono_succAbove_zero hι
      obtain ⟨κ', hκ'mono, hκ'val, hκsucc⟩ := exists_strictMono_succAbove_zero hκ
      -- the smallest unit row, and its column
      set i₀ : Fin (m + k + 1) := ι 0 with hi₀
      set j₀ : Fin (m + k + 1) := κ 0 with hj₀
      set M' : Matrix (Fin (m + k)) (Fin (m + k)) R :=
        M.submatrix i₀.succAbove j₀.succAbove with hM'
      have hrow' : ∀ a c, M' (ι' a) c = if c = κ' a then 1 else 0 := fun a =>
        submatrix_succAbove_row_eq_single M (hrow a.succ) (hιsucc a) (hκsucc a)
      obtain ⟨f', g', hf', hg', havoid', hdet'⟩ := ih M' ι' κ' hι'mono hκ'mono hrow'
      have havoid : ∀ (a : Fin m) (b : Fin (k + 1)), i₀.succAbove (f' a) ≠ ι b := by
        intro a b
        refine Fin.cases ?_ ?_ b
        · exact hi₀ ▸ Fin.succAbove_ne i₀ (f' a)
        · intro c hc
          rw [← hιsucc c] at hc
          exact havoid' a c (Fin.succAbove_right_injective (p := i₀) hc)
      refine ⟨i₀.succAbove ∘ f', j₀.succAbove ∘ g',
        (Fin.strictMono_succAbove i₀).comp hf', (Fin.strictMono_succAbove j₀).comp hg',
        havoid, ?_⟩
      rw [det_of_row_eq_single M i₀ j₀ (hrow 0), hdet', ← mul_assoc, ← Matrix.submatrix_submatrix,
        ← hM']
      congr 1
      have hsum : ∑ a : Fin k, ((ι' a : ℕ) + (κ' a : ℕ)) + 2 * k
          = ∑ a : Fin k, ((ι a.succ : ℕ) + (κ a.succ : ℕ)) := by
        rw [show 2 * k = ∑ _a : Fin k, 2 by simp [mul_comm], ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        have ha := hι'val a
        have hb := hκ'val a
        omega
      have htot : ∑ a : Fin (k + 1), ((ι a : ℕ) + (κ a : ℕ))
          = ((i₀ : ℕ) + (j₀ : ℕ) + ∑ a : Fin k, ((ι' a : ℕ) + (κ' a : ℕ))) + 2 * k := by
        rw [Fin.sum_univ_succ, ← hsum]
        omega
      have hpar : ∀ x y : ℕ, ((-1 : R)) ^ (x + 2 * y) = (-1) ^ x := fun x y => by
        rw [pow_add, pow_mul]
        norm_num
      rw [htot, hpar]
      simp [pow_add]

/-- `det_of_unitRows` on a square matrix of unsplit size, with the split supplied as a
hypothesis.  A caller enumerating the unit rows as a `Finset` knows `n = s.card + sᶜ.card`
rather than working in `Fin (m + k)` from the start. -/
theorem det_of_unitRows_of_card {n m k : ℕ} (hn : n = m + k)
    (M : Matrix (Fin n) (Fin n) R) (ι κ : Fin k → Fin n)
    (hι : StrictMono ι) (hκ : StrictMono κ)
    (hrow : ∀ a c, M (ι a) c = if c = κ a then 1 else 0) :
    ∃ f g : Fin m → Fin n, StrictMono f ∧ StrictMono g ∧ (∀ a b, f a ≠ ι b) ∧
      M.det = (-1) ^ (∑ a, ((ι a : ℕ) + (κ a : ℕ))) * (M.submatrix f g).det := by
  subst hn
  exact det_of_unitRows m k M ι κ hι hκ hrow

end UnitRows


/-! ### Axiom footprint -/

/-- info: 'Shields.det_of_two_rows_eq_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_of_two_rows_eq_single

/-- info: 'Shields.det_of_unitRows_of_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_of_unitRows_of_card

/-- info: 'Shields.det_add_smul_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_add_smul_eq_sum

end Shields
