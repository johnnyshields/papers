/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.RhoOneDominanceComposition

/-!
# `thm:weighted-dominance`: the four cells, and that they exhaust the class

`subsec:proof` walks a `2 × 2` grid.  `ρ` — the multiplicity of the smallest zero
— governs the **lower** endpoint: the principal pair collides at that zero when it
is repeated, and at the critical point `t_a` of `eq:ab-def` when it is simple.  `r`
governs the **upper** endpoint independently: the pair collapses into the origin at
`2 ≤ r` and onto a finite `-L` at `r = 1`.  The two are independent, so there are
four cells and each needs its own endpoint block.

* `2 ≤ ρ`, `r = 1` — `ft_weighted_dominance_one_unconditional`
* `2 ≤ ρ`, `2 ≤ r` — `ft_weighted_dominance_unconditional`
* `ρ = 1`, `r = 1` — `ft_weighted_dominance_rho_one_unconditional`
* `ρ = 1`, `2 ≤ r` — `ft_weighted_dominance_rho_one_two_le_unconditional`

**Why this module exists.**  Four theorems covering a class is not the same as one
theorem stating it, and until this file nothing in the tree said the four exhaust
the grid — a reader had to reconstruct the partition from four signatures.  Done
that way it was got wrong: the `n = 3` and `n ≥ 4` halves of the `2 ≤ ρ`, `r = 1`
cell were counted as two cells, which made four look like four while `ρ = 1`,
`2 ≤ r` was empty.  So the partition is **checked** here rather than asserted, and
each cell is elaborated against the theorem that covers it, so a missing cell or a
drifted signature fails the build instead of a reading.

**The `n` ranges are the paper's, not binders stronger than needed.**  Both `r = 1`
cells carry `3 ≤ n`, because Forgács–Tran's Lemmas 2–6 and Props. 1–2 both exclude
`(deg Q, r) = (2,1)`, where `τ` is constant; with `deg Q ≥ 2` that leaves `n ≥ 3`
at `r = 1` exactly.  That excluded case is a remark of the manuscript, handled by
other means, and is **not** covered by any cell here.

## Main statements

* `simple_of_card_eq_one` — the two ways the grid says "the smallest zero is
  simple" agree: a fiber of size one is a zero no other index matches.
* `ft_dominance_cell_of_admissible` — every admissible pencil lands in one of the
  four cells, with that cell's own `n` range.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `subsec:proof`, `eq:ab-def`, `eq:Q-hypotheses`, `rem:quadratic-case`.

## Tags

weighted dominance, case partition, exhaustiveness, endpoint dichotomy
-/

namespace ForgacsTran

open Polynomial

/-- **The two spellings of "the smallest zero is simple" agree.**  The `2 ≤ ρ`
cells count the fiber of the smallest zero; the `ρ = 1` cells say no other index
matches it.  A fiber of size one is the second, since the fiber always contains its
own index. -/
theorem simple_of_card_eq_one {n : ℕ} {a : Fin n → ℝ} {i : Fin n}
    (hcard : (Finset.univ.filter fun k => a k = a i).card = 1) :
    ∀ k, k ≠ i → a k ≠ a i := by
  classical
  intro k hk hEq
  have hi : i ∈ Finset.univ.filter fun k => a k = a i := by simp
  have hkmem : k ∈ Finset.univ.filter fun k => a k = a i := by simp [hEq]
  have h2 : 1 < (Finset.univ.filter fun k => a k = a i).card :=
    Finset.one_lt_card.2 ⟨k, hkmem, i, hi, hk⟩
  omega

/-- **Every admissible pencil lands in one of the four cells.**  `ρ ≥ 1` is not
assumed — the fiber of the smallest zero contains its own index — and the `n` range
attached to each cell is that cell's theorem's own.

Dropping any one disjunct makes this unprovable, which is the point: the
exhaustiveness is checked rather than read off four signatures. -/
theorem ft_dominance_cell_of_admissible {n r ρ : ℕ} {a : Fin n → ℝ} {i : Fin n}
    (hn2 : 2 ≤ n) (hr : 1 ≤ r) (hne21 : ¬(n = 2 ∧ r = 1))
    (hcard : (Finset.univ.filter fun k => a k = a i).card = ρ) :
    (ρ = 1 ∧ r = 1 ∧ 3 ≤ n) ∨ (ρ = 1 ∧ 2 ≤ r ∧ 2 ≤ n)
      ∨ (2 ≤ ρ ∧ r = 1 ∧ 3 ≤ n) ∨ (2 ≤ ρ ∧ 2 ≤ r ∧ 2 ≤ n) := by
  classical
  have hρ1 : 1 ≤ ρ := by
    rw [← hcard]
    exact Finset.card_pos.2 ⟨i, by simp⟩
  by_cases h21 : n = 2
  · have : r ≠ 1 := fun h => hne21 ⟨h21, h⟩
    omega
  · omega

/-! ### Each cell against the theorem that covers it

The partition above is arithmetic; on its own it would not notice a cell whose
theorem had moved.  Elaborating each cell's hypotheses into its theorem is what
ties the two together, so a signature change fails here rather than in a reading.
The `2 ≤ ρ` cells take the fiber count directly; the `ρ = 1` cells take it through
`simple_of_card_eq_one`. -/

example {n r ρ : ℕ} {a : Fin n → ℝ} {c : ℝ} {i : Fin n}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hmin : ∀ k, a i ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = a i).card = ρ) (hρ : ρ = 1) : True := by
  have _cell := ft_weighted_dominance_rho_one_two_le_unconditional hn2 ha hc hr hmin
    (simple_of_card_eq_one (by rw [hcard, hρ]))
  trivial

example {n ρ : ℕ} {a : Fin n → ℝ} {c : ℝ} {i : Fin n}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hmin : ∀ k, a i ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = a i).card = ρ) (hρ : ρ = 1) : True := by
  have _cell := ft_weighted_dominance_rho_one_unconditional hn3 ha hc hmin
    (simple_of_card_eq_one (by rw [hcard, hρ]))
  trivial

example {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) : True := by
  have _cell := ft_weighted_dominance_unconditional hn2 ha hc hr hx₁ hmin hcard hρ
  trivial

example {n ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) : True := by
  have _cell := ft_weighted_dominance_one_unconditional hn3 ha hc hx₁ hmin hcard hρ
  trivial

end ForgacsTran
