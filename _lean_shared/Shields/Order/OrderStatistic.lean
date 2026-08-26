/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Finset.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Order statistics of a finite family of reals

The `k`-th **order statistic** of `x : Fin n → ℝ` is its `k`-th smallest entry, counted from
`0` and with multiplicity.  `Shields.orderStat` defines it in min–max form,

  `orderStat k x = ⨅_{|S| = k+1} max_{i ∈ S} x i`,

the least, over the `(k+1)`-element subsets of the index set, of the greatest entry on the
subset.  For `k + 1 > n` there is no such subset and the value is `0`.

Mathlib sorts a tuple by a permutation (`Tuple.sort`) and has no function returning the `k`-th
smallest entry, hence nothing about how sorting moves when the family does.  The min–max form is
chosen because in it the two facts one wants are short: the map is `1`-Lipschitz for the sup
norm, so sorting a continuously varying family keeps every ordered entry continuous, and the
value is pinned by the two counts around it.

## Main results

* `Shields.orderStat_of_monotone` -- on an already ordered family the `k`-th order statistic is
  the `k`-th entry, so the definition deserves its name.
* `Shields.abs_orderStat_sub_le`, `Shields.lipschitzWith_orderStat`,
  `Shields.continuous_orderStat` -- the `k`-th order statistic moves by at most the sup-norm
  displacement of the family.
* `Shields.orderStat_eq_of_card` -- if at most `k` entries lie strictly below `τ` and at least
  `k + 1` lie weakly below it, the `k`-th order statistic is `τ`.
* `Shields.orderStat_pair_eq_of_coalescence` -- with exactly `m` entries strictly below `τ` and
  at least two equal to it, `τ` occupies the two consecutive positions `m` and `m + 1`.

## Implementation notes

The infimum is indexed by the subtype `{S : Finset (Fin n) // S.card = k + 1}`, which is empty
exactly when `k + 1 > n`; `⨅` over an empty index type is `0` in `ℝ`, which is the convention
`orderStat` inherits.  Every statement about the value therefore either supplies a witness
subset or is proved separately in the empty case.

## Tags

order statistic, rank, sort, Lipschitz, min-max
-/

namespace Shields

/-- The greatest entry of `x` on a `(k+1)`-element subset of the index set. -/
noncomputable def subsetMax {n k : ℕ} (x : Fin n → ℝ)
    (S : {S : Finset (Fin n) // S.card = k + 1}) : ℝ :=
  (S : Finset (Fin n)).sup' (Finset.card_pos.mp (by rw [S.2]; omega)) x

/-- The `k`-th order statistic of a finite family of reals, in min–max form: the least,
over the `(k+1)`-element subsets of the index set, of the greatest entry on the subset.
For `k + 1 > n` there is no such subset and the value is `0`.

`orderStat_of_monotone` identifies this with the `k`-th entry of an already ordered family.
The min–max form is the one used here, because in it the Lipschitz bound is a two-line
monotonicity argument. -/
noncomputable def orderStat {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ⨅ S : {S : Finset (Fin n) // S.card = k + 1}, subsetMax x S

theorem bddBelow_range_subsetMax {n k : ℕ} (x : Fin n → ℝ) :
    BddBelow (Set.range (subsetMax (k := k) x)) :=
  (Set.finite_range _).bddBelow

theorem orderStat_le_subsetMax {n k : ℕ} (x : Fin n → ℝ)
    (S : {S : Finset (Fin n) // S.card = k + 1}) : orderStat k x ≤ subsetMax x S :=
  ciInf_le (bddBelow_range_subsetMax x) S

theorem subsetMax_le_add {n k : ℕ} {x y : Fin n → ℝ} {ε : ℝ} (h : ∀ i, x i ≤ y i + ε)
    (S : {S : Finset (Fin n) // S.card = k + 1}) : subsetMax x S ≤ subsetMax y S + ε := by
  refine Finset.sup'_le _ _ fun i hi => ?_
  have hle : y i ≤ subsetMax y S := Finset.le_sup' y hi
  linarith [h i]

theorem orderStat_le_add {n k : ℕ} {x y : Fin n → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, x i ≤ y i + ε) : orderStat k x ≤ orderStat k y + ε := by
  rcases isEmpty_or_nonempty {S : Finset (Fin n) // S.card = k + 1} with _ | _
  · simpa [orderStat] using hε
  · have key : ∀ S : {S : Finset (Fin n) // S.card = k + 1},
        orderStat k x - ε ≤ subsetMax y S := fun S => by
      have h1 := orderStat_le_subsetMax x S
      have h2 := subsetMax_le_add h S
      linarith
    have : orderStat k x - ε ≤ orderStat k y := le_ciInf key
    linarith

/-- **The `k`-th order statistic moves by at most the sup-norm displacement of the family.**
This is the sorting half of the statement that ordering a continuously varying finite family
keeps each ordered entry continuous. -/
theorem abs_orderStat_sub_le {n k : ℕ} {x y : Fin n → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, |x i - y i| ≤ ε) : |orderStat k x - orderStat k y| ≤ ε := by
  have h1 : orderStat k x ≤ orderStat k y + ε :=
    orderStat_le_add hε fun i => by obtain ⟨hl, hr⟩ := abs_le.mp (h i); linarith
  have h2 : orderStat k y ≤ orderStat k x + ε :=
    orderStat_le_add hε fun i => by
      obtain ⟨hl, hr⟩ := abs_le.mp (h i); linarith
  rw [abs_le]
  constructor <;> linarith

theorem lipschitzWith_orderStat {n k : ℕ} : LipschitzWith 1 (orderStat (n := n) k) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  exact abs_orderStat_sub_le dist_nonneg fun i => by
    simpa [Real.dist_eq] using dist_le_pi_dist x y i

/-- Sorting a continuously varying finite family of reals keeps every ordered entry
continuous. -/
theorem continuous_orderStat {n k : ℕ} : Continuous (orderStat (n := n) k) :=
  lipschitzWith_orderStat.continuous

/-- `orderStat` deserves its name: on an already ordered family the `k`-th order
statistic is the `k`-th entry.  With `abs_orderStat_sub_le` this says that the entries of a
continuously varying family, sorted into increasing order, vary continuously. -/
theorem orderStat_of_monotone {n k : ℕ} (hk : k + 1 ≤ n) {x : Fin n → ℝ}
    (hmono : Monotone x) : orderStat k x = x ⟨k, hk⟩ := by
  have hseg : ∀ m ∈ Finset.range (k + 1), m < n := fun _ hm =>
    lt_of_lt_of_le (Finset.mem_range.mp hm) hk
  have hcard : ((Finset.range (k + 1)).attachFin hseg).card = k + 1 := by
    rw [Finset.card_attachFin, Finset.card_range]
  haveI : Nonempty {S : Finset (Fin n) // S.card = k + 1} := ⟨⟨_, hcard⟩⟩
  refine le_antisymm ?_ ?_
  · refine (orderStat_le_subsetMax x ⟨_, hcard⟩).trans ?_
    refine Finset.sup'_le _ _ fun i hi => ?_
    rw [Finset.mem_attachFin, Finset.mem_range] at hi
    exact hmono (Fin.le_def.mpr (show (i : ℕ) ≤ k by omega))
  · have key : ∀ S : {S : Finset (Fin n) // S.card = k + 1}, x ⟨k, hk⟩ ≤ subsetMax x S := by
      intro S
      obtain ⟨i, hiS, hik⟩ : ∃ i ∈ (S : Finset (Fin n)), k ≤ (i : ℕ) := by
        by_contra hcon
        push Not at hcon
        have hlt : ∀ m ∈ Finset.range k, m < n := fun _ hm =>
          lt_of_lt_of_le (Finset.mem_range.mp hm) (by omega)
        have hsub : (S : Finset (Fin n)) ⊆ (Finset.range k).attachFin hlt := fun i hi =>
          (Finset.mem_attachFin _).mpr (Finset.mem_range.mpr (hcon i hi))
        have hcle := Finset.card_le_card hsub
        rw [S.2, Finset.card_attachFin, Finset.card_range] at hcle
        omega
      have h1 : x ⟨k, hk⟩ ≤ x i := hmono (Fin.le_def.mpr hik)
      have h2 : x i ≤ subsetMax x S := Finset.le_sup' x hiS
      linarith
    exact le_ciInf key

/-! ### The order statistic pinned by the counts around a value -/

theorem orderStat_le_of_card_le {n k : ℕ} (x : Fin n → ℝ) {τ : ℝ}
    (h : k + 1 ≤ (Finset.univ.filter fun i => x i ≤ τ).card) : orderStat k x ≤ τ := by
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (s := Finset.univ.filter fun i => x i ≤ τ) (n := k + 1) h
  refine le_trans (orderStat_le_subsetMax x ⟨S, hScard⟩) ?_
  refine Finset.sup'_le _ _ fun i hi => ?_
  exact (Finset.mem_filter.mp (hSsub hi)).2

theorem le_orderStat_of_card_le {n k : ℕ} (x : Fin n → ℝ) {τ : ℝ}
    [Nonempty {S : Finset (Fin n) // S.card = k + 1}]
    (h : (Finset.univ.filter fun i => x i < τ).card ≤ k) : τ ≤ orderStat k x := by
  refine le_ciInf fun S => ?_
  obtain ⟨i, hiS, hi⟩ : ∃ i ∈ (S : Finset (Fin n)), ¬ x i < τ := by
    by_contra hcon
    push Not at hcon
    have hsub : (S : Finset (Fin n)) ⊆ Finset.univ.filter fun i => x i < τ := fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon i hi⟩
    have := Finset.card_le_card hsub
    rw [S.2] at this
    omega
  exact le_trans (not_lt.mp hi) (Finset.le_sup' x hiS)

/-- **The order statistic, characterized by the two counts around a value.**  If at most `k`
entries lie strictly below `τ` and at least `k+1` lie weakly below it, then the `k`-th smallest
entry is `τ`. -/
theorem orderStat_eq_of_card {n k : ℕ} (x : Fin n → ℝ) {τ : ℝ}
    (hlt : (Finset.univ.filter fun i => x i < τ).card ≤ k)
    (hle : k + 1 ≤ (Finset.univ.filter fun i => x i ≤ τ).card) : orderStat k x = τ := by
  obtain ⟨S, -, hScard⟩ :=
    Finset.exists_subset_card_eq (s := Finset.univ.filter fun i => x i ≤ τ) (n := k + 1) hle
  haveI : Nonempty {S : Finset (Fin n) // S.card = k + 1} := ⟨⟨S, hScard⟩⟩
  exact le_antisymm (orderStat_le_of_card_le x hle) (le_orderStat_of_card_le x hlt)

theorem card_filter_le_eq_add {n : ℕ} (x : Fin n → ℝ) (τ : ℝ) :
    (Finset.univ.filter fun i => x i ≤ τ).card
      = (Finset.univ.filter fun i => x i < τ).card
        + (Finset.univ.filter fun i => x i = τ).card := by
  have hdisj : Disjoint (Finset.univ.filter fun i => x i < τ)
      (Finset.univ.filter fun i => x i = τ) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_filter] at hi hi'
    exact absurd hi'.2 (ne_of_lt hi.2)
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext i
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_iff_lt_or_eq

/-- **The coalescence of two entries at a value.**  With exactly `m` entries strictly below
`τ` and at least two equal to it, the family in increasing order carries `τ` in the two
consecutive positions `m` and `m + 1`, i.e. at one-based ranks `m + 1` and `m + 2`. -/
theorem orderStat_pair_eq_of_coalescence {n : ℕ} (x : Fin n → ℝ) {m : ℕ} {τ : ℝ}
    (hbelow : (Finset.univ.filter fun i => x i < τ).card = m)
    (hcirc : 2 ≤ (Finset.univ.filter fun i => x i = τ).card) :
    orderStat m x = τ ∧ orderStat (m + 1) x = τ := by
  have hle : m + 2 ≤ (Finset.univ.filter fun i => x i ≤ τ).card := by
    rw [card_filter_le_eq_add, hbelow]
    omega
  exact ⟨orderStat_eq_of_card x (by omega) (by omega),
    orderStat_eq_of_card x (by omega) (by omega)⟩

end Shields
