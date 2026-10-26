import SkewJacobiNegative.ComponentBudget
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Finite component orders forced by the negative budget

The arithmetic in `eq:threshold-budget-table` and `eq:ten-negative-budget`
follows from positivity of actual component orders and their exact cut budget.
The row bound is proved before the finite arithmetic enumeration.  Sorting
forgets only the order of the connected components, not their sizes.
-/

namespace SkewJacobiNegative
namespace ComponentOrderInventory

/-- The sum of positive orders dominates their number. -/
theorem length_le_sum (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a) :
    xs.length ≤ xs.sum := by
  revert hp
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro hp
    have ha := hp a (by simp)
    have ht := ih (fun b hb => hp b (by simp [hb]))
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem head_product_bound (a s k : ℕ) (ha : 0 < a) (hs : k ≤ s) :
    k * a + s ≤ a * s + k := by
  obtain ⟨u, rfl⟩ : ∃ u, a = u + 1 := Nat.exists_eq_add_of_le' ha
  obtain ⟨v, rfl⟩ : ∃ v, s = v + k := Nat.exists_eq_add_of_le' hs
  nlinarith [Nat.zero_le (u * v)]

/-- At least two positive components cost at least the total order minus one. -/
theorem sum_le_cross_add_one (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a)
    (hl : 2 ≤ xs.length) : xs.sum ≤ pairwiseRowProducts xs + 1 := by
  revert hp hl
  induction xs with
  | nil => intro hp hl; simp at hl
  | cons a xs ih =>
    intro hp hl
    have ha := hp a (by simp)
    have hp' : ∀ b ∈ xs, 0 < b := fun b hb => hp b (by simp [hb])
    cases xs with
    | nil => simp at hl
    | cons b ys =>
      cases ys with
      | nil =>
        have hb := hp' b (by simp)
        have h := head_product_bound a b 1 ha (by omega)
        simpa [pairwiseRowProducts] using h
      | cons c zs =>
        have ht := ih hp' (by simp)
        have hs : 1 ≤ (b :: c :: zs).sum :=
          (by have h := hp' b (by simp); simp only [List.sum_cons]; omega)
        have hm : a ≤ a * (b :: c :: zs).sum := by
          simpa using Nat.mul_le_mul_left a hs
        simp only [List.sum_cons, pairwiseRowProducts_cons] at *
        omega

/-- The disconnected-order bound has no finite-box or inventory premise. -/
theorem row_bound (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a)
    (hl : 2 ≤ xs.length) (budget : ℕ) (hb : pairwiseRowProducts xs ≤ budget) :
    xs.sum - 1 ≤ pairwiseRowProducts xs ∧ xs.sum ≤ budget + 1 := by
  have h := sum_le_cross_add_one xs hp hl
  omega

/-- Three positive components cost at least twice the total order minus three. -/
theorem three_component_bound (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a)
    (hl : 3 ≤ xs.length) : 2 * xs.sum ≤ pairwiseRowProducts xs + 3 := by
  cases xs with
  | nil => simp at hl
  | cons a xs =>
    have ha := hp a (by simp)
    have hp' : ∀ b ∈ xs, 0 < b := fun b hb => hp b (by simp [hb])
    have ht : 2 ≤ xs.length := by simp only [List.length_cons] at hl; omega
    have hs : 2 ≤ xs.sum := ht.trans (length_le_sum xs hp')
    have hc := sum_le_cross_add_one xs hp' ht
    have hm := head_product_bound a xs.sum 2 ha hs
    simp only [List.sum_cons, pairwiseRowProducts_cons]
    omega

/-- Four or more components already cost at least twelve negatives at order six. -/
theorem four_component_bound (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a)
    (hl : 4 ≤ xs.length) : 3 * xs.sum ≤ pairwiseRowProducts xs + 6 := by
  cases xs with
  | nil => simp at hl
  | cons a xs =>
    have ha := hp a (by simp)
    have hp' : ∀ b ∈ xs, 0 < b := fun b hb => hp b (by simp [hb])
    have ht : 3 ≤ xs.length := by simp only [List.length_cons] at hl; omega
    have hs : 3 ≤ xs.sum := ht.trans (length_le_sum xs hp')
    have hc := three_component_bound xs hp' ht
    have hm := head_product_bound a xs.sum 3 ha hs
    simp only [List.sum_cons, pairwiseRowProducts_cons]
    omega

/-- For budgets at most ten and total order at least six, there are at most three
components.  This is an unbounded arithmetic theorem. -/
theorem length_le_three (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a)
    (hm : 6 ≤ xs.sum) (hb : pairwiseRowProducts xs ≤ 10) : xs.length ≤ 3 := by
  by_contra h
  have hc := four_component_bound xs hp (by omega)
  omega

/-- Reordering components preserves every cross pair. -/
theorem cross_eq_of_perm {xs ys : List ℕ} (h : xs.Perm ys) :
    pairwiseRowProducts xs = pairwiseRowProducts ys := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    simp only [pairwiseRowProducts_cons, h.sum_eq, ih]
  | swap a b xs =>
    simp only [pairwiseRowProducts_cons, List.sum_cons]
    ring
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Each pair records a sorted component-order list and the remaining internal
capacity, not an assumed classification. -/
def tenPatterns : List (List ℕ × ℕ) :=
  [([1, 5], 5), ([2, 4], 2), ([3, 3], 1), ([1, 1, 4], 1),
   ([1, 6], 4), ([2, 5], 0), ([1, 7], 3), ([1, 8], 2),
   ([1, 9], 1), ([1, 10], 0)]

/-- The nine-negative table includes every order from six through ten. -/
def ninePatterns : List (List ℕ × ℕ) :=
  [([1, 5], 4), ([2, 4], 1), ([3, 3], 0), ([1, 1, 4], 0),
   ([1, 6], 3), ([1, 7], 2), ([1, 8], 1), ([1, 9], 0)]

set_option maxHeartbeats 2000000 in
/-- Exhaustive finite arithmetic, used only after deriving both row and length
bounds from positivity and cross cost. -/
theorem ten_inventory_sorted (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a)
    (hs : xs.Pairwise (· ≤ ·)) (hl : 2 ≤ xs.length) (hm : 6 ≤ xs.sum)
    (hb : pairwiseRowProducts xs ≤ 10) :
    (xs, 10 - pairwiseRowProducts xs) ∈ tenPatterns := by
  have hu := (row_bound xs hp hl 10 hb).2
  have hk := length_le_three xs hp hm hb
  cases xs with
  | nil => simp at hl
  | cons a xs =>
    cases xs with
    | nil => simp at hl
    | cons b xs =>
      cases xs with
      | nil =>
        have ha : 1 ≤ a := by have h := hp a (by simp); omega
        have hb' : 1 ≤ b := by have h := hp b (by simp); omega
        have hab : a ≤ b := (List.pairwise_cons.mp hs).1 b (by simp)
        have ha' : a ≤ 5 := by simp only [List.sum_cons, List.sum_nil] at hu; omega
        have hb'' : b ≤ 10 := by simp only [List.sum_cons, List.sum_nil] at hu; omega
        interval_cases a <;> interval_cases b <;>
          norm_num [tenPatterns, pairwiseRowProducts] at *
      | cons c xs =>
        have hz : xs.length = 0 := by simp only [List.length_cons] at hk; omega
        have he : xs = [] := List.length_eq_zero_iff.mp hz
        subst xs
        have ha : 1 ≤ a := by have h := hp a (by simp); omega
        have hb' : 1 ≤ b := by have h := hp b (by simp); omega
        have hc : 1 ≤ c := by have h := hp c (by simp); omega
        have hab : a ≤ b := (List.pairwise_cons.mp hs).1 b (by simp)
        have hbc : b ≤ c :=
          (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 c (by simp)
        have ha' : a ≤ 3 := by simp only [List.sum_cons, List.sum_nil] at hu; omega
        have hb'' : b ≤ 5 := by simp only [List.sum_cons, List.sum_nil] at hu; omega
        have hc' : c ≤ 9 := by simp only [List.sum_cons, List.sum_nil] at hu; omega
        interval_cases a <;> interval_cases b <;> interval_cases c <;>
          norm_num [tenPatterns, pairwiseRowProducts] at *

/-- The ordinary ordered list needs no sorting assumption. -/
theorem ten_inventory (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a)
    (hl : 2 ≤ xs.length) (hm : 6 ≤ xs.sum) (hb : pairwiseRowProducts xs ≤ 10) :
    (xs.insertionSort (· ≤ ·), 10 - pairwiseRowProducts xs) ∈ tenPatterns := by
  let ys := xs.insertionSort (· ≤ ·)
  have hperm : ys.Perm xs := List.perm_insertionSort (· ≤ ·) xs
  have hp' : ∀ a ∈ ys, 0 < a := fun a ha => hp a (hperm.mem_iff.mp ha)
  have hc := cross_eq_of_perm hperm
  have h := ten_inventory_sorted ys hp' (List.pairwise_insertionSort _ _)
    (by simpa only [hperm.length_eq] using hl)
    (by simpa only [hperm.sum_eq] using hm)
    (by simpa only [hc] using hb)
  simpa only [ys, hc] using h

/-- The smaller table is derived from the ten-budget inventory and the stronger
cross inequality, not from a separate component census. -/
theorem nine_inventory (xs : List ℕ) (hp : ∀ a ∈ xs, 0 < a)
    (hl : 2 ≤ xs.length) (hm : 6 ≤ xs.sum) (hb : pairwiseRowProducts xs ≤ 9) :
    (xs.insertionSort (· ≤ ·), 9 - pairwiseRowProducts xs) ∈ ninePatterns := by
  have ht := ten_inventory xs hp hl hm (by omega)
  have hpSort := List.perm_insertionSort (fun a b : ℕ => a ≤ b) xs
  have hc := cross_eq_of_perm hpSort
  simp only [tenPatterns, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨he, _⟩ <;>
    rw [he] at hc <;>
    norm_num [pairwiseRowProducts] at hc <;>
    simp [ninePatterns, he, ← hc] at *

/-- Membership is exact: every listed pattern has positive entries, at least
two components, total order at least six, and precisely the displayed capacity. -/
theorem ten_pattern_sound (xs : List ℕ) (cap : ℕ) (h : (xs, cap) ∈ tenPatterns) :
    (∀ a ∈ xs, 0 < a) ∧ 2 ≤ xs.length ∧ 6 ≤ xs.sum ∧
      pairwiseRowProducts xs ≤ 10 ∧ cap = 10 - pairwiseRowProducts xs := by
  simp only [tenPatterns, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> norm_num [pairwiseRowProducts]

theorem nine_pattern_sound (xs : List ℕ) (cap : ℕ) (h : (xs, cap) ∈ ninePatterns) :
    (∀ a ∈ xs, 0 < a) ∧ 2 ≤ xs.length ∧ 6 ≤ xs.sum ∧
      pairwiseRowProducts xs ≤ 9 ∧ cap = 9 - pairwiseRowProducts xs := by
  simp only [ninePatterns, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> norm_num [pairwiseRowProducts]

end ComponentOrderInventory

namespace BetaDiagram.ComponentDecomposition

/-- Positivity is supplied by the connected geometric leaves. -/
theorem orders_positive {n : ℕ} {D : BetaDiagram n} (C : ComponentDecomposition D) :
    ∀ a ∈ C.components.map Sigma.fst, 0 < a := by
  intro a ha
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp ha
  exact C.component_order_pos X hX

/-- A positive-order disconnected diagram has at least two actual leaves. -/
theorem disconnected_length_ge_two {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) (hn : 0 < n) (hD : ¬ D.Connected) :
    2 ≤ C.components.length := by
  cases C with
  | empty D => omega
  | connected D hC => exact False.elim (hD hC)
  | cut D ha hb he hcut left right =>
    have hl : left.components ≠ [] := by
      intro h
      have hs := left.component_rows_sum
      simp [h] at hs
      omega
    have hr : right.components ≠ [] := by
      intro h
      have hs := right.component_rows_sum
      simp [h] at hs
      omega
    have hl' := List.length_pos_of_ne_nil hl
    have hr' := List.length_pos_of_ne_nil hr
    simp only [components, List.length_append]
    omega

/-- Nonnegative internal counts and the exact actual cut budget yield the row
bound before any case classification. -/
theorem negative_budget_row_bound {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) (hn : 0 < n) (hD : ¬ D.Connected)
    (budget : ℕ) (hb : negativeCount D ≤ budget) :
    n - 1 ≤ pairwiseRowProducts (C.components.map Sigma.fst) ∧ n ≤ budget + 1 := by
  have he := C.negative_budget
  have hc : pairwiseRowProducts (C.components.map Sigma.fst) ≤ budget := by omega
  have hl : 2 ≤ (C.components.map Sigma.fst).length := by
    simpa using C.disconnected_length_ge_two hn hD
  simpa only [C.component_rows_sum] using
    ComponentOrderInventory.row_bound _ C.orders_positive hl budget hc

/-- The nine-negative threshold table, with actual remaining internal capacity. -/
theorem nine_negative_inventory {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) (hn : 6 ≤ n) (hD : ¬ D.Connected)
    (hb : negativeCount D ≤ 9) :
    ∃ cap, ((C.components.map Sigma.fst).insertionSort (· ≤ ·), cap) ∈
      ComponentOrderInventory.ninePatterns ∧
      (C.components.map (fun X => negativeCount X.2)).sum ≤ cap := by
  have he := C.negative_budget
  have hc : pairwiseRowProducts (C.components.map Sigma.fst) ≤ 9 := by omega
  have hl : 2 ≤ (C.components.map Sigma.fst).length := by
    simpa using C.disconnected_length_ge_two (by omega) hD
  have hm : 6 ≤ (C.components.map Sigma.fst).sum := by
    simpa only [C.component_rows_sum] using hn
  refine ⟨9 - pairwiseRowProducts (C.components.map Sigma.fst),
    ComponentOrderInventory.nine_inventory _ C.orders_positive hl hm hc, ?_⟩
  omega

/-- The ten-negative inventory includes the additional seven-row pattern
`[2, 5]` and every possible larger cofactor order, through eleven. -/
theorem ten_negative_inventory {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) (hn : 6 ≤ n) (hD : ¬ D.Connected)
    (hb : negativeCount D ≤ 10) :
    ∃ cap, ((C.components.map Sigma.fst).insertionSort (· ≤ ·), cap) ∈
      ComponentOrderInventory.tenPatterns ∧
      (C.components.map (fun X => negativeCount X.2)).sum ≤ cap := by
  have he := C.negative_budget
  have hc : pairwiseRowProducts (C.components.map Sigma.fst) ≤ 10 := by omega
  have hl : 2 ≤ (C.components.map Sigma.fst).length := by
    simpa using C.disconnected_length_ge_two (by omega) hD
  have hm : 6 ≤ (C.components.map Sigma.fst).sum := by
    simpa only [C.component_rows_sum] using hn
  refine ⟨10 - pairwiseRowProducts (C.components.map Sigma.fst),
    ComponentOrderInventory.ten_inventory _ C.orders_positive hl hm hc, ?_⟩
  omega

/-- At exactly ten negatives the displayed internal capacities are equalities. -/
theorem ten_negative_inventory_exact {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) (hn : 6 ≤ n) (hD : ¬ D.Connected)
    (hb : negativeCount D = 10) :
    ((C.components.map Sigma.fst).insertionSort (· ≤ ·),
      (C.components.map (fun X => negativeCount X.2)).sum) ∈
      ComponentOrderInventory.tenPatterns := by
  have he := C.negative_budget
  have hc : (C.components.map (fun X => negativeCount X.2)).sum =
      10 - pairwiseRowProducts (C.components.map Sigma.fst) := by omega
  obtain ⟨cap, hcap, _⟩ := C.ten_negative_inventory hn hD hb.le
  have hs := (ComponentOrderInventory.ten_pattern_sound _ _ hcap).2.2.2.2
  have hpSort := List.perm_insertionSort (fun a b : ℕ => a ≤ b)
    (C.components.map Sigma.fst)
  rw [ComponentOrderInventory.cross_eq_of_perm hpSort] at hs
  rw [hc, ← hs]
  exact hcap

end BetaDiagram.ComponentDecomposition

namespace BetaDiagram

/-- The threshold inventory is produced for the actual maximal cofactor at
minimum realizing order; no decomposition or arithmetic inventory is assumed. -/
theorem maximal_cofactor_nine_inventory {n : ℕ} (D : BetaDiagram (n + 1))
    (hC : D.Connected) (hZ : D.ZeroFree) (hn : 6 ≤ n)
    (hmin : n + 1 = minimumRealizingRows (negativePartition D))
    (hb : negativeCount D ≤ 9) :
    let R := D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hC hZ)
    ∃ cap, ((R.componentDecomposition.components.map Sigma.fst).insertionSort
      (· ≤ ·), cap) ∈ ComponentOrderInventory.ninePatterns ∧
      (R.componentDecomposition.components.map (fun X => negativeCount X.2)).sum ≤
        cap := by
  dsimp only
  apply ComponentDecomposition.nine_negative_inventory _ hn
  · exact (D.corner_disconnected_iff_minimum hC _).mpr hmin
  · rw [D.corner_negativeCount]
    exact hb

/-- At budget ten the actual cofactor has precisely the orders in the extended
table, including all higher-order cases; the sole row hypothesis is `6 ≤ n`. -/
theorem maximal_cofactor_ten_inventory {n : ℕ} (D : BetaDiagram (n + 1))
    (hC : D.Connected) (hZ : D.ZeroFree) (hn : 6 ≤ n)
    (hmin : n + 1 = minimumRealizingRows (negativePartition D))
    (hb : negativeCount D ≤ 10) :
    let R := D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hC hZ)
    ∃ cap, ((R.componentDecomposition.components.map Sigma.fst).insertionSort
      (· ≤ ·), cap) ∈ ComponentOrderInventory.tenPatterns ∧
      (R.componentDecomposition.components.map (fun X => negativeCount X.2)).sum ≤
        cap := by
  dsimp only
  apply ComponentDecomposition.ten_negative_inventory _ hn
  · exact (D.corner_disconnected_iff_minimum hC _).mpr hmin
  · rw [D.corner_negativeCount]
    exact hb

end BetaDiagram
end SkewJacobiNegative
