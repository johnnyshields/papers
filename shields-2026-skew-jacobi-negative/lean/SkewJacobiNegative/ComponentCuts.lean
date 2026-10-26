import SkewJacobiNegative.NegativeBoards
import SkewJacobiNegative.ConnectedIrreducibility


/-!
# Actual cuts and connected components

Geometric disconnected cuts and their negative-cell budgets for
`lem:component-budget` of `shields-2026-skew-jacobi-negative.tex`.
A decomposition is a tree of literal restrictions at genuine cuts; its
leaves are connected diagrams, not prescribed polynomial factors.
-/

namespace SkewJacobiNegative

open Finset

namespace BetaDiagram

variable {n : ℕ}

/-- Every cell strictly below a genuine component cut is negative. -/
theorem cut_lowerLeft_negative {a b : ℕ} (D : BetaDiagram (a + b))
    (ha : 0 < a) (hb : 0 < b)
    (hcut : D.row ⟨a, by omega⟩ < D.col ⟨a - 1, by omega⟩)
    (i : Fin b) (j : Fin a) : D.row (i.natAdd a) < D.col (j.castAdd b) := by
  have hr := D.row_strictAnti.antitone
    (show (⟨a, by omega⟩ : Fin (a + b)) ≤ i.natAdd a by
      change a ≤ a + i.val; omega)
  have hc := D.col_strictAnti.antitone
    (show j.castAdd b ≤ (⟨a - 1, by omega⟩ : Fin (a + b)) by
      change j.val ≤ a - 1; omega)
  omega

/-- Every cell above a component cut is strictly positive, even without the cut hypothesis. -/
theorem cut_upperRight_positive {a b : ℕ} (D : BetaDiagram (a + b))
    (i : Fin a) (j : Fin b) : D.col (j.natAdd a) < D.row (i.castAdd b) := by
  have hc := D.col_strictAnti
    (show i.castAdd b < j.natAdd a by
      change i.val < a + j.val; omega)
  have hd := D.row_nonempty (i.castAdd b)
  omega

/-- The count can be read cell by cell, with zero indices contributing zero. -/
theorem negativeCount_eq_cell_sum (D : BetaDiagram n) :
    negativeCount D = ∑ i : Fin n, ∑ j : Fin n,
      if D.row i < D.col j then (1 : ℕ) else 0 := by
  classical
  rw [D.negativeCount_eq_sum]
  simp only [negativeRowCount, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- A genuine cut contributes exactly its lower-left rectangle. -/
theorem negativeCount_at_cut {a b : ℕ} (D : BetaDiagram (a + b))
    (ha : 0 < a) (hb : 0 < b)
    (hcut : D.row ⟨a, by omega⟩ < D.col ⟨a - 1, by omega⟩) :
    negativeCount D = negativeCount D.betaPrefix + negativeCount D.suffix + a * b := by
  classical
  rw [D.negativeCount_eq_cell_sum, Fin.sum_univ_add]
  have htop : (∑ i : Fin a, ∑ j : Fin (a + b),
      if D.row (i.castAdd b) < D.col j then (1 : ℕ) else 0) =
      negativeCount D.betaPrefix := by
    simp_rw [Fin.sum_univ_add]
    have hz : ∀ (i : Fin a) (j : Fin b),
        ¬ D.row (i.castAdd b) < D.col (j.natAdd a) := by
      intro i j
      exact not_lt_of_ge (D.cut_upperRight_positive i j).le
    simp only [hz, if_false, Finset.sum_const_zero, add_zero]
    exact D.betaPrefix.negativeCount_eq_cell_sum.symm
  have hbottom : (∑ i : Fin b, ∑ j : Fin (a + b),
      if D.row (i.natAdd a) < D.col j then (1 : ℕ) else 0) =
      b * a + negativeCount D.suffix := by
    simp_rw [Fin.sum_univ_add]
    have hn : ∀ (i : Fin b) (j : Fin a),
        D.row (i.natAdd a) < D.col (j.castAdd b) :=
      D.cut_lowerLeft_negative ha hb hcut
    simp only [hn, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, Finset.sum_add_distrib]
    change b * a + (∑ i : Fin b, ∑ j : Fin b,
      if D.suffix.row i < D.suffix.col j then (1 : ℕ) else 0) =
        b * a + negativeCount D.suffix
    rw [← D.suffix.negativeCount_eq_cell_sum]
  rw [htop, hbottom, Nat.mul_comm b a]
  omega

/-- Equality of the order transports the actual negative count. -/
theorem reindexOrder_negativeCount {m : ℕ} (D : BetaDiagram n) (h : m = n) :
    negativeCount (D.reindexOrder h) = negativeCount D := by
  subst m
  rfl

/-- A recursive decomposition using only genuine geometric cuts.
The connected leaves are therefore the actual maximal connected components. -/
inductive ComponentDecomposition : {n : ℕ} → BetaDiagram n → Type
  | empty (D : BetaDiagram 0) : ComponentDecomposition D
  | connected {n : ℕ} (D : BetaDiagram n) (hD : D.Connected) :
      ComponentDecomposition D
  | cut {n a b : ℕ} (D : BetaDiagram n) (ha : 0 < a) (hb : 0 < b)
      (he : a + b = n)
      (hcut : (D.reindexOrder he).row ⟨a, by omega⟩ <
        (D.reindexOrder he).col ⟨a - 1, by omega⟩)
      (left : ComponentDecomposition (D.reindexOrder he).betaPrefix)
      (right : ComponentDecomposition (D.reindexOrder he).suffix) :
      ComponentDecomposition D

namespace ComponentDecomposition

/-- The connected beta-list leaves, in their original order. -/
def components {n : ℕ} {D : BetaDiagram n} (C : ComponentDecomposition D) :
    List (Σ k : ℕ, BetaDiagram k) :=
  match C with
  | .empty _ => []
  | .connected D _ => [⟨_, D⟩]
  | .cut _ _ _ _ _ left right => left.components ++ right.components

/-- All leaves have nonempty rows and are connected. -/
theorem components_connected {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) :
    ∀ X ∈ C.components, X.2.Connected := by
  induction C with
  | empty D => simp [components]
  | connected D hD => simpa [components] using hD
  | cut D ha hb he hcut left right ihl ihr =>
    intro X hX
    rcases List.mem_append.mp hX with hX | hX
    · exact ihl X hX
    · exact ihr X hX

/-- No component is a zero-row or constant-factor surrogate. -/
theorem component_order_pos {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) (X : Σ k : ℕ, BetaDiagram k)
    (hX : X ∈ C.components) : 0 < X.1 :=
  (C.components_connected X hX).1

/-- The actual component orders exhaust the parent's rows. -/
theorem component_rows_sum {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) : (C.components.map Sigma.fst).sum = n := by
  induction C with
  | empty D => simp [components]
  | connected D hD => simp [components]
  | cut D ha hb he hcut left right ihl ihr =>
    simp only [components, List.map_append, List.sum_append, ihl, ihr]
    exact he

/-- The genuine component determinants multiply to the actual determinant. -/
theorem component_schur_product {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) :
    D.schur = (C.components.map (fun X => X.2.schur)).prod := by
  induction C with
  | empty D => simp [components, schur, Matrix.det_isEmpty]
  | connected D hD => simp [components]
  | cut D ha hb he hcut left right ihl ihr =>
    rw [components, List.map_append, List.prod_append, ← ihl, ← ihr,
      ← (D.reindexOrder he).schur_factor_at_cut ha hb hcut,
      D.reindexOrder_schur he]

/-- Every component factor is nonzero and nonunit. -/
theorem component_factor_nontrivial {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) (X : Σ k : ℕ, BetaDiagram k)
    (hX : X ∈ C.components) : X.2.schur ≠ 0 ∧ ¬ IsUnit X.2.schur :=
  ⟨X.2.schur_ne_zero, X.2.schur_not_isUnit (C.component_order_pos X hX)⟩

end ComponentDecomposition

/-- Every diagram admits an actual recursive decomposition at its cuts. -/
theorem exists_componentDecomposition (D : BetaDiagram n) :
    Nonempty (ComponentDecomposition D) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      exact ⟨.empty D⟩
    have hn : 0 < n := Nat.pos_of_ne_zero hz
    by_cases hD : D.Connected
    · exact ⟨.connected D hD⟩
    · have hbad : ¬ ∀ i : Fin n, ∀ hi : i.val + 1 < n,
          D.col i ≤ D.row ⟨i.val + 1, hi⟩ := by
        intro hc
        exact hD ⟨hn, hc⟩
      push Not at hbad
      obtain ⟨i, hi, hcut⟩ := hbad
      let a := i.val + 1
      let b := n - a
      have ha : 0 < a := by dsimp [a]; omega
      have hb : 0 < b := by dsimp [a, b]; omega
      have he : a + b = n := by dsimp [a, b]; omega
      let E : BetaDiagram (a + b) := D.reindexOrder he
      have hcutE : E.row ⟨a, by omega⟩ < E.col ⟨a - 1, by omega⟩ := by
        have hr : Fin.cast he (⟨a, by omega⟩ : Fin (a + b)) =
            ⟨i.val + 1, hi⟩ := by apply Fin.ext; rfl
        have hc : Fin.cast he (⟨a - 1, by omega⟩ : Fin (a + b)) = i := by
          apply Fin.ext
          change i.val + 1 - 1 = i.val
          omega
        change D.row (Fin.cast he _) < D.col (Fin.cast he _)
        rw [hr, hc]
        exact hcut
      obtain ⟨left⟩ := ih a (by omega) E.betaPrefix
      obtain ⟨right⟩ := ih b (by omega) E.suffix
      exact ⟨.cut D ha hb he hcutE left right⟩

/-- A producer, with no count or factorization conclusions as inputs. -/
noncomputable def componentDecomposition (D : BetaDiagram n) :
    ComponentDecomposition D := Classical.choice D.exists_componentDecomposition

end BetaDiagram

/-- The sum of `nᵢ nⱼ` for every ordered pair of distinct component positions `i < j`. -/
def pairwiseRowProducts : List ℕ → ℕ
  | [] => 0
  | a :: ns => a * ns.sum + pairwiseRowProducts ns

@[simp] theorem pairwiseRowProducts_nil : pairwiseRowProducts [] = 0 := rfl

@[simp] theorem pairwiseRowProducts_cons (a : ℕ) (ns : List ℕ) :
    pairwiseRowProducts (a :: ns) = a * ns.sum + pairwiseRowProducts ns := rfl

/-- Splitting the ordered components separates internal pairs and cross pairs. -/
theorem pairwiseRowProducts_append (xs ys : List ℕ) :
    pairwiseRowProducts (xs ++ ys) =
      pairwiseRowProducts xs + pairwiseRowProducts ys + xs.sum * ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, pairwiseRowProducts_cons, List.sum_append,
      List.sum_cons, ih]
    ring

namespace BetaDiagram.ComponentDecomposition

/-- The exact negative budget of the actual geometric components. -/
theorem negative_budget {n : ℕ} {D : BetaDiagram n}
    (C : ComponentDecomposition D) :
    negativeCount D = pairwiseRowProducts (C.components.map Sigma.fst) +
      (C.components.map (fun X => negativeCount X.2)).sum := by
  induction C with
  | empty D => simp [components, negativeCount, negativeSites]
  | connected D hD => simp [components]
  | cut D ha hb he hcut left right ihl ihr =>
    have hcount := (D.reindexOrder he).negativeCount_at_cut ha hb hcut
    rw [D.reindexOrder_negativeCount he] at hcount
    rw [hcount, ihl, ihr]
    simp only [components, List.map_append, List.sum_append,
      pairwiseRowProducts_append, left.component_rows_sum, right.component_rows_sum]
    omega

end BetaDiagram.ComponentDecomposition
end SkewJacobiNegative
