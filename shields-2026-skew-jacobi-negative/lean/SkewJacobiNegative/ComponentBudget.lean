import SkewJacobiNegative.ComponentCuts
import SkewJacobiNegative.NegativeRealizability
import SkewJacobiNegative.PositiveBorders

/-!
# Maximal-cofactor budgets and above-minimum borders

The actual connected components of the maximal cofactor give the budget in
`lem:component-budget`.  Removing the first row and last column retains the
negative mask, and the exact realizability inequalities decide the child's
connectedness in `lem:above-minimum-border`.  Endpoint extensions preserve
negative positions, including in boards with common row and column betas.
-/

namespace SkewJacobiNegative

open Finset

namespace BetaDiagram

variable {n : ℕ}

/-- The first row has no negative or zero entries. -/
theorem first_row_positive (D : BetaDiagram (n + 1)) (j : Fin (n + 1)) :
    D.col j < D.row 0 := by
  have hc := D.col_strictAnti.antitone (Fin.zero_le j)
  have hd := D.row_nonempty 0
  omega

/-- The last column has no negative or zero entries. -/
theorem last_column_positive (D : BetaDiagram (n + 1)) (i : Fin (n + 1)) :
    D.col (Fin.last n) < D.row i := by
  have hr := D.row_strictAnti.antitone (Fin.le_last i)
  have hd := D.row_nonempty (Fin.last n)
  omega

/-- The deleted first row contributes no negatives. -/
theorem negativeRowCount_zero (D : BetaDiagram (n + 1)) :
    negativeRowCount D 0 = 0 := by
  classical
  have h : ∀ j, ¬ D.row 0 < D.col j :=
    fun j => not_lt_of_ge (D.first_row_positive j).le
  simp [negativeRowCount, h]

/-- Each retained row has exactly the same number of negative sites. -/
theorem corner_negativeRowCount (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner)
    (i : Fin n) :
    negativeRowCount (D.cornerDiagram hP) i = negativeRowCount D i.succ := by
  classical
  have h : ¬ D.row i.succ < D.col (Fin.last n) :=
    not_lt_of_ge (D.last_column_positive i.succ).le
  simp only [negativeRowCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [h, if_false, add_zero]
  rfl

/-- The retained negative positions are precisely the original positions at
successor rows and all but the last column. -/
theorem corner_negative_iff (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner)
    (i j : Fin n) :
    (D.cornerDiagram hP).row i < (D.cornerDiagram hP).col j ↔
      D.row i.succ < D.col j.castSucc := Iff.rfl

/-- Deleting boundary entries cannot introduce a common row and column beta. -/
theorem corner_zeroFree (D : BetaDiagram (n + 1)) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) : (D.cornerDiagram hP).ZeroFree :=
  fun i j => hZ i.succ j.castSucc

/-- Removing the first row and last column removes no negative cells. -/
theorem corner_negativeCount (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner) :
    negativeCount (D.cornerDiagram hP) = negativeCount D := by
  rw [(D.cornerDiagram hP).negativeCount_eq_sum, D.negativeCount_eq_sum,
    Fin.sum_univ_succ, D.negativeRowCount_zero, zero_add]
  exact Finset.sum_congr rfl (fun i _ => D.corner_negativeRowCount hP i)

/-- The maximal cofactor keeps the entire actual negative partition. -/
theorem corner_negativePartition (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner) :
    negativePartition (D.cornerDiagram hP) = negativePartition D := by
  have hlist : List.ofFn (negativeRowCount D) =
      0 :: List.ofFn (negativeRowCount (D.cornerDiagram hP)) := by
    rw [List.ofFn_succ, D.negativeRowCount_zero]
    congr 1
    congr 1
    funext i
    exact (D.corner_negativeRowCount hP i).symm
  unfold negativePartition negativePaddedPartition
  rw [hlist]
  simp

/-- A positive border adds only a positive first row and last column. -/
theorem positiveBorder_negativePartition (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    negativePartition (D.positiveBorder u v hu hv) = negativePartition D := by
  have h := (D.positiveBorder u v hu hv).corner_negativePartition
    (D.positiveBorder_positiveCorner u v hu hv)
  rw [D.positiveBorder_cornerDiagram u v hu hv] at h
  exact h.symm

/-- The actual mask identifies connectedness, not just a necessary numerical bound. -/
theorem connected_iff_negativeRowCount_bound (D : BetaDiagram n) :
    D.Connected ↔ 0 < n ∧ ∀ i : Fin n, negativeRowCount D i ≤ i.val - 1 := by
  constructor
  · intro hD
    exact ⟨hD.1, D.connected_negativeRowCount_le hD⟩
  · rintro ⟨hn, hcounts⟩
    refine ⟨hn, ?_⟩
    intro i hi
    have hc := hcounts (⟨i.val + 1, hi⟩ : Fin n)
    have hn : ¬ D.row ⟨i.val + 1, hi⟩ < D.col i := by
      rw [D.negative_iff_lt_rowCount]
      simp only [Fin.val_mk] at hc
      omega
    exact le_of_not_gt hn

/-- The realizability inequalities also characterize the connectedness of an
already given actual diagram, via its own negative mask. -/
theorem connected_iff_negativePartition_admissible (D : BetaDiagram n) :
    D.Connected ↔ NegativeRowsAdmissible (negativePartition D) n := by
  constructor
  · exact D.connected_negativePartition_admissible
  · intro had
    apply D.connected_iff_negativeRowCount_bound.mpr
    refine ⟨had.1, ?_⟩
    intro i
    by_cases hz : negativeRowCount D i = 0
    · simp [hz]
    · have hp : 0 < negativeRowCount D i := Nat.pos_of_ne_zero hz
      have he : (negativePartition D).getD i.rev.val 0 = negativeRowCount D i := by
        rw [D.negativePartition_getD]
        simp only [dite_eq_left i.rev.isLt, Fin.eta, Fin.rev_rev]
      have hk : i.rev.val < (negativePartition D).length := by
        by_contra hk
        rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hk)] at he
        omega
      have hb := had.2 i.rev.val hk
      rw [he] at hb
      have hv : i.rev.val = n - 1 - i.val := by simp [Fin.rev]; omega
      rw [hv] at hb
      have hi := i.isLt
      omega

/-- Connectedness is determined by the exact minimum of the actual partition. -/
theorem connected_iff_minimumRealizingRows_le (D : BetaDiagram n) :
    D.Connected ↔ minimumRealizingRows (negativePartition D) ≤ n := by
  rw [minimumRealizingRows_le_iff]
  exact D.connected_iff_negativePartition_admissible

/-- The corner is connected exactly above the minimum realizing parent order. -/
theorem corner_connected_iff_above_minimum (D : BetaDiagram (n + 1))
    (hP : D.PositiveCorner) :
    (D.cornerDiagram hP).Connected ↔
      minimumRealizingRows (negativePartition D) < n + 1 := by
  rw [(D.cornerDiagram hP).connected_iff_minimumRealizingRows_le,
    D.corner_negativePartition hP]
  omega

/-- At the minimum parent order, and only there, its positive-row child disconnects. -/
theorem corner_disconnected_iff_minimum (D : BetaDiagram (n + 1))
    (hC : D.Connected) (hP : D.PositiveCorner) :
    ¬ (D.cornerDiagram hP).Connected ↔
      n + 1 = minimumRealizingRows (negativePartition D) := by
  have hb := D.connected_iff_minimumRealizingRows_le.mp hC
  rw [D.corner_connected_iff_above_minimum hP]
  omega

/-- The source statement for the actual zero-free maximal cofactor:
positive corner rows, unchanged negatives, and the exact connectedness threshold
are all produced from the source's ordinary geometric hypotheses. -/
theorem above_minimum_border (D : BetaDiagram (n + 1))
    (hC : D.Connected) (hZ : D.ZeroFree) :
    let R := D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hC hZ)
    negativePartition R = negativePartition D ∧
      (R.Connected ↔ minimumRealizingRows (negativePartition D) < n + 1) ∧
      (¬ R.Connected ↔ n + 1 = minimumRealizingRows (negativePartition D)) := by
  dsimp only
  exact ⟨D.corner_negativePartition _, D.corner_connected_iff_above_minimum _,
    D.corner_disconnected_iff_minimum hC _⟩

/-- Equal actual negative masks have equal actual partitions. -/
theorem negativePartition_eq_of_mask_eq (D E : BetaDiagram n)
    (hmask : ∀ i j, D.row i < D.col j ↔ E.row i < E.col j) :
    negativePartition D = negativePartition E := by
  have hc : negativeRowCount D = negativeRowCount E := by
    funext i
    unfold negativeRowCount
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmask i j
  simp only [negativePartition, negativePaddedPartition, hc]

/-- Increasing the first row changes no negative position. -/
theorem extendTop_negative_iff (D : BetaDiagram (n + 1))
    (d : ℤ) (hd : 0 < d) (i j : Fin (n + 1)) :
    (D.extendTop d hd).row i < (D.extendTop d hd).col j ↔ D.row i < D.col j := by
  change (if i = 0 then D.row i + d else D.row i) < D.col j ↔ _
  by_cases hi : i = 0
  · subst i
    have h := D.first_row_positive j
    simp only [ite_true]
    omega
  · simp [hi]

/-- Decreasing the last column changes no negative position. -/
theorem extendBottom_negative_iff (D : BetaDiagram (n + 1))
    (d : ℤ) (hd : 0 < d) (i j : Fin (n + 1)) :
    (D.extendBottom d hd).row i < (D.extendBottom d hd).col j ↔ D.row i < D.col j := by
  change D.row i < (if j = Fin.last n then D.col j - d else D.col j) ↔ _
  by_cases hj : j = Fin.last n
  · subst j
    have h := D.last_column_positive i
    simp only [ite_true]
    omega
  · simp [hj]

/-- Positive top endpoint extensions preserve the negative partition. -/
theorem extendTop_negativePartition (D : BetaDiagram (n + 1))
    (d : ℤ) (hd : 0 < d) :
    negativePartition (D.extendTop d hd) = negativePartition D :=
  (D.extendTop d hd).negativePartition_eq_of_mask_eq D (D.extendTop_negative_iff d hd)

/-- Positive bottom endpoint extensions preserve the negative partition. -/
theorem extendBottom_negativePartition (D : BetaDiagram (n + 1))
    (d : ℤ) (hd : 0 < d) :
    negativePartition (D.extendBottom d hd) = negativePartition D :=
  (D.extendBottom d hd).negativePartition_eq_of_mask_eq D
    (D.extendBottom_negative_iff d hd)

/-- The printed component budget for the actual maximal cofactor.
The decomposition input consists solely of actual cuts and connected leaves. -/
theorem component_budget (D : BetaDiagram (n + 1))
    (hC : D.Connected) (hZ : D.ZeroFree)
    (C : ComponentDecomposition
      (D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hC hZ))) :
    negativeCount D = pairwiseRowProducts (C.components.map Sigma.fst) +
      (C.components.map (fun X => negativeCount X.2)).sum := by
  rw [← D.corner_negativeCount (D.positiveCorner_of_connected_zeroFree hC hZ)]
  exact C.negative_budget

/-- The maximal-cofactor components, their orders, their exact factorization,
and their negative budget are constructed, not assumed. -/
theorem exists_maximal_cofactor_components (D : BetaDiagram (n + 1))
    (hC : D.Connected) (hZ : D.ZeroFree) :
    ∃ cs : List (Σ k : ℕ, BetaDiagram k),
      (∀ X ∈ cs, X.2.Connected) ∧
      (cs.map Sigma.fst).sum = n ∧
      D.cornerPolynomial = (cs.map (fun X => X.2.schur)).prod ∧
      negativeCount D = pairwiseRowProducts (cs.map Sigma.fst) +
        (cs.map (fun X => negativeCount X.2)).sum := by
  let hP := D.positiveCorner_of_connected_zeroFree hC hZ
  let R := D.cornerDiagram hP
  let C := R.componentDecomposition
  refine ⟨C.components, C.components_connected, C.component_rows_sum, ?_, ?_⟩
  · rw [← D.cornerDiagram_schur hP]
    exact C.component_schur_product
  · exact D.component_budget hC hZ C

end BetaDiagram
end SkewJacobiNegative
