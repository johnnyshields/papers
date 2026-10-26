import SkewJacobiNegative.ExteriorGaps
import Mathlib

/-!
# Negative Ferrers boards

Actual negative beta differences, their row counts, and rotation, for
`sec:boards` and `lem:negative-partition` of
`shields-2026-skew-jacobi-negative.tex`.  Zero beta differences are not negative.
-/

namespace SkewJacobiNegative

open Finset

variable {n : ℕ}

/-- The actual negative sites, with the original row and column ordering. -/
def negativeSites (D : BetaDiagram n) : Finset (Fin n × Fin n) :=
  univ.filter fun p => D.row p.1 < D.col p.2

/-- Number of genuinely negative matrix indices. -/
def negativeCount (D : BetaDiagram n) : ℕ := (negativeSites D).card

/-- Number of negative columns in an actual row. -/
def negativeRowCount (D : BetaDiagram n) (i : Fin n) : ℕ :=
  (univ.filter fun j => D.row i < D.col j).card

/-- Bottom-to-top counts, retaining the zero padding. -/
def negativePaddedPartition (D : BetaDiagram n) : List ℕ :=
  (List.ofFn (negativeRowCount D)).reverse

/-- The negative partition, with its zero parts removed. -/
def negativePartition (D : BetaDiagram n) : List ℕ :=
  (negativePaddedPartition D).filter fun r => r ≠ 0

/-- Ordinary finite partitions, including the empty partition. -/
def IsNegativePartition (ρ : List ℕ) : Prop :=
  ρ.Pairwise (· ≥ ·) ∧ ∀ r ∈ ρ, 0 < r

/-- The usual conjugacy equation: part `k` counts parts larger than `k`. -/
def PartitionsConjugate (ρ σ : List ℕ) : Prop :=
  ∀ k : ℕ, ρ.getD k 0 = (σ.filter fun r => k < r).length

namespace NegativePartitionTools

/-- Removing terminal zero parts preserves the zero-extended sequence. -/
theorem trim_getD (l : List ℕ) (h : l.Pairwise (· ≥ ·)) (k : ℕ) :
    (l.filter fun r => r ≠ 0).getD k 0 = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
    by_cases hz : a = 0
    · subst a
      have hall : ∀ b ∈ l, b = 0 := by
        intro b hb
        have := ha b hb
        omega
      have hf : l.filter (fun r => decide (r ≠ 0)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        simp [hall b hb]
      have hd : ∀ t, l.getD t 0 = 0 := by
        intro t
        by_cases ht : t < l.length
        · rw [List.getD_eq_getElem _ _ ht]
          exact hall _ (List.getElem_mem ht)
        · simp [List.getD_eq_default, Nat.le_of_not_gt ht]
      rw [List.filter_cons_of_neg (p := fun r : ℕ => decide (r ≠ 0))
        (a := 0) (by simp), hf]
      cases k with
      | zero => simp
      | succ k =>
        change 0 = l.getD k 0
        exact (hd k).symm
    · cases k with
      | zero => simp [hz]
      | succ k => simpa [hz, -decide_not] using ih hl k

/-- Zero deletion does not change area. -/
theorem trim_sum (l : List ℕ) :
    (l.filter fun r => r ≠ 0).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons]
    by_cases h : a ≠ 0
    · rw [if_pos (show decide (a ≠ 0) = true from decide_eq_true h),
        List.sum_cons, List.sum_cons, ih]
    · have hz : a = 0 := not_ne_iff.mp h
      rw [if_neg (by simpa only [decide_eq_true_eq] using h), List.sum_cons, hz, zero_add]
      exact ih

/-- Threshold counts ignore the deleted zeros. -/
theorem trim_threshold (l : List ℕ) (k : ℕ) :
    ((l.filter fun r => r ≠ 0).filter fun r => k < r) =
      l.filter (fun r => k < r) := by
  rw [List.filter_filter]
  congr 1
  funext r
  by_cases h : k < r
  · have hz : r ≠ 0 := by omega
    simp [h, hz]
  · simp [h]

/-- A finite function read in reverse order. -/
theorem reverse_ofFn {α : Type*} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.rev]
    omega

/-- Filtering a finite function counts exactly its satisfying indices. -/
theorem length_filter_ofFn {α : Type*} (f : Fin n → α) (p : α → Prop)
    [DecidablePred p] :
    ((List.ofFn f).filter fun a => p a).length = (univ.filter fun i => p (f i)).card := by
  have hlist : ∀ l : List α, (l.filter fun a => p a).length =
      (l.map fun a => if p a then 1 else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => by_cases h : p a <;> simp [h, ih, Nat.add_comm]
  rw [hlist, ← List.ofFn_comp', List.sum_ofFn,
    Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Equality of zero-extended positive lists implies equality of the lists. -/
theorem ext_getD {l m : List ℕ} (hl : ∀ r ∈ l, 0 < r)
    (hm : ∀ r ∈ m, 0 < r) (h : ∀ k, l.getD k 0 = m.getD k 0) : l = m := by
  have hlen : l.length = m.length := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hp := hm (m[l.length]) (List.getElem_mem hn)
      have he := h l.length
      rw [List.getD_eq_default _ _ (le_refl _), List.getD_eq_getElem _ _ hn] at he
      omega
    · have hp := hl (l[m.length]) (List.getElem_mem hn)
      have he := h m.length
      rw [List.getD_eq_getElem _ _ hn, List.getD_eq_default _ _ (le_refl _)] at he
      omega
  apply List.ext_getElem hlen
  intro i hi hj
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using h i

end NegativePartitionTools

namespace BetaDiagram

@[simp] theorem mem_negativeSites (D : BetaDiagram n) (i j : Fin n) :
    (i, j) ∈ negativeSites D ↔ D.row i < D.col j := by
  simp [negativeSites]

/-- Exact southwest closure, `lem:negative-partition`. -/
theorem negative_southwest (D : BetaDiagram n) {i j i' j' : Fin n}
    (h : D.row i < D.col j) (hi : i ≤ i') (hj : j' ≤ j) :
    D.row i' < D.col j' :=
  lt_of_le_of_lt (D.row_strictAnti.antitone hi)
    (lt_of_lt_of_le h (D.col_strictAnti.antitone hj))

/-- Row counts increase downward. -/
theorem negativeRowCount_monotone (D : BetaDiagram n) : Monotone (negativeRowCount D) := by
  intro i i' hi
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact D.negative_southwest hj hi le_rfl

theorem negativeRowCount_le (D : BetaDiagram n) (i : Fin n) :
    negativeRowCount D i ≤ n := by
  simpa [negativeRowCount] using
    Finset.card_le_card (Finset.filter_subset (fun j => D.row i < D.col j) univ)

/-- A row is exactly the initial segment specified by its count. -/
theorem negative_iff_lt_rowCount (D : BetaDiagram n) (i j : Fin n) :
    D.row i < D.col j ↔ j.val < negativeRowCount D i := by
  constructor
  · intro h
    have hs : Finset.Iic j ⊆ (univ.filter fun k => D.row i < D.col k) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact D.negative_southwest h le_rfl (Finset.mem_Iic.mp hk)
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hc
  · intro h
    by_contra hn
    have hs : (univ.filter fun k => D.row i < D.col k) ⊆ Finset.Iio j := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      apply Finset.mem_Iio.mpr
      by_contra hkj
      exact hn (D.negative_southwest hk le_rfl (le_of_not_gt hkj))
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    exact Nat.not_lt_of_ge hc h

/-- The actual site count is the sum of actual row counts. -/
theorem negativeCount_eq_sum (D : BetaDiagram n) :
    negativeCount D = ∑ i : Fin n, negativeRowCount D i := by
  simp only [negativeCount, negativeSites, negativeRowCount,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]

/-- Connectedness excludes every first-subdiagonal negative. -/
theorem negative_lt_predecessor (D : BetaDiagram n) (hD : D.Connected)
    {i j : Fin n} (h : D.row i < D.col j) : j.val < i.val - 1 := by
  by_cases hi : i.val = 0
  · have hij : i ≤ j := by simpa only [Fin.le_def, hi] using Nat.zero_le j.val
    have hc := D.col_strictAnti.antitone hij
    have hd := D.row_nonempty i
    omega
  · let p : Fin n := ⟨i.val - 1, by omega⟩
    have hp : p.val + 1 < n := by dsimp [p]; omega
    have he : (⟨p.val + 1, hp⟩ : Fin n) = i := by
      apply Fin.ext
      dsimp [p]
      omega
    have hc := hD.2 p hp
    rw [he] at hc
    by_contra hj
    have hpj : p ≤ j := by simpa only [Fin.le_def] using Nat.le_of_not_gt hj
    have ha := D.col_strictAnti.antitone hpj
    omega

/-- Connected row bounds include the first two rows, both of count zero. -/
theorem connected_negativeRowCount_le (D : BetaDiagram n) (hD : D.Connected)
    (i : Fin n) : negativeRowCount D i ≤ i.val - 1 := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  have hs : (univ.filter fun j => D.row i < D.col j) ⊆ Finset.Iio p := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_Iio.mpr (D.negative_lt_predecessor hD hj)
  simpa [negativeRowCount, p] using Finset.card_le_card hs

/-- Bottom-to-top counts are nonincreasing. -/
theorem negativePaddedPartition_pairwise (D : BetaDiagram n) :
    (negativePaddedPartition D).Pairwise (· ≥ ·) := by
  rw [negativePaddedPartition, NegativePartitionTools.reverse_ofFn, List.pairwise_ofFn]
  intro i j hij
  apply D.negativeRowCount_monotone
  exact (Fin.rev_lt_rev.mpr hij).le

/-- The actual negative partition is an ordinary positive partition. -/
theorem negativePartition_isPartition (D : BetaDiagram n) :
    IsNegativePartition (negativePartition D) := by
  constructor
  · exact D.negativePaddedPartition_pairwise.filter _
  · intro r hr
    have h := (List.mem_filter.mp hr).2
    have hn : r ≠ 0 := of_decide_eq_true h
    exact Nat.pos_of_ne_zero hn

/-- Zero extension recovers every reversed row count. -/
theorem negativePartition_getD (D : BetaDiagram n) (k : ℕ) :
    (negativePartition D).getD k 0 =
      if hk : k < n then negativeRowCount D (Fin.rev ⟨k, hk⟩) else 0 := by
  rw [negativePartition,
    NegativePartitionTools.trim_getD _ D.negativePaddedPartition_pairwise,
    negativePaddedPartition, NegativePartitionTools.reverse_ofFn]
  split_ifs with hk
  · simp [List.getD_eq_getElem, hk]
  · exact List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hk)

/-- Area is exactly the negative-site count, `lem:negative-partition`. -/
theorem negativePartition_sum (D : BetaDiagram n) :
    (negativePartition D).sum = negativeCount D := by
  rw [negativePartition, NegativePartitionTools.trim_sum, negativePaddedPartition,
    List.sum_reverse, List.sum_ofFn, D.negativeCount_eq_sum]


/-- Rotation transposes the actual southwest mask in corner coordinates. -/
theorem rotate_negative_iff (D : BetaDiagram n) (i j : Fin n) :
    D.rotate.row i < D.rotate.col j ↔ D.row j.rev < D.col i.rev := by
  change -D.col i.rev < -D.row j.rev ↔ _
  omega

/-- Row `k` of the rotated Ferrers partition counts columns above height `k`. -/
theorem rotate_negativeRowCount (D : BetaDiagram n) (k : Fin n) :
    negativeRowCount D.rotate k.rev =
      ((negativePartition D).filter fun r => k.val < r).length := by
  rw [negativePartition, NegativePartitionTools.trim_threshold,
    negativePaddedPartition, NegativePartitionTools.reverse_ofFn,
    NegativePartitionTools.length_filter_ofFn]
  unfold negativeRowCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [D.rotate_negative_iff, Fin.rev_rev, D.negative_iff_lt_rowCount]
  rfl

/-- Actual rotation conjugates the partition, `lem:negative-partition`. -/
theorem rotate_partition_conjugate (D : BetaDiagram n) :
    PartitionsConjugate (negativePartition D.rotate) (negativePartition D) := by
  intro k
  rw [D.rotate.negativePartition_getD]
  split_ifs with hk
  · exact D.rotate_negativeRowCount ⟨k, hk⟩
  · symm
    apply List.length_eq_zero_iff.mpr
    apply List.filter_eq_nil_iff.mpr
    intro r hr
    obtain ⟨hr, _⟩ := List.mem_filter.mp hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by
      simpa [negativePaddedPartition, NegativePartitionTools.reverse_ofFn] using hr)
    have hc := D.negativeRowCount_le i.rev
    simp only [decide_eq_true_eq]
    omega

end BetaDiagram
end SkewJacobiNegative
