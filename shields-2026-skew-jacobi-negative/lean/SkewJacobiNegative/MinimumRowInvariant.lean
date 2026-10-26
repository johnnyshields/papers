import SkewJacobiNegative.NegativeInvariants
import SkewJacobiNegative.NegativeRealizability

/-!
# The least realizing row count as a Schur invariant

The earliest padded-overlap threshold, `prop:minimal-row-invariant` and
`eq:overlap-minimum` of `shields-2026-skew-jacobi-negative.tex`.
The partition itself is not asserted to be invariant.
-/

namespace SkewJacobiNegative
namespace BetaDiagram

open Finset
variable {n m : ℕ}

/-- An overlap order with at least one genuinely negative beta index. -/
def HasNegativeOverlap (D : BetaDiagram n) (k : ℕ) : Prop :=
  2 ≤ k ∧ ∃ v ∈ D.paddedRowOverlaps k, v ≤ k - 2

/-- The threshold tests exactly the actual cells on the corresponding subdiagonal. -/
theorem hasNegativeOverlap_iff (D : BetaDiagram n) (k : ℕ) :
    D.HasNegativeOverlap k ↔ ∃ i j : Fin n,
      D.row i < D.col j ∧ i.val + 1 = j.val + k := by
  classical
  constructor
  · rintro ⟨hk, v, hv, hsmall⟩
    change v ∈ (Finset.range (n - (k - 1))).val.map
      (D.toWeakRows.overlap (k - 1)) at hv
    obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hv
    have hj' : j < n - (k - 1) := Finset.mem_range.mp hj
    refine ⟨⟨j + (k - 1), by omega⟩, ⟨j, by omega⟩, ?_, by dsimp; omega⟩
    apply (D.overlap_negative_iff hk hj').mp
    simpa only [he] using hsmall
  · rintro ⟨i, j, hn, he⟩
    have hb := D.negative_below_diagonal hn
    have hk : 2 ≤ k := by omega
    have hj : j.val < n - (k - 1) := by have := i.isLt; omega
    have hi : j.val + (k - 1) = i.val := by omega
    refine ⟨hk, D.toWeakRows.overlap (k - 1) j.val, ?_, ?_⟩
    · change D.toWeakRows.overlap (k - 1) j.val ∈
        (Finset.range (n - (k - 1))).val.map (D.toWeakRows.overlap (k - 1))
      exact Multiset.mem_map.mpr ⟨j.val, Finset.mem_range.mpr hj, rfl⟩
    · apply (D.overlap_negative_iff hk hj).mpr
      simpa only [hi] using hn

/-- Zero deletion is empty exactly when every actual row count vanishes. -/
theorem negativePartition_ne_nil_iff (D : BetaDiagram n) :
    negativePartition D ≠ [] ↔ ∃ i j : Fin n, D.row i < D.col j := by
  constructor
  · intro hp
    by_contra hn
    have hc : ∀ i, negativeRowCount D i = 0 := by
      intro i
      unfold negativeRowCount
      have he : (univ.filter fun j => D.row i < D.col j) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact fun h => hn ⟨i, j, h⟩
      rw [he, Finset.card_empty]
    apply hp
    simp [negativePartition, negativePaddedPartition, hc]
  · rintro ⟨i, j, hn⟩ hp
    have hc := (D.negative_iff_lt_rowCount i j).mp hn
    have hg := D.negativePartition_getD i.rev.val
    have hi : i.rev.val < n := i.rev.isLt
    rw [hp] at hg
    have hz : 0 = negativeRowCount D i := by
      simpa only [List.getD_nil, dif_pos hi, Fin.eta, Fin.rev_rev] using hg
    omega

/-- Existence of an earliest overlap threshold has precisely the nonempty-pattern guard. -/
theorem exists_negativeOverlap_iff (D : BetaDiagram n) :
    (∃ k, D.HasNegativeOverlap k) ↔ negativePartition D ≠ [] := by
  rw [D.negativePartition_ne_nil_iff]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨i, j, hn, _⟩ := (D.hasNegativeOverlap_iff k).mp hk
    exact ⟨i, j, hn⟩
  · rintro ⟨i, j, hn⟩
    have hb := D.negative_below_diagonal hn
    refine ⟨i.val - j.val + 1, (D.hasNegativeOverlap_iff _).mpr ?_⟩
    exact ⟨i, j, hn, by omega⟩

/-- The original partition maximum can be tested on the actual negative cells. -/
theorem minimumRealizingRows_le_iff_cells (D : BetaDiagram n) (r : ℕ) :
    minimumRealizingRows (negativePartition D) ≤ r ↔
      0 < r ∧ ∀ i j : Fin n, D.row i < D.col j → n + 2 ≤ r + i.val - j.val := by
  rw [minimumRealizingRows_le_iff]
  constructor
  · rintro ⟨hr, had⟩
    refine ⟨hr, ?_⟩
    intro i j hn
    have hc := (D.negative_iff_lt_rowCount i j).mp hn
    let k := i.rev.val
    have hkn : k < n := i.rev.isLt
    have hg : (negativePartition D).getD k 0 = negativeRowCount D i := by
      simpa only [k, dif_pos hkn, Fin.eta, Fin.rev_rev] using D.negativePartition_getD k
    have hkl : k < (negativePartition D).length := by
      by_contra h
      rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)] at hg
      omega
    have hh := had k hkl
    rw [hg] at hh
    have hv : k = n - 1 - i.val := by simp [k, Fin.rev]; omega
    have hi := i.isLt
    omega
  · rintro ⟨hr, hcells⟩
    refine ⟨hr, ?_⟩
    intro k hk
    have hlen : (negativePartition D).length ≤ n := by
      exact (List.length_filter_le _ _).trans (by simp [negativePaddedPartition])
    have hkn : k < n := hk.trans_le hlen
    let i : Fin n := (⟨k, hkn⟩ : Fin n).rev
    have hg : (negativePartition D).getD k 0 = negativeRowCount D i := by
      simpa only [dif_pos hkn] using D.negativePartition_getD k
    have hp : 0 < negativeRowCount D i := by
      rw [← hg, List.getD_eq_getElem _ _ hk]
      exact D.negativePartition_isPartition.2 _ (List.getElem_mem hk)
    let j : Fin n := ⟨negativeRowCount D i - 1,
      lt_of_lt_of_le (by omega) (D.negativeRowCount_le i)⟩
    have hn : D.row i < D.col j := (D.negative_iff_lt_rowCount i j).mpr (by dsimp [j]; omega)
    have hh := hcells i j hn
    have hv : i.val = n - 1 - k := by simp [i, Fin.rev]; omega
    dsimp [j] at hh
    rw [hg]
    omega

/-- The first threshold gives the least actual realizing order, `eq:overlap-minimum`. -/
theorem minimumRealizingRows_eq_first_overlap (D : BetaDiagram n)
    (hD : D.Connected) {k₀ : ℕ}
    (hk₀ : IsLeast {k : ℕ | D.HasNegativeOverlap k} k₀) :
    minimumRealizingRows (negativePartition D) = n + 3 - k₀ := by
  obtain ⟨i₀, j₀, hn₀, he₀⟩ := (D.hasNegativeOverlap_iff k₀).mp hk₀.1
  have hk : 2 ≤ k₀ := hk₀.1.1
  have hkn : k₀ ≤ n := by have := i₀.isLt; omega
  apply le_antisymm
  · apply (D.minimumRealizingRows_le_iff_cells _).mpr
    refine ⟨by omega, ?_⟩
    intro i j hn
    have hb := D.negative_below_diagonal hn
    have ho : D.HasNegativeOverlap (i.val - j.val + 1) :=
      (D.hasNegativeOverlap_iff _).mpr ⟨i, j, hn, by omega⟩
    have hh := hk₀.2 ho
    omega
  · have had := (D.minimumRealizingRows_le_iff_cells _).mp (le_refl _)
    have hh := had.2 i₀ j₀ hn₀
    have hb := D.negative_lt_predecessor hD hn₀
    omega

/-- The least order exists exactly for a nonempty negative partition. -/
theorem exists_first_negativeOverlap_iff (D : BetaDiagram n) :
    (∃ k₀, IsLeast {k : ℕ | D.HasNegativeOverlap k} k₀) ↔ negativePartition D ≠ [] := by
  classical
  constructor
  · rintro ⟨k₀, hk₀⟩
    exact (D.exists_negativeOverlap_iff).mp ⟨k₀, hk₀.1⟩
  · intro hp
    have h := (D.exists_negativeOverlap_iff).mpr hp
    exact ⟨Nat.find h, Nat.find_spec h, fun k hk => Nat.find_min' h hk⟩

/-- Every threshold order, not merely its cardinality, is a full Schur invariant. -/
theorem hasNegativeOverlap_iff_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (he : D.schur = E.schur) (k : ℕ) : D.HasNegativeOverlap k ↔ E.HasNegativeOverlap k := by
  unfold HasNegativeOverlap
  rw [D.paddedRowOverlaps_eq_of_schur_eq E he k]

/-- The minimum of the actual connected realizations is invariant without pattern equality. -/
theorem minimumRealizingRows_eq_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    minimumRealizingRows (negativePartition D) = minimumRealizingRows (negativePartition E) := by
  classical
  have hn := D.row_count_of_schur_eq E he
  by_cases hp : negativePartition D = []
  · have hpE : negativePartition E = [] := by
      by_contra hpE
      obtain ⟨k, hk⟩ := E.exists_negativeOverlap_iff.mpr hpE
      have hd := (D.hasNegativeOverlap_iff_of_schur_eq E he k).mpr hk
      exact (D.exists_negativeOverlap_iff.mp ⟨k, hd⟩) hp
    simp only [hp, hpE]
  · obtain ⟨k, hk⟩ := D.exists_first_negativeOverlap_iff.mpr hp
    have hkE : IsLeast {k : ℕ | E.HasNegativeOverlap k} k := by
      refine ⟨(D.hasNegativeOverlap_iff_of_schur_eq E he k).mp hk.1, ?_⟩
      intro l hl
      exact hk.2 ((D.hasNegativeOverlap_iff_of_schur_eq E he l).mpr hl)
    rw [D.minimumRealizingRows_eq_first_overlap hD hk,
      E.minimumRealizingRows_eq_first_overlap hE hkE, hn]

/-- The invariant is the least actual realization, not a surrogate bound. -/
theorem minimumRealizingRows_actual_isLeast (D : BetaDiagram n) :
    IsLeast {r : ℕ | NegativeRealizable (negativePartition D) r}
      (minimumRealizingRows (negativePartition D)) :=
  minimumRealizingRows_isLeast _ D.negativePartition_isPartition

end BetaDiagram
end SkewJacobiNegative
