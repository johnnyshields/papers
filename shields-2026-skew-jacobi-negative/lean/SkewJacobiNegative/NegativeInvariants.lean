import SkewJacobiNegative.NegativeBoards
import SkewJacobiNegative.RepresentationBridges

/-!
# Negative counts from padded overlaps

The actual full-board count and unrestricted mate closure in
`lem:five-mate-closure` of `shields-2026-skew-jacobi-negative.tex`.
-/

namespace SkewJacobiNegative
namespace BetaDiagram

open Finset
variable {n m : ℕ}

/-- The starts counted at overlap order `k`, retaining zero overlaps. -/
def negativeOverlapStarts (D : BetaDiagram n) (k : ℕ) : Finset ℕ :=
  (range (n - (k - 1))).filter fun j => D.toWeakRows.overlap (k - 1) j ≤ k - 2

/-- Only coordinates in the actual beta arrays enter the overlap test. -/
theorem overlap_negative_iff (D : BetaDiagram n) {k j : ℕ}
    (hk : 2 ≤ k) (hj : j < n - (k - 1)) :
    D.toWeakRows.overlap (k - 1) j ≤ k - 2 ↔
      D.row ⟨j + (k - 1), by omega⟩ < D.col ⟨j, by omega⟩ := by
  have hi : j + (k - 1) < n := by omega
  have hjn : j < n := by omega
  simp only [Overlaps.BetaRows.overlap, toWeakRows, dif_pos hi, dif_pos hjn]
  omega

/-- Nonempty rows exclude negatives on and above the diagonal. -/
theorem negative_below_diagonal (D : BetaDiagram n) {i j : Fin n}
    (h : D.row i < D.col j) : j.val < i.val := by
  by_contra hn
  have hc := D.col_strictAnti.antitone (show i ≤ j from Nat.le_of_not_gt hn)
  have hr := D.row_nonempty i
  omega

/-- The cardinality of the filtered padded multiset is the number of actual starts. -/
theorem negativeOverlapStarts_card (D : BetaDiagram n) (k : ℕ) :
    (D.negativeOverlapStarts k).card =
      ((D.paddedRowOverlaps k).filter fun v => v ≤ k - 2).card := by
  simp only [paddedRowOverlaps, Overlaps.BetaRows.overlaps, Multiset.filter_map,
    Multiset.card_map, negativeOverlapStarts, Finset.filter_val]
  rfl

/-- Distance and start give a bijection with the actual negative cells. -/
theorem negativeCount_eq_overlap_starts (D : BetaDiagram n) :
    negativeCount D = ∑ k ∈ Icc 2 n, (D.negativeOverlapStarts k).card := by
  classical
  let S := (Icc 2 n).sigma (fun k => D.negativeOverlapStarts k)
  have hb : (negativeSites D).card = S.card := by
    apply Finset.card_bij (fun p _ => (⟨p.1.val - p.2.val + 1, p.2.val⟩ : Σ _ : ℕ, ℕ))
    · intro p hp
      have hn := (D.mem_negativeSites p.1 p.2).mp hp
      have hl := D.negative_below_diagonal hn
      have hi := p.1.isLt
      have hj := p.2.isLt
      have hs : p.2.val < n - ((p.1.val - p.2.val + 1) - 1) := by omega
      have he : p.2.val + ((p.1.val - p.2.val + 1) - 1) = p.1.val := by omega
      simp only [S, Finset.mem_sigma, Finset.mem_Icc, negativeOverlapStarts,
        Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨by omega, by omega⟩, hs, ?_⟩
      rw [D.overlap_negative_iff (by omega) hs]
      simpa only [he] using hn
    · intro p hp q hq he
      have hp' := D.negative_below_diagonal ((D.mem_negativeSites _ _).mp hp)
      have hq' := D.negative_below_diagonal ((D.mem_negativeSites _ _).mp hq)
      have h₁ := congrArg Sigma.fst he
      have h₂ : p.2.val = q.2.val := congrArg (fun s : Σ _ : ℕ, ℕ => s.2) he
      apply Prod.ext <;> apply Fin.ext <;> dsimp at h₁ h₂ ⊢ <;> omega
    · intro b hb
      obtain ⟨hk, hj, ho⟩ := (by
        simpa only [S, Finset.mem_sigma, Finset.mem_Icc, negativeOverlapStarts,
          Finset.mem_filter, Finset.mem_range] using hb :
        (2 ≤ b.1 ∧ b.1 ≤ n) ∧ b.2 < n - (b.1 - 1) ∧
          D.toWeakRows.overlap (b.1 - 1) b.2 ≤ b.1 - 2)
      let i : Fin n := ⟨b.2 + (b.1 - 1), by omega⟩
      let j : Fin n := ⟨b.2, by omega⟩
      have hp : (i, j) ∈ negativeSites D :=
        (D.mem_negativeSites i j).mpr ((D.overlap_negative_iff hk.1 hj).mp ho)
      refine ⟨(i, j), hp, ?_⟩
      apply Sigma.ext
      · dsimp [i, j]; omega
      · simp [i, j]
  rw [negativeCount, hb]
  simp only [S, Finset.card_sigma]

/-- Actual negative-count formula, including the zero padded overlap parts. -/
theorem negativeCount_eq_padded_overlaps (D : BetaDiagram n) :
    negativeCount D = ∑ k ∈ Icc 2 n,
      ((D.paddedRowOverlaps k).filter fun v => v ≤ k - 2).card := by
  rw [D.negativeCount_eq_overlap_starts]
  exact Finset.sum_congr rfl (fun k _ => D.negativeOverlapStarts_card k)

/-- No bound on the size, order, or negative pattern of the mate is assumed. -/
theorem negativeCount_eq_of_schur_eq (D : BetaDiagram n) (E : BetaDiagram m)
    (he : D.schur = E.schur) : negativeCount D = negativeCount E := by
  have hn := D.row_count_of_schur_eq E he
  subst m
  rw [D.negativeCount_eq_padded_overlaps, E.negativeCount_eq_padded_overlaps]
  apply Finset.sum_congr rfl
  intro k hk
  rw [D.paddedRowOverlaps_eq_of_schur_eq E he k]

/-- Connected mate closure, `lem:five-mate-closure`, for arbitrary orders. -/
theorem connected_mate_closure (D : BetaDiagram n) (E : BetaDiagram m)
    (_hD : D.Connected) (_hE : E.Connected) (he : D.schur = E.schur) :
    n = m ∧ negativeCount D = negativeCount E :=
  ⟨D.row_count_of_schur_eq E he, D.negativeCount_eq_of_schur_eq E he⟩

end BetaDiagram
end SkewJacobiNegative
