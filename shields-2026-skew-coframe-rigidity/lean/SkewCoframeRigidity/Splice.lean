/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.BetaDiagrams

/-!
# The `00`-splice of two connected diagrams

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Rigidity with the same literal cap»
(`sec:fixed-caps`, `sc:splice-flags`).  For normalized `K` and `B` with `B` of span `c`, the
splice has full lists `(c + X_K) ∪ (X_B \ {c})` and `(c + (Y_K \ {0})) ∪ Y_B`.  It is again a
connected normalized diagram, of span `span K + span B` and area `|K| + |B|`.  Sorry-free.
-/

namespace SkewCoframeRigidity

open SkewCofactorIndependence

variable {k b : ℕ}

/-- The row list of the splice: `c + X_K` followed by `X_B` without its top entry. -/
def spliceRow (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (i : Fin (k + b + 1)) : ℤ :=
  if h : i.val < k + 1 then B.row 0 + K.row ⟨i.val, h⟩
  else B.row ⟨i.val - k, by omega⟩

/-- The column list of the splice: `c + (Y_K \ {0})` followed by `Y_B`. -/
def spliceCol (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (i : Fin (k + b + 1)) : ℤ :=
  if h : i.val < k then B.row 0 + K.col ⟨i.val, by omega⟩
  else B.col ⟨i.val - k, by omega⟩

/-- Normalization: the last column beta of a diagram is zero. -/
abbrev IsNorm {n : ℕ} (D : BetaDiagram (n + 1)) : Prop := D.col (Fin.last n) = 0

theorem col_pos_of_ne_last {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : 0 < D.col i := by
  have := D.col_strictAnti (show i < Fin.last n from Fin.lt_last_iff_ne_last.mpr hi)
  omega

theorem col_nonneg {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D) (i : Fin (n + 1)) :
    0 ≤ D.col i := by
  have := D.col_strictAnti.antitone (Fin.le_last i)
  omega

theorem top_pos {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D) : 0 < D.row 0 := by
  have := D.row_nonempty 0
  have := col_nonneg D hD 0
  omega

theorem spliceRow_top (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (i : Fin (k + b + 1))
    (h : i.val < k + 1) : spliceRow K B i = B.row 0 + K.row ⟨i.val, h⟩ := by
  simp [spliceRow, h]

theorem spliceRow_bot (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (i : Fin (k + b + 1))
    (h : ¬ i.val < k + 1) : spliceRow K B i = B.row ⟨i.val - k, by omega⟩ := by
  simp [spliceRow, h]

theorem spliceCol_top (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (i : Fin (k + b + 1))
    (h : i.val < k) : spliceCol K B i = B.row 0 + K.col ⟨i.val, by omega⟩ := by
  simp [spliceCol, h]

theorem spliceCol_bot (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (i : Fin (k + b + 1))
    (h : ¬ i.val < k) : spliceCol K B i = B.col ⟨i.val - k, by omega⟩ := by
  simp [spliceCol, h]

/-- The `00`-splice `K ◁ B` of normalized diagrams, as an actual beta diagram. -/
def splice (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (hK : IsNorm K)
    (hB : IsNorm B) : BetaDiagram (k + b + 1) where
  row := spliceRow K B
  col := spliceCol K B
  row_strictAnti := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hc := top_pos B hB
    by_cases h1 : i.val < k + 1
    · by_cases h2 : j.val < k + 1
      · rw [spliceRow_top K B i h1, spliceRow_top K B j h2]
        have := K.row_strictAnti (show (⟨i.val, h1⟩ : Fin (k + 1)) < ⟨j.val, h2⟩ from hij')
        omega
      · rw [spliceRow_top K B i h1, spliceRow_bot K B j h2]
        have h3 : B.row ⟨j.val - k, by omega⟩ < B.row 0 :=
          B.row_strictAnti (show (0 : Fin (b + 1)) < ⟨j.val - k, by omega⟩ from by
            show 0 < j.val - k
            omega)
        have h4 := K.row_nonempty ⟨i.val, h1⟩
        have h5 := col_nonneg K hK ⟨i.val, h1⟩
        omega
    · have h2 : ¬ j.val < k + 1 := by omega
      rw [spliceRow_bot K B i h1, spliceRow_bot K B j h2]
      exact B.row_strictAnti (show (⟨i.val - k, by omega⟩ : Fin (b + 1)) < ⟨j.val - k, by omega⟩
        from by simp only [Fin.lt_def]; omega)
  col_strictAnti := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hc := top_pos B hB
    by_cases h1 : i.val < k
    · by_cases h2 : j.val < k
      · rw [spliceCol_top K B i h1, spliceCol_top K B j h2]
        have := K.col_strictAnti (show (⟨i.val, by omega⟩ : Fin (k + 1)) < ⟨j.val, by omega⟩
          from hij')
        omega
      · rw [spliceCol_top K B i h1, spliceCol_bot K B j h2]
        have h3 : B.col ⟨j.val - k, by omega⟩ ≤ B.col 0 :=
          B.col_strictAnti.antitone (Fin.zero_le _)
        have h4 : 0 < K.col ⟨i.val, by omega⟩ :=
          col_pos_of_ne_last K hK _ (by intro h; have := congrArg Fin.val h; simp at this; omega)
        have h5 := B.row_nonempty 0
        omega
    · have h2 : ¬ j.val < k := by omega
      rw [spliceCol_bot K B i h1, spliceCol_bot K B j h2]
      exact B.col_strictAnti (show (⟨i.val - k, by omega⟩ : Fin (b + 1)) < ⟨j.val - k, by omega⟩
        from by simp only [Fin.lt_def]; omega)
  row_nonempty := by
    intro i
    have hc := top_pos B hB
    by_cases h1 : i.val < k
    · have := K.row_nonempty ⟨i.val, by omega⟩
      rw [spliceRow_top K B i (by omega), spliceCol_top K B i h1]
      omega
    · by_cases h2 : i.val < k + 1
      · have h3 := B.col_strictAnti.antitone (show (0 : Fin (b + 1)) ≤ ⟨i.val - k, by omega⟩
          from Fin.zero_le _)
        have h4 := B.row_nonempty 0
        have h5 := K.row_nonempty ⟨i.val, h2⟩
        have h6 := col_nonneg K hK ⟨i.val, h2⟩
        rw [spliceRow_top K B i h2, spliceCol_bot K B i h1]
        omega
      · rw [spliceRow_bot K B i h2, spliceCol_bot K B i h1]
        have e : (⟨i.val - k, by omega⟩ : Fin (b + 1)) = ⟨i.val - k, by omega⟩ := rfl
        exact B.row_nonempty ⟨i.val - k, by omega⟩

/-- The splice is connected whenever both factors are. -/
theorem splice_connected (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (hK : IsNorm K)
    (hB : IsNorm B) (hKc : K.Connected) (hBc : B.Connected) : (splice K B hK hB).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  change spliceCol K B i ≤ spliceRow K B ⟨i.val + 1, hi⟩
  have hKc' := hKc.2
  have hBc' := hBc.2
  by_cases h1 : i.val < k
  · have := hKc' ⟨i.val, by omega⟩ (by simp only; omega)
    rw [spliceCol_top K B i h1, spliceRow_top K B ⟨i.val + 1, hi⟩ (by simp only; omega)]
    simp only at this ⊢
    omega
  · rw [spliceCol_bot K B i h1, spliceRow_bot K B ⟨i.val + 1, hi⟩ (by simp only; omega)]
    have := hBc' ⟨i.val - k, by omega⟩ (by simp only; omega)
    have e2 : (⟨i.val + 1 - k, by omega⟩ : Fin (b + 1)) = ⟨i.val - k + 1, by omega⟩ := by
      ext; simp only; omega
    simp only [] at this ⊢
    rw [e2]
    exact this

/-- The splice is normalized. -/
theorem splice_norm (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (hK : IsNorm K)
    (hB : IsNorm B) : IsNorm (splice K B hK hB) := by
  change spliceCol K B (Fin.last (k + b)) = 0
  rw [spliceCol_bot K B _ (by simp only [Fin.val_last]; omega)]
  have e : (⟨(Fin.last (k + b)).val - k, by omega⟩ : Fin (b + 1)) = Fin.last b := by
    ext; simp only [Fin.val_last]; omega
  rw [e]
  exact hB

/-- The span of the splice is the sum of the spans. -/
theorem splice_span (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1)) (hK : IsNorm K)
    (hB : IsNorm B) : (splice K B hK hB).row 0 = B.row 0 + K.row 0 := by
  change spliceRow K B 0 = _
  rw [spliceRow_top K B 0 (by simp only [Fin.val_zero]; omega)]
  rfl

end SkewCoframeRigidity
