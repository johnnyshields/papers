/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.TopColumn
import SkewCoframeRigidity.Stationary.ComponentRemainder

/-!
# The position of the highest strict component

Formalizes the positional facts behind `sc:top-matching` and `sc:top-support` in
`shields-2026-skew-coframe-rigidity.tex`: if the first strict component occupies the proper
indices `0, …, t`, every row and column below it lies strictly below the least column `a` of the
component, and every row of the component lies strictly above `a`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem colPos_lt_of_beyond (D : BetaDiagram (n + 1)) {t : ℕ} (ht : t + 1 ≤ n) (j : Fin n)
    (hj : t < j.val) : colPos D j < colPos D ⟨t, by omega⟩ := by
  have := colPos_strictAnti D (show (⟨t, by omega⟩ : Fin n) < j from hj)
  exact this

theorem rowPos_lt_of_beyond (D : BetaDiagram (n + 1)) (hn : 0 < n) {t : ℕ} (ht : t + 1 ≤ n)
    (hblk : ∀ j : Fin n, blockIdx D j = blockIdx D ⟨0, hn⟩ ↔ j.val ≤ t) (j : Fin n)
    (hj : t < j.val) : rowPos D j < colPos D ⟨t, by omega⟩ := by
  have hne : blockIdx D j ≠ blockIdx D ⟨0, hn⟩ := fun h => by have := (hblk j).1 h; omega
  have hle : blockIdx D ⟨0, hn⟩ ≤ blockIdx D j :=
    blockIdx_mono D (by rw [Fin.le_iff_val_le_val]; simp)
  have hlt : blockIdx D ⟨0, hn⟩ < blockIdx D j := lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨c, h0c, hcj, j0, hj0, hrow⟩ := exists_cut_of_blockIdx_lt D hlt
  have hj0c : j0 < c := by rw [Fin.lt_def]; omega
  have hcut : IsCut D c := ⟨j0, hj0, hrow⟩
  have hbl := blockIdx_lt_of_cut D hj0c le_rfl hcut
  have hct : t + 1 ≤ c.val := by
    by_contra hc
    have h1 := (hblk c).2 (by omega)
    have h2 := (hblk j0).2 (by omega)
    omega
  have h1 : D.row j.succ ≤ D.row c.succ :=
    D.row_strictAnti.antitone (Fin.succ_le_succ_iff.mpr hcj)
  have h2 : D.col j0.castSucc ≤ D.col (⟨t, by omega⟩ : Fin n).castSucc :=
    D.col_strictAnti.antitone (Fin.castSucc_le_castSucc_iff.mpr (by
      rw [Fin.le_iff_val_le_val]; simp; omega))
  have := rowPos_cast D j
  have := colPos_cast D (⟨t, by omega⟩ : Fin n)
  omega

/-- The flags of `D` at the positions `≥ a`, read off the component data `(L, g)`. -/
def TopFlags (D : BetaDiagram (n + 1)) (a L : ℕ) (g : CohField[X]) : Prop :=
  (∀ s, a ≤ s → (s ∈ colSet D ↔ g.coeff (s - a) ≠ 0)) ∧
  (∀ i, a ≤ i → (i ∈ rowSet D ↔ i = a + L ∨ (a < i ∧ i < a + L ∧
    (PowerSeries.trunc L (letterSeries * (g : PowerSeries CohField))).coeff (i - a) = 0)))

theorem flags_unit (D : BetaDiagram (n + 1)) (hn : 0 < n)
    (hblk : ∀ j : Fin n, blockIdx D j = blockIdx D ⟨0, hn⟩ ↔ j.val ≤ 0)
    (hu : D.row (⟨0, hn⟩ : Fin n).succ = D.col (⟨0, hn⟩ : Fin n).castSucc) :
    TopFlags D (colPos D ⟨0, hn⟩) 0 1 := by
  have hrow : rowPos D ⟨0, hn⟩ = colPos D ⟨0, hn⟩ := by
    have h1 := rowPos_cast D ⟨0, hn⟩
    have h2 := colPos_cast D ⟨0, hn⟩
    apply Nat.cast_injective (R := ℤ); push_cast; omega
  refine ⟨fun s hs => ?_, fun i hi => ?_⟩
  · rw [Polynomial.coeff_one]
    constructor
    · intro hmem
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hmem
      by_cases hj : j.val ≤ 0
      · have : j = ⟨0, hn⟩ := Fin.ext (by simp only; omega)
        subst this; simp
      · exact absurd hs (not_le.2 (colPos_lt_of_beyond D (t := 0) hn j (by omega)))
    · intro h
      have : s - colPos D ⟨0, hn⟩ = 0 := by by_contra h'; simp [h'] at h
      have hs' : s = colPos D ⟨0, hn⟩ := by omega
      rw [hs']; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · simp only [Nat.add_zero]
    constructor
    · intro hmem
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hmem
      left
      by_cases hj : j.val ≤ 0
      · have : j = ⟨0, hn⟩ := Fin.ext (by simp only; omega)
        subst this; exact hrow
      · exact absurd hi (not_le.2 (hrow ▸ rowPos_lt_of_beyond D hn (t := 0) hn hblk j (by omega)))
    · rintro (h | ⟨h1, h2, -⟩)
      · rw [h, ← hrow]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · omega

section Big

variable {D : BetaDiagram (n + 1)} {t : ℕ} (ht : t + 1 ≤ n) (hpos : BlockPos D t ht)

theorem firstBlock_col (j : Fin (t + 1)) :
    (firstBlock D t ht hpos).col j = D.col (⟨j.val, by omega⟩ : Fin n).castSucc := by
  show D.col (blockEmb 0 (t + 1) (by omega) j).castSucc = _
  congr 2
  exact Fin.ext (by simp [blockEmb])

theorem firstBlock_row (j : Fin (t + 1)) :
    (firstBlock D t ht hpos).row j = D.row (⟨j.val, by omega⟩ : Fin n).succ := by
  show D.row (blockEmb 0 (t + 1) (by omega) j).succ = _
  congr 2
  exact Fin.ext (by simp [blockEmb])

theorem colPos_firstBlock (j : Fin t) :
    colPos D ⟨j.val, by omega⟩ = colPos D ⟨t, by omega⟩ + colPos (firstBlock D t ht hpos) j := by
  have h1 := colPos_cast D (⟨j.val, by omega⟩ : Fin n)
  have h2 := colPos_cast D (⟨t, by omega⟩ : Fin n)
  have h3 := colPos_cast (firstBlock D t ht hpos) j
  have e1 := firstBlock_col ht hpos j.castSucc
  have e2 := firstBlock_col ht hpos (Fin.last t)
  have e3 : (⟨(Fin.last t).val, by omega⟩ : Fin n) = ⟨t, by omega⟩ := Fin.ext (by simp)
  have e4 : (⟨(j.castSucc).val, by omega⟩ : Fin n) = ⟨j.val, by omega⟩ := Fin.ext (by simp)
  rw [e3] at e2
  rw [e4] at e1
  apply Nat.cast_injective (R := ℤ)
  push_cast
  omega

theorem rowPos_firstBlock (j : Fin t) :
    rowPos D ⟨j.val + 1, by omega⟩ =
      colPos D ⟨t, by omega⟩ + rowPos (firstBlock D t ht hpos) j := by
  have h1 := rowPos_cast D (⟨j.val + 1, by omega⟩ : Fin n)
  have h2 := colPos_cast D (⟨t, by omega⟩ : Fin n)
  have h3 := rowPos_cast (firstBlock D t ht hpos) j
  have e1 := firstBlock_row ht hpos j.succ
  have e2 := firstBlock_col ht hpos (Fin.last t)
  have e3 : (⟨(Fin.last t).val, by omega⟩ : Fin n) = ⟨t, by omega⟩ := Fin.ext (by simp)
  have e4 : (⟨(j.succ).val, by omega⟩ : Fin n) = ⟨j.val + 1, by omega⟩ := Fin.ext (by simp)
  rw [e3] at e2
  rw [e4] at e1
  apply Nat.cast_injective (R := ℤ)
  push_cast
  omega

theorem rowPos_zero_firstBlock (hn : 0 < n) :
    rowPos D ⟨0, hn⟩ = colPos D ⟨t, by omega⟩ + span (firstBlock D t ht hpos) := by
  have h1 := rowPos_cast D (⟨0, hn⟩ : Fin n)
  have h2 := colPos_cast D (⟨t, by omega⟩ : Fin n)
  have h3 := span_cast (firstBlock D t ht hpos)
  have e1 := firstBlock_row ht hpos 0
  have e2 := firstBlock_col ht hpos (Fin.last t)
  have e3 : (⟨(Fin.last t).val, by omega⟩ : Fin n) = ⟨t, by omega⟩ := Fin.ext (by simp)
  rw [e3] at e2
  unfold BetaDiagram.largestLabel at h3
  apply Nat.cast_injective (R := ℤ)
  push_cast
  have e0 : (⟨(0 : Fin (t + 1)).val, by omega⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext (by simp)
  rw [e0] at e1
  omega

theorem flags_big (hn : 0 < n)
    (hblk : ∀ j : Fin n, blockIdx D j = blockIdx D ⟨0, hn⟩ ↔ j.val ≤ t)
    (hE : (firstBlock D t ht hpos).Connected) :
    TopFlags D (colPos D ⟨t, by omega⟩) (span (firstBlock D t ht hpos))
      (coframe (firstBlock D t ht hpos)) := by
  set E := firstBlock D t ht hpos with hEdef
  set a := colPos D ⟨t, by omega⟩ with ha
  refine ⟨fun s hs => ?_, fun i hi => ?_⟩
  · constructor
    · intro hmem
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hmem
      rcases lt_trichotomy j.val t with hj | hj | hj
      · have := colPos_firstBlock ht hpos (⟨j.val, hj⟩ : Fin t)
        have e : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
        simp only [e] at this
        rw [this, ← ha, Nat.add_sub_cancel_left]
        exact (coframe_coeff_ne_zero_iff hE (colPos_pos E _)).2
          (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      · have e : j = ⟨t, by omega⟩ := Fin.ext hj
        have e2 : colPos D j = a := by rw [e]
        rw [e2, Nat.sub_self, coeff_zero_coframe]; exact one_ne_zero
      · exact absurd hs (not_le.2 (colPos_lt_of_beyond D ht j hj))
    · intro h
      by_cases hsa : s = a
      · rw [hsa]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · have hpos' : 0 < s - a := by omega
        have hmem := (coframe_coeff_ne_zero_iff hE hpos').1 h
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
        have := colPos_firstBlock ht hpos j
        refine Finset.mem_image.mpr ⟨⟨j.val, by omega⟩, Finset.mem_univ _, ?_⟩
        rw [this, hj]; omega
  · have hTop := rowPos_zero_firstBlock ht hpos hn
    rw [← hEdef] at hTop
    constructor
    · intro hmem
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hmem
      by_cases hi' : i'.val ≤ t
      · rcases Nat.eq_zero_or_pos i'.val with h0 | h0
        · left
          have : i' = ⟨0, hn⟩ := Fin.ext h0
          rw [this, hTop]
        · right
          obtain ⟨j, hj⟩ : ∃ j : Fin t, j.val + 1 = i'.val := ⟨⟨i'.val - 1, by omega⟩, by simp; omega⟩
          have e : i' = ⟨j.val + 1, by omega⟩ := Fin.ext hj.symm
          rw [e, rowPos_firstBlock ht hpos j, ← ha, ← hEdef]
          refine ⟨by have := rowPos_pos E j; omega, by have := rowPos_lt_span E j; omega, ?_⟩
          rw [Nat.add_sub_cancel_left]
          have := (numerator_coeff_eq_zero_iff hE (rowPos_pos E j) (rowPos_lt_span E j)).2
            (Finset.mem_image_of_mem _ (Finset.mem_univ _))
          exact this
      · exact absurd hi (not_le.2 (lt_of_lt_of_le (rowPos_lt_of_beyond D hn ht hblk i'
          (by omega)) le_rfl))
    · rintro (h | ⟨h1, h2, h3⟩)
      · rw [h, ← hTop]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · have hnum : (numerator E).coeff (i - a) = 0 := h3
        have hL : i - a < span E := by omega
        have hmem := (numerator_coeff_eq_zero_iff hE (by omega) hL).1 hnum
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
        refine Finset.mem_image.mpr ⟨⟨j.val + 1, by omega⟩, Finset.mem_univ _, ?_⟩
        rw [rowPos_firstBlock ht hpos j, ← ha, ← hEdef, hj]; omega

end Big

end SkewCoframeRigidity.Coframe
