/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationWeights

/-!
# Produced geometry for arbitrary repeated-block source mates

The full-board source reduction preceding `lem:total-contraction-inverse`
in `shields-2026-skew-class-inflation.tex`.  All rows, both gap
multiplicities, and the Hessenberg condition come from the actual Schur
equality.  The inner gap is allowed to vanish.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- Every source row exceeds the larger seam, not merely the constant inner gap. -/
theorem chain_rows_above_seam (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    ∀ i, A.d < (A.chain a ha l hl).2.r i := by
  induction l generalizing a with
  | nil => exact A.power_rows_above_seam a ha
  | cons b l ih =>
    intro i
    change A.d < Profile.joinRows (A.power a ha) (A.chain b _ l _).2 i
    unfold Profile.joinRows
    split_ifs
    · exact A.power_rows_above_seam a ha _
    · exact ih b _ _ _

/-- The actual source introduces no third kind of gap. -/
theorem chain_gap_values (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    ∀ j, (A.chain a ha l hl).2.g j = A.c ∨ (A.chain a ha l hl).2.g j = A.d := by
  induction l generalizing a with
  | nil => intro j; exact Or.inl rfl
  | cons b l ih =>
    intro j
    change Profile.joinGaps (A.power a ha) (A.chain b _ l _).2 A.d j = A.c ∨
      Profile.joinGaps (A.power a ha) (A.chain b _ l _).2 A.d j = A.d
    unfold Profile.joinGaps
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact ih b _ _ _

/-- Every literal general source has the full row bounds used by the cut-and-contract inverse. -/
theorem diagram_rows_above_seam {M : ℕ} (α : Composition M) (hM : 0 < M) :
    ∀ i, A.d < (A.diagram α hM).2.r i := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · exact A.chain_rows_above_seam _ _ _ _

/-- The two actual gap values are known before any component rigidity theorem is applied. -/
theorem diagram_gap_values {M : ℕ} (α : Composition M) (hM : 0 < M) :
    ∀ j, (A.diagram α hM).2.g j = A.c ∨ (A.diagram α hM).2.g j = A.d := by
  unfold diagram
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · exact A.chain_gap_values _ _ _ _

private theorem gap_multiset_count {n : ℕ} (P : Profile n) (v : ℕ) :
    P.gapMultiset.count v = (Finset.univ.filter (fun j => P.g j = v)).card := by
  simp only [Gluing.Profile.gapMultiset, Multiset.count_map, ← Finset.filter_val,
    Finset.card_def, eq_comm]

/-- All geometric premises of the general source inverse are supplied by its original equality. -/
theorem source_mate_reduction {M : ℕ} (α : Composition M) (hM : 0 < M)
    {n : ℕ} (P : Profile n)
    (he : P.toBetaDiagram.schur = (A.diagram α hM).2.toBetaDiagram.schur) :
    n + 1 = M * A.k + α.length ∧
      Staircase.Thick P ∧
      (∀ i, A.d < P.r i) ∧
      (∀ j, P.g j = A.c ∨ P.g j = A.d) ∧
      (Finset.univ.filter (fun j => P.g j = A.c)).card = M * A.k ∧
      (Finset.univ.filter (fun j => P.g j = A.d)).card = α.length - 1 := by
  have hn : n = (A.diagram α hM).1 := Nat.succ.inj
    (P.toBetaDiagram.row_count_of_schur_eq (A.diagram α hM).2.toBetaDiagram he)
  subst n
  have hr := (Gluing.Profile.rows_eq_of_schur_eq
    (by simpa only [Gluing.Profile.toBetaDiagram_schur] using he)).2
  have hg : P.gapMultiset = (A.diagram α hM).2.gapMultiset :=
    Gluing.Profile.gaps_eq_of_schur_eq
      (by simpa only [Gluing.Profile.toBetaDiagram_schur] using he)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn := P.toBetaDiagram.row_count_of_schur_eq (A.diagram α hM).2.toBetaDiagram he
    exact hn.trans (A.diagram_row_count α hM)
  · exact GeneralHessenberg.hessenberg_thick _
      (hessenberg_of_equal_schur (A.diagram α hM).2.toBetaDiagram P.toBetaDiagram
        (A.diagram α hM).2.toBetaDiagram_connected P.toBetaDiagram_connected he.symm
        (A.diagram_thick α hM).hessenberg)
  · intro i
    have hi : P.r i ∈ P.rowMultiset := Gluing.Profile.mem_rowMultiset.mpr ⟨i, rfl⟩
    rw [hr] at hi
    obtain ⟨j, hj⟩ := Gluing.Profile.mem_rowMultiset.mp hi
    rw [← hj]
    exact A.diagram_rows_above_seam α hM j
  · intro i
    have hi : P.g i ∈ P.gapMultiset := Gluing.Profile.mem_gapMultiset.mpr ⟨i, rfl⟩
    rw [hg] at hi
    obtain ⟨j, hj⟩ := Gluing.Profile.mem_gapMultiset.mp hi
    rw [← hj]
    exact A.diagram_gap_values α hM j
  · rw [← gap_multiset_count, hg, gap_multiset_count]
    exact A.diagram_small_gap_count α hM
  · rw [← gap_multiset_count, hg, gap_multiset_count]
    exact A.diagram_large_gap_count α hM

end SkewClassInflation.SaturationInner
