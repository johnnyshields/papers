import SkewJacobiNegative.NegativeBoards

/-!
# Exact negative-partition realizability

The unrestricted canonical beta-list construction for `sec:negative-invariants`,
`thm:negative-realizability`, `eq:realizability`, and `eq:minimum-intro` of
`shields-2026-skew-jacobi-negative.tex`.
-/

namespace SkewJacobiNegative

open Finset

/-- The exact row inequalities, with zero-based partition indices. -/
def NegativeRowsAdmissible (ρ : List ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ k, k < ρ.length → ρ.getD k 0 + k + 2 ≤ n

/-- Realizability means existence of an actual connected beta diagram. -/
def NegativeRealizable (ρ : List ℕ) (n : ℕ) : Prop :=
  ∃ D : BetaDiagram n, D.Connected ∧ negativePartition D = ρ

namespace NegativePartitionTools

/-- Zero extension of a partition is antitone, including indices beyond its length. -/
theorem getD_antitone (ρ : List ℕ) (hρ : IsNegativePartition ρ) :
    Antitone (fun k => ρ.getD k 0) := by
  intro i j hij
  change ρ.getD j 0 ≤ ρ.getD i 0
  by_cases hj : j < ρ.length
  · have hi : i < ρ.length := lt_of_le_of_lt hij hj
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    rcases eq_or_lt_of_le hij with h | h
    · subst j
      exact le_rfl
    · exact List.pairwise_iff_getElem.mp hρ.1 i j hi hj h
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    exact Nat.zero_le _

/-- The inequalities force enough room for all the positive parts. -/
theorem length_le_of_admissible {ρ : List ℕ} {n : ℕ}
    (h : NegativeRowsAdmissible ρ n) : ρ.length ≤ n := by
  by_contra hn
  have hb := h.2 n (Nat.lt_of_not_ge hn)
  omega

end NegativePartitionTools

namespace BetaDiagram

/-- Necessity of the exact row bound, `eq:realizability`. -/
theorem connected_negativePartition_bound {n : ℕ} (D : BetaDiagram n)
    (hD : D.Connected) (k : ℕ) (hk : k < (negativePartition D).length) :
    (negativePartition D).getD k 0 + k + 2 ≤ n := by
  have hlen : (negativePartition D).length ≤ n := by
    calc
      _ ≤ (negativePaddedPartition D).length := List.length_filter_le _ _
      _ = n := by simp [negativePaddedPartition]
  have hkn : k < n := lt_of_lt_of_le hk hlen
  have hp : 0 < (negativePartition D).getD k 0 := by
    rw [List.getD_eq_getElem _ _ hk]
    exact D.negativePartition_isPartition.2 _ (List.getElem_mem hk)
  rw [D.negativePartition_getD] at hp ⊢
  simp only [dif_pos hkn] at hp ⊢
  have hc := D.connected_negativeRowCount_le hD (Fin.rev ⟨k, hkn⟩)
  have hv : (Fin.rev (⟨k, hkn⟩ : Fin n)).val = n - 1 - k := by
    simp [Fin.rev]
    omega
  rw [hv] at hc
  omega

/-- Every connected diagram supplies the ordinary, unconditional admissibility inequalities. -/
theorem connected_negativePartition_admissible {n : ℕ} (D : BetaDiagram n)
    (hD : D.Connected) : NegativeRowsAdmissible (negativePartition D) n :=
  ⟨hD.1, D.connected_negativePartition_bound hD⟩

end BetaDiagram

/-- The prescribed increasing count sequence: reverse the zero-extended partition. -/
def realizingRowCounts (ρ : List ℕ) (n : ℕ) (i : Fin n) : ℕ :=
  ρ.getD (n - 1 - i.val) 0

theorem realizingRowCounts_monotone (ρ : List ℕ) (hρ : IsNegativePartition ρ)
    (n : ℕ) : Monotone (realizingRowCounts ρ n) := by
  intro i j hij
  apply NegativePartitionTools.getD_antitone ρ hρ
  have hij' : i.val ≤ j.val := hij
  omega

theorem realizingRowCounts_bound {ρ : List ℕ} {n : ℕ}
    (had : NegativeRowsAdmissible ρ n) (i : Fin n) :
    realizingRowCounts ρ n i ≤ i.val - 1 := by
  unfold realizingRowCounts
  by_cases hk : n - 1 - i.val < ρ.length
  · have h := had.2 (n - 1 - i.val) hk
    have hi := i.isLt
    omega
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hk)]
    exact Nat.zero_le _

/-- Canonical integer beta lists in `eq:realizing-lists`, up to common translation. -/
def realizingDiagram (ρ : List ℕ) (hρ : IsNegativePartition ρ) (n : ℕ)
    (had : NegativeRowsAdmissible ρ n) : BetaDiagram n where
  row i := -(n + 1 : ℤ) * realizingRowCounts ρ n i + ((n : ℤ) - i.val)
  col j := -(n + 1 : ℤ) * j.val
  row_strictAnti := by
    intro i j hij
    have hc := realizingRowCounts_monotone ρ hρ n hij.le
    have hcz : (realizingRowCounts ρ n i : ℤ) ≤ realizingRowCounts ρ n j := by
      exact_mod_cast hc
    have hijz : (i.val : ℤ) < j.val := by exact_mod_cast hij
    have hm := mul_nonneg (show (0 : ℤ) ≤ n + 1 by omega)
      (sub_nonneg.mpr hcz)
    dsimp
    nlinarith
  col_strictAnti := by
    intro i j hij
    have hijz : (i.val : ℤ) < j.val := by exact_mod_cast hij
    have hn : (0 : ℤ) < n + 1 := by omega
    dsimp
    nlinarith
  row_nonempty := by
    intro i
    have hb := realizingRowCounts_bound had i
    have hc : (realizingRowCounts ρ n i : ℤ) ≤ i.val := by
      exact_mod_cast (hb.trans (Nat.sub_le _ _))
    have hi : (i.val : ℤ) < n := by exact_mod_cast i.isLt
    have hm := mul_nonneg (show (0 : ℤ) ≤ n + 1 by omega)
      (sub_nonneg.mpr hc)
    nlinarith

/-- The constructed lists produce connected nonempty rows, not just a Ferrers mask. -/
theorem realizingDiagram_connected (ρ : List ℕ) (hρ : IsNegativePartition ρ)
    (n : ℕ) (had : NegativeRowsAdmissible ρ n) :
    (realizingDiagram ρ hρ n had).Connected := by
  refine ⟨had.1, ?_⟩
  intro i hi
  have hb := realizingRowCounts_bound had (⟨i.val + 1, hi⟩ : Fin n)
  have hc : (realizingRowCounts ρ n ⟨i.val + 1, hi⟩ : ℤ) ≤ i.val := by
    exact_mod_cast (by simpa using hb : realizingRowCounts ρ n ⟨i.val + 1, hi⟩ ≤ i.val)
  have hin : (i.val : ℤ) + 1 < n := by exact_mod_cast hi
  have hm := mul_nonneg (show (0 : ℤ) ≤ n + 1 by omega)
    (sub_nonneg.mpr hc)
  change -(n + 1 : ℤ) * i.val ≤
    -(n + 1 : ℤ) * realizingRowCounts ρ n ⟨i.val + 1, hi⟩ +
      ((n : ℤ) - (i.val + 1 : ℕ))
  push_cast
  nlinarith

/-- The strict comparison is exactly `j < c_i`; common zero betas are not counted. -/
theorem realizingDiagram_negative_iff (ρ : List ℕ) (hρ : IsNegativePartition ρ)
    (n : ℕ) (had : NegativeRowsAdmissible ρ n) (i j : Fin n) :
    (realizingDiagram ρ hρ n had).row i < (realizingDiagram ρ hρ n had).col j ↔
      j.val < realizingRowCounts ρ n i := by
  change -(n + 1 : ℤ) * realizingRowCounts ρ n i + ((n : ℤ) - i.val) <
    -(n + 1 : ℤ) * j.val ↔ _
  have hi : (i.val : ℤ) < n := by exact_mod_cast i.isLt
  have h0 : (0 : ℤ) ≤ i.val := by positivity
  constructor
  · intro h
    by_contra hj
    have hjz : (realizingRowCounts ρ n i : ℤ) ≤ j.val := by
      exact_mod_cast Nat.le_of_not_gt hj
    have hm := mul_nonneg (show (0 : ℤ) ≤ n + 1 by omega)
      (sub_nonneg.mpr hjz)
    nlinarith
  · intro hj
    have hjz : (j.val : ℤ) + 1 ≤ realizingRowCounts ρ n i := by
      exact_mod_cast hj
    have hm := mul_nonneg (show (0 : ℤ) ≤ n + 1 by omega)
      (show (0 : ℤ) ≤ realizingRowCounts ρ n i - j.val - 1 by omega)
    nlinarith

/-- Actual cardinality of each constructed negative prefix. -/
theorem realizingDiagram_negativeRowCount (ρ : List ℕ) (hρ : IsNegativePartition ρ)
    (n : ℕ) (had : NegativeRowsAdmissible ρ n) (i : Fin n) :
    negativeRowCount (realizingDiagram ρ hρ n had) i = realizingRowCounts ρ n i := by
  have hc : realizingRowCounts ρ n i < n :=
    lt_of_le_of_lt (realizingRowCounts_bound had i)
      (lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)
  let c : Fin n := ⟨realizingRowCounts ρ n i, hc⟩
  have he : (univ.filter fun j =>
      (realizingDiagram ρ hρ n had).row i < (realizingDiagram ρ hρ n had).col j) =
      Finset.Iio c := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact realizingDiagram_negative_iff ρ hρ n had i j
  unfold negativeRowCount
  rw [he, Fin.card_Iio]

/-- The construction has exactly the requested positive partition. -/
theorem realizingDiagram_negativePartition (ρ : List ℕ) (hρ : IsNegativePartition ρ)
    (n : ℕ) (had : NegativeRowsAdmissible ρ n) :
    negativePartition (realizingDiagram ρ hρ n had) = ρ := by
  apply NegativePartitionTools.ext_getD
    (realizingDiagram ρ hρ n had).negativePartition_isPartition.2 hρ.2
  intro k
  rw [(realizingDiagram ρ hρ n had).negativePartition_getD]
  split_ifs with hk
  · rw [realizingDiagram_negativeRowCount]
    unfold realizingRowCounts
    have hv : n - 1 - (Fin.rev (⟨k, hk⟩ : Fin n)).val = k := by
      simp [Fin.rev]
      omega
    rw [hv]
  · symm
    exact List.getD_eq_default _ _
      ((NegativePartitionTools.length_le_of_admissible had).trans (Nat.le_of_not_gt hk))

/-- Exact, unbounded realizability, `thm:negative-realizability` and `eq:realizability`.
The empty partition is included; connected zero-row diagrams do not exist. -/
theorem negative_realizability_iff (ρ : List ℕ) (hρ : IsNegativePartition ρ) (n : ℕ) :
    NegativeRealizable ρ n ↔ NegativeRowsAdmissible ρ n := by
  constructor
  · rintro ⟨D, hD, hρD⟩
    rw [← hρD]
    exact D.connected_negativePartition_admissible hD
  · intro had
    exact ⟨realizingDiagram ρ hρ n had, realizingDiagram_connected ρ hρ n had,
      realizingDiagram_negativePartition ρ hρ n had⟩

/-- The displayed maximum, with the empty maximum equal to zero. -/
def minimumRealizingRows (ρ : List ℕ) : ℕ :=
  1 + (Finset.range ρ.length).sup (fun k => ρ.getD k 0 + k + 1)

/-- The maximum is equivalent to the original inequalities, including positivity of `n`. -/
theorem minimumRealizingRows_le_iff (ρ : List ℕ) (n : ℕ) :
    minimumRealizingRows ρ ≤ n ↔ NegativeRowsAdmissible ρ n := by
  constructor
  · intro h
    refine ⟨by unfold minimumRealizingRows at h; omega, ?_⟩
    intro k hk
    have hs : ρ.getD k 0 + k + 1 ≤
        (Finset.range ρ.length).sup (fun k => ρ.getD k 0 + k + 1) :=
      Finset.le_sup (f := fun k => ρ.getD k 0 + k + 1) (Finset.mem_range.mpr hk)
    unfold minimumRealizingRows at h
    omega
  · rintro ⟨hn, h⟩
    have hs : (Finset.range ρ.length).sup (fun k => ρ.getD k 0 + k + 1) ≤ n - 1 := by
      apply Finset.sup_le
      intro k hk
      have hb := h k (Finset.mem_range.mp hk)
      omega
    unfold minimumRealizingRows
    omega

/-- The displayed maximum is the least *actual* connected realization, `eq:minimum-intro`. -/
theorem minimumRealizingRows_isLeast (ρ : List ℕ) (hρ : IsNegativePartition ρ) :
    IsLeast {n : ℕ | NegativeRealizable ρ n} (minimumRealizingRows ρ) := by
  constructor
  · exact (negative_realizability_iff ρ hρ _).mpr
      ((minimumRealizingRows_le_iff ρ _).mp le_rfl)
  · intro n hn
    exact (minimumRealizingRows_le_iff ρ n).mpr
      ((negative_realizability_iff ρ hρ n).mp hn)

/-- Every finite partition has an actual connected realization. -/
theorem exists_negative_realization (ρ : List ℕ) (hρ : IsNegativePartition ρ) :
    ∃ n : ℕ, NegativeRealizable ρ n :=
  ⟨minimumRealizingRows ρ, (minimumRealizingRows_isLeast ρ hρ).1⟩

@[simp] theorem minimumRealizingRows_nil : minimumRealizingRows [] = 1 := by
  simp [minimumRealizingRows]

/-- The empty partition occurs for every positive row count, with minimum one. -/
theorem empty_negative_realizable_iff (n : ℕ) : NegativeRealizable [] n ↔ 0 < n := by
  have hp : IsNegativePartition [] := by simp [IsNegativePartition]
  rw [negative_realizability_iff [] hp n]
  simp [NegativeRowsAdmissible]

/-- Connectedness honestly excludes the zero-row case for every partition. -/
theorem not_negative_realizable_zero (ρ : List ℕ) : ¬ NegativeRealizable ρ 0 := by
  rintro ⟨D, hD, _⟩
  exact Nat.not_lt_zero _ hD.1

end SkewJacobiNegative
