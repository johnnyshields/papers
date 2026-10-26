/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryRestoration
import Mathlib.Order.Interval.Finset.Fin

/-!
# Exact retained-beta ranks at a common suffix beta

The parity counts behind `eq:boundary-lowest-degree` in
`shields-2026-skew-class-inflation.tex`.  At the restored beta `s*q`,
exactly `s-1` retained upper betas and `s+1` retained lower betas lie
below it.  Their sum is even.  Sorry-free.
-/

namespace SkewClassInflation.BoundaryParameters

open SkewJacobiNegative

variable (B : BoundaryParameters)

/-- The position of a common suffix grid point in the retained upper list. -/
theorem upper_lt_suffix_grid_iff (M : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.Ioo 0 M)
    (s : ℕ) (hs : s ∈ T) (i : Fin (M + 1)) :
    B.upper M T i < (B.q : ℤ) * s ↔ M + 1 - s < i.val := by
  have hsB := Finset.mem_Ioo.mp (hT hs)
  have hp := B.p_pos
  have hpq : B.p < B.q := by have := B.p_lt_a; have := B.ap_lt_q; omega
  have hq := B.q_pos
  have hi := i.isLt
  have hmul : (B.q : ℤ) * ((s : ℤ) + 1) ≤ (B.q : ℤ) * M :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  unfold upper
  split_ifs with h0 h1
  · constructor <;> intro hh <;> first | omega | nlinarith
  · constructor <;> intro hh <;> first | omega | nlinarith
  · let r := M + 1 - i.val
    have hri : (r : ℤ) = (M : ℤ) + 1 - i.val := by dsimp [r]; omega
    change (B.q : ℤ) * ((M : ℤ) + 1 - i.val) + B.bit T r < (B.q : ℤ) * s ↔ _
    rw [← hri]
    have hbit := B.bit_le T r
    rcases lt_trichotomy r s with hrs | hrs | hrs
    · have hm : (B.q : ℤ) * ((r : ℤ) + 1) ≤ (B.q : ℤ) * s :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have he : (B.q : ℤ) * r + B.bit T r < (B.q : ℤ) * s := by nlinarith
      have hrhs : M + 1 - s < i.val := by dsimp [r] at hrs; omega
      exact ⟨fun _ => hrhs, fun _ => he⟩
    · have hb : B.bit T r = B.p := by rw [hrs, bit, ite_eq_left hs]
      have he : ¬ ((B.q : ℤ) * r + B.bit T r < (B.q : ℤ) * s) := by rw [hb, hrs]; omega
      have hn : ¬ M + 1 - s < i.val := by dsimp [r] at hrs; omega
      exact ⟨fun hh => (he hh).elim, fun hh => (hn hh).elim⟩
    · have hm : (B.q : ℤ) * ((s : ℤ) + 1) ≤ (B.q : ℤ) * r :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have he : ¬ ((B.q : ℤ) * r + B.bit T r < (B.q : ℤ) * s) := by
        have hb0 : (0 : ℤ) ≤ B.bit T r := by omega
        nlinarith
      have hn : ¬ M + 1 - s < i.val := by dsimp [r] at hrs; omega
      exact ⟨fun hh => (he hh).elim, fun hh => (hn hh).elim⟩

/-- The same restored suffix beta sits two retained positions earlier in the lower list. -/
theorem lower_lt_suffix_grid_iff (M s : ℕ) (hs : 0 < s) (hsM : s < M)
    (i : Fin (M + 1)) : B.lower M i < (B.q : ℤ) * s ↔ M - s ≤ i.val := by
  have hq := B.q_pos
  have ha := B.p_lt_a
  have hp := B.p_pos
  have haq : B.a < B.q := by have := B.ap_lt_q; omega
  have hi := i.isLt
  unfold lower
  split_ifs with hlast
  · have hm : (0 : ℤ) < (B.q : ℤ) * s := mul_pos (by omega) (by omega)
    constructor <;> intro hh <;> omega
  · let r := M - i.val
    have hri : (r : ℤ) = (M : ℤ) - i.val := by dsimp [r]; omega
    change (B.q : ℤ) * ((M : ℤ) - i.val) - B.a < (B.q : ℤ) * s ↔ _
    rw [← hri]
    by_cases hrs : r ≤ s
    · have hm : (B.q : ℤ) * r ≤ (B.q : ℤ) * s :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have he : (B.q : ℤ) * r - B.a < (B.q : ℤ) * s := by omega
      have hb : M - s ≤ i.val := by dsimp [r] at hrs; omega
      exact ⟨fun _ => hb, fun _ => he⟩
    · have hm : (B.q : ℤ) * ((s : ℤ) + 1) ≤ (B.q : ℤ) * r :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have he : ¬ ((B.q : ℤ) * r - B.a < (B.q : ℤ) * s) := by nlinarith
      have hb : ¬ M - s ≤ i.val := by dsimp [r] at hrs; omega
      exact ⟨fun hh => (he hh).elim, fun hh => (hb hh).elim⟩

/-- Exactly `s-1` retained rows cross a restored common suffix beta. -/
theorem core_row_crossing_count (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) (s : ℕ) (hs : s ∈ T) :
    (Finset.univ.filter (fun i : Fin (M + 1) => (B.core M hM T).row i < (B.q : ℤ) * s)).card =
      s - 1 := by
  classical
  have hsB := Finset.mem_Ioo.mp (hT hs)
  let r : Fin (M + 1) := ⟨M + 1 - s, by omega⟩
  have he : Finset.univ.filter (fun i : Fin (M + 1) =>
      (B.core M hM T).row i < (B.q : ℤ) * s) = Finset.Ioi r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    exact B.upper_lt_suffix_grid_iff M T hT s hs i
  rw [he, Fin.card_Ioi]
  dsimp [r]
  omega

/-- Exactly `s+1` retained columns cross the same restored common suffix beta. -/
theorem core_col_crossing_count (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) (s : ℕ) (hs : s ∈ T) :
    (Finset.univ.filter (fun i : Fin (M + 1) => (B.core M hM T).col i < (B.q : ℤ) * s)).card =
      s + 1 := by
  classical
  have hsB := Finset.mem_Ioo.mp (hT hs)
  let r : Fin (M + 1) := ⟨M - s, by omega⟩
  have he : Finset.univ.filter (fun i : Fin (M + 1) =>
      (B.core M hM T).col i < (B.q : ℤ) * s) = Finset.Ici r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    exact B.lower_lt_suffix_grid_iff M s hsB.1 hsB.2 i
  rw [he, Fin.card_Ici]
  dsimp [r]
  omega

end SkewClassInflation.BoundaryParameters
