/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.HessenbergIntervalDistances
import SkewCornerDescent.Matrix.OriginalClosureResponse
import SkewCornerDescent.CyclicFiniteIntervals

/-!
# The completed actual selected gap word

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:original-transfer`).
The closure position combines both actual exterior endpoints; all other positions use the
original internal diagonal distances. The total is the literal parent top, not a distinct-class sum.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original internal gaps followed by the true cap-splice gap. Positions are not
identified when their response values or diagonal distances coincide. -/
noncomputable def originalCompletedGap {n : ℕ} (P : Profile n)
    (k : Fin (originalSelectedCount (hD := hD) P)) : ℤ :=
  if k.val + 1 = originalSelectedCount (hD := hD) P then
    originalHessenbergDistance (hD := hD) P 0 0 +
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) - (c.top : ℤ)
  else originalHessenbergDistance (hD := hD) P k.succ k.succ - (c.top : ℤ)

/-- The completed actual gaps are strictly positive, including the cap-splice position. -/
theorem originalCompletedGap_pos {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (k : Fin (originalSelectedCount (hD := hD) P)) : 0 < c.originalCompletedGap P k := by
  unfold originalCompletedGap
  split_ifs
  · have hf := c.originalHessenbergDistance_gt_top P hB 0 0 le_rfl
    have hl := c.originalHessenbergDistance_gt_top P hB (Fin.last _) (Fin.last _) le_rfl
    have := c.top.property
    omega
  · have h := c.originalHessenbergDistance_gt_top P hB k.succ k.succ le_rfl
    omega

/-- Every complete actual gap strictly exceeds the selected span. Internal
positions use both complete selected endpoint strips; the last position uses
both true caps. No numeric gap lower bound is supplied as a hypothesis. -/
theorem originalCompletedGap_gt_top {n : ℕ} (P : Profile n)
    (k : Fin (originalSelectedCount (hD := hD) P)) :
    (c.top : ℤ) < c.originalCompletedGap P k := by
  have hB : 0 < originalSelectedCount (hD := hD) P := by have := k.isLt; omega
  unfold originalCompletedGap
  split_ifs with hk
  · have hf := c.originalHessenbergDistance_gt_top P hB 0 0 le_rfl
    have hl := c.originalHessenbergDistance_gt_top P hB (Fin.last _) (Fin.last _) le_rfl
    omega
  · let next : Fin (originalSelectedCount (hD := hD) P) := ⟨k.val + 1, by
      have := k.isLt
      omega⟩
    have hknext : k < next := by change k.val < k.val + 1; omega
    have h := c.originalHessenbergDistance_selected_gt_twice_top P k next hknext
    change 2 * (c.top : ℤ) < originalHessenbergDistance (hD := hD) P k.succ k.succ at h
    omega

/-- The exact complete gap sum equals the literal parent endpoint distance. Both caps
and every selected occurrence are counted, even when some values agree. -/
theorem originalCompletedGap_sum {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    ∑ k, c.originalCompletedGap P k = P.xi 0 - P.zeta (Fin.last n) := by
  classical
  let B := originalSelectedCount (hD := hD) P
  have hB' : 0 < B := hB
  have he (k : Fin B) : c.originalCompletedGap P k =
      originalHessenbergDistance (hD := hD) P k.succ k.succ - (c.top : ℤ) +
        if k.val + 1 = B then originalHessenbergDistance (hD := hD) P 0 0 else 0 := by
    by_cases hk : k.val + 1 = B
    · have hl : k.succ = Fin.last B := by
        apply Fin.ext
        simpa only [Fin.val_succ, Fin.val_last] using hk
      dsimp only [B] at hk hl ⊢
      simp only [originalCompletedGap, hk, ite_true, hl]
      ring
    · dsimp only [B] at hk ⊢
      simp only [originalCompletedGap, hk, ite_false, add_zero]
  let last : Fin B := ⟨B - 1, by omega⟩
  have hfirst : (∑ k : Fin B, if k.val + 1 = B then
      originalHessenbergDistance (hD := hD) P 0 0 else 0) =
      originalHessenbergDistance (hD := hD) P 0 0 := by
    rw [Finset.sum_eq_single last]
    · rw [ite_eq_left (show last.val + 1 = B by dsimp [last]; omega)]
    · intro k _ hk
      rw [ite_eq_right]
      intro he
      apply hk
      apply Fin.ext
      dsimp [last]
      omega
    · simp
  simp_rw [he]
  rw [Finset.sum_add_distrib, hfirst, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs := c.originalHessenbergDistance_sum P
  rw [Fin.sum_univ_succ] at hs
  change originalHessenbergDistance (hD := hD) P 0 0 +
      (∑ k : Fin B, originalHessenbergDistance (hD := hD) P k.succ k.succ) =
        P.xi 0 - P.zeta (Fin.last n) + (B : ℤ) * (c.top : ℤ) at hs
  dsimp only [B] at hs ⊢
  omega

/-- The last position of the completed actual word is exactly the geometric horizontal
splice between its actual first and last selected component occurrences. -/
theorem originalCompletedGap_last_eq_splice {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    c.originalCompletedGap P last =
      originalCapSpliceDistance P
        (originalSelectedEnumeration P ⟨0, hB⟩) (originalSelectedEnumeration P last) := by
  dsimp only
  rw [originalCompletedGap, ite_eq_left (by
    change (originalSelectedCount (hD := hD) P - 1) + 1 = originalSelectedCount (hD := hD) P
    omega), originalHessenbergDistance_first P hB, originalHessenbergDistance_last P hB]
  have h := c.originalCapSpliceDistance_cap_sum P
    (originalSelectedEnumeration P ⟨0, hB⟩)
    (originalSelectedEnumeration P ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩)
  omega

/-- An internal actual endpoint window is the corresponding positional window in the
completed gap word. The final closure gap is excluded by the literal endpoint inequality. -/
theorem originalCompletedGap_internal_window {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P)) (hij : i ≤ j)
    (hj : j.val + 1 < originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) P i.succ j.succ = (c.top : ℤ) +
      ∑ k ∈ Finset.Icc i j, c.originalCompletedGap P k := by
  classical
  rw [c.originalHessenbergDistance_interval_sum P i.succ j.succ
    (by simpa using hij), ← Fin.map_succEmb_Icc, Finset.sum_map]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkj := (Finset.mem_Icc.mp hk).2
  have hlast : k.val + 1 ≠ originalSelectedCount (hD := hD) P := by
    change k.val ≤ j.val at hkj
    omega
  simp only [originalCompletedGap, hlast, ite_false]
  rfl

/-- A left boundary window uses the true left cap and every intervening internal gap.
It does not replace the left cap by the completed closure response. -/
theorem originalCompletedGap_left_window {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (j : Fin (originalSelectedCount (hD := hD) P))
    (hj : j.val + 1 < originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) P 0 j.succ =
      originalHessenbergDistance (hD := hD) P 0 0 +
        ∑ k ∈ Finset.Icc ⟨0, hB⟩ j, c.originalCompletedGap P k := by
  have hw := c.originalCompletedGap_internal_window P ⟨0, hB⟩ j
    (by change 0 ≤ j.val; omega) hj
  have hs := c.originalHessenbergDistance_subdiagonal P ⟨0, hB⟩
  have he : originalHessenbergDistance (hD := hD) P 0 j.succ =
      originalHessenbergDistance (hD := hD) P 0 0 +
        originalHessenbergDistance (hD := hD) P (⟨0, hB⟩ : Fin _).succ j.succ -
          (c.top : ℤ) := by
    unfold originalHessenbergDistance at hs ⊢
    change _ - P.zeta (originalColSplitEquiv P
      (.inl (originalHessenbergCols P 0))) = (c.top : ℤ) at hs
    omega
  rw [he, hw]
  ring

/-- The internal actual distance is its complete cyclic window in the constructed gap
word. The cycle is indexed by occurrences, so equal gap values remain separate. -/
theorem originalCompletedGap_cyclic_internal_window {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (i j : Fin (originalSelectedCount (hD := hD) P)) (hij : i ≤ j)
    (hj : j.val + 1 < originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) P i.succ j.succ = (c.top : ℤ) +
      CyclicWindows.windowSum
        (fun z => c.originalCompletedGap P
          ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
        1 (j.val - i.val + 1) (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
  rw [CyclicWindows.windowSum_finite_interval _ i j hij]
  exact c.originalCompletedGap_internal_window P i j hij hj

/-- Completing a left-cap window with the actual closure gap is a strict upper bound:
the true right cap is strictly positive and is not silently discarded. -/
theorem originalCompletedGap_left_window_lt_completion {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (j : Fin (originalSelectedCount (hD := hD) P))
    (hj : j.val + 1 < originalSelectedCount (hD := hD) P) :
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    originalHessenbergDistance (hD := hD) P 0 j.succ < (c.top : ℤ) +
      (c.originalCompletedGap P last +
        ∑ k ∈ Finset.Icc ⟨0, hB⟩ j, c.originalCompletedGap P k) := by
  dsimp only
  rw [c.originalCompletedGap_left_window P hB j hj, originalCompletedGap,
    ite_eq_left (by
      change (originalSelectedCount (hD := hD) P - 1) + 1 =
        originalSelectedCount (hD := hD) P
      omega)]
  have hcap := c.originalHessenbergDistance_gt_top P hB (Fin.last _) (Fin.last _) le_rfl
  have htop := c.top.property
  omega

/-- The closure position adds the true left cap to the last diagonal increment;
all other positions are the literal internal diagonal increments. -/
theorem originalCompletedGap_eq_diagonal {n : ℕ} (P : Profile n)
    (k : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalCompletedGap P k =
      originalHessenbergDistance (hD := hD) P k.succ k.succ - (c.top : ℤ) +
        if k.val + 1 = originalSelectedCount (hD := hD) P then
          originalHessenbergDistance (hD := hD) P 0 0 else 0 := by
  by_cases hk : k.val + 1 = originalSelectedCount (hD := hD) P
  · have hl : k.succ = Fin.last (originalSelectedCount (hD := hD) P) := by
      apply Fin.ext
      simpa only [Fin.val_succ, Fin.val_last] using hk
    simp only [originalCompletedGap, hk, ite_true, hl]
    ring
  · simp only [originalCompletedGap, hk, ite_false, add_zero]

/-- A right-cap endpoint interval is the completed positional window minus the true
left cap. Both caps retain their actual geometric values. -/
theorem originalCompletedGap_right_window {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    originalHessenbergDistance (hD := hD) P i.succ (Fin.last _) +
      originalHessenbergDistance (hD := hD) P 0 0 =
        (c.top : ℤ) + ∑ k ∈ Finset.Icc i last, c.originalCompletedGap P k := by
  classical
  dsimp only
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  have hil : i ≤ last := by change i.val ≤ last.val; dsimp [last]; omega
  have hlast : last.succ = Fin.last (originalSelectedCount (hD := hD) P) := by
    apply Fin.ext
    dsimp [last]
    omega
  have hw := c.originalHessenbergDistance_interval_sum P i.succ last.succ
    (by simpa using hil)
  rw [← Fin.map_succEmb_Icc, Finset.sum_map] at hw
  have hone : (∑ k ∈ Finset.Icc i last,
      if k.val + 1 = originalSelectedCount (hD := hD) P then
        originalHessenbergDistance (hD := hD) P 0 0 else 0) =
      originalHessenbergDistance (hD := hD) P 0 0 := by
    rw [Finset.sum_eq_single last]
    · rw [ite_eq_left (by dsimp [last]; omega)]
    · intro k _ hk
      rw [ite_eq_right]
      intro he
      apply hk
      apply Fin.ext
      dsimp [last]
      omega
    · intro h
      exact (h (Finset.mem_Icc.mpr ⟨hil, le_rfl⟩)).elim
  change _ = (c.top : ℤ) + ∑ k ∈ Finset.Icc i last, c.originalCompletedGap P k
  simp_rw [c.originalCompletedGap_eq_diagonal P]
  rw [Finset.sum_add_distrib, hone]
  change originalHessenbergDistance (hD := hD) P i.succ last.succ =
    (c.top : ℤ) + ∑ k ∈ Finset.Icc i last,
      (originalHessenbergDistance (hD := hD) P k.succ k.succ - (c.top : ℤ)) at hw
  rw [hlast] at hw
  omega

/-- The right-cap interval lies strictly below its complete cyclic gap window.
The omitted contribution is the actual positive left cap. -/
theorem originalCompletedGap_cyclic_right_window_lt {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    originalHessenbergDistance (hD := hD) P i.succ (Fin.last _) < (c.top : ℤ) +
      CyclicWindows.windowSum
        (fun z => c.originalCompletedGap P
          ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
        1 (originalSelectedCount (hD := hD) P - i.val)
        (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  have hil : i ≤ last := by change i.val ≤ last.val; dsimp [last]; omega
  have he : originalSelectedCount (hD := hD) P - i.val = last.val - i.val + 1 := by
    dsimp [last]
    omega
  rw [he, CyclicWindows.windowSum_finite_interval _ i last hil]
  have hw := c.originalCompletedGap_right_window P hB i
  have hcap := c.originalHessenbergDistance_gt_top P hB 0 0 le_rfl
  have htop := c.top.property
  dsimp only at hw
  change originalHessenbergDistance (hD := hD) P i.succ (Fin.last _) +
    originalHessenbergDistance (hD := hD) P 0 0 =
      (c.top : ℤ) + ∑ k ∈ Finset.Icc i last, c.originalCompletedGap P k at hw
  change _ < (c.top : ℤ) + ∑ k ∈ Finset.Icc i last, c.originalCompletedGap P k
  omega

/-- The left-cap interval lies strictly below the wrapping completed gap window.
The final closure occurrence and every initial internal occurrence are retained. -/
theorem originalCompletedGap_cyclic_left_window_lt {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : Fin (originalSelectedCount (hD := hD) P))
    (hj : j.val + 1 < originalSelectedCount (hD := hD) P) :
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    originalHessenbergDistance (hD := hD) P 0 j.succ < (c.top : ℤ) +
      CyclicWindows.windowSum
        (fun z => c.originalCompletedGap P
          ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
        1 (j.val + 2) (last.val : ZMod (originalSelectedCount (hD := hD) P)) := by
  dsimp only
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  change originalHessenbergDistance (hD := hD) P 0 j.succ < (c.top : ℤ) +
    CyclicWindows.windowSum
      (fun z => c.originalCompletedGap P
        ((ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm z))
      1 (j.val + 2) (last.val : ZMod (originalSelectedCount (hD := hD) P))
  have hl : last.val + 1 = originalSelectedCount (hD := hD) P := by
    dsimp [last]
    omega
  rw [show j.val + 2 = (j.val + 1) + 1 by omega,
    CyclicWindows.windowSum_finite_wrap _ last hl]
  have hz : (j.val + 1) = j.val - (⟨0, hB⟩ : Fin _).val + 1 := by rfl
  rw [hz, show (0 : ZMod (originalSelectedCount (hD := hD) P)) =
    ((⟨0, hB⟩ : Fin _).val : ZMod _) by simp only [Nat.cast_zero],
    CyclicWindows.windowSum_finite_interval _ ⟨0, hB⟩ j
      (by change 0 ≤ j.val; omega)]
  exact c.originalCompletedGap_left_window_lt_completion P hB j hj

end SkewCornerDescent.Matrix.SelectedCoordinate
