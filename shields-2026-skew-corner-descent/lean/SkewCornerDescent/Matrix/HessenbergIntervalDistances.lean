/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalHessenbergInventory
import Mathlib.Order.Interval.Finset.Fin

/-!
# Literal interval distance as a complete diagonal window sum

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Actual selected endpoint distances telescope without replacing either exterior cap.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Equal selected subdiagonal distances telescope every upper endpoint interval to
its complete diagonal window, including both endpoints. -/
theorem hessenberg_distance_interval_sum {B : ℕ} (x z : Fin (B + 1) → ℤ) (N : ℤ)
    (hN : ∀ k : Fin B, x k.succ - z k.castSucc = N)
    (i j : Fin (B + 1)) (hij : i ≤ j) :
    x i - z j = N + ∑ k ∈ Finset.Icc i j, (x k - z k - N) := by
  classical
  revert hij
  induction j using Fin.induction with
  | zero =>
    intro hij
    have hi : i = 0 := by
      apply Fin.ext
      change (i : ℕ) = 0
      change (i : ℕ) ≤ 0 at hij
      omega
    subst i
    simp
  | succ j ih =>
    intro hij
    by_cases hi : i = j.succ
    · subst i
      simp
    · have hij' : i ≤ j.castSucc := by
        have hne := Fin.val_ne_of_ne hi
        change (i : ℕ) ≤ (j.succ : ℕ) at hij
        change (i : ℕ) ≤ (j.castSucc : ℕ)
        simp only [Fin.val_succ, Fin.val_castSucc] at hij hne ⊢
        omega
      have hs : Finset.Icc i j.succ = insert j.succ (Finset.Icc i j.castSucc) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert, Fin.ext_iff]
        change ((i : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) ≤ (j : ℕ) + 1) ↔
          (k : ℕ) = (j : ℕ) + 1 ∨ ((i : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) ≤ (j : ℕ))
        change (i : ℕ) ≤ (j : ℕ) at hij'
        omega
      have hjnot : j.succ ∉ Finset.Icc i j.castSucc := by
        simp only [Finset.mem_Icc, not_and]
        intro _ h
        change (j : ℕ) + 1 ≤ (j : ℕ) at h
        omega
      rw [hs, Finset.sum_insert hjnot]
      have hp := ih hij'
      have hn := hN j
      omega

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual selected subdiagonal retains the literal selected endpoint distance. -/
theorem originalHessenbergDistance_subdiagonal {n : ℕ} (P : Profile n)
    (k : Fin (originalSelectedCount (hD := hD) P)) :
    originalHessenbergDistance (hD := hD) P k.succ k.castSucc = (c.top : ℤ) := by
  unfold originalHessenbergDistance
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  exact c.originalSelected_endpoint_distance P (originalSelectedEnumeration P k)

/-- Actual upper tops are sums of their literal diagonal increments over the full window.
No distinct-value count replaces repeated original selected occurrences. -/
theorem originalHessenbergDistance_interval_sum {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j) :
    originalHessenbergDistance (hD := hD) P i j = (c.top : ℤ) +
      ∑ k ∈ Finset.Icc i j, (originalHessenbergDistance (hD := hD) P k k - (c.top : ℤ)) := by
  exact hessenberg_distance_interval_sum
    (fun k => P.xi (originalRowSplitEquiv (hD := hD) P (.inl (originalHessenbergRows P k))))
    (fun k => P.zeta (originalColSplitEquiv (hD := hD) P (.inl (originalHessenbergCols P k))))
    (c.top : ℤ) (fun k => c.originalHessenbergDistance_subdiagonal P k) i j hij

include c

/-- Extending an actual upper window gains strictly positive distance. Positivity is
derived from the actual selected geometry, not supplied as a condition on formal weights. -/
theorem originalHessenbergDistance_lt_of_strict_window {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i u v j : Fin (originalSelectedCount (hD := hD) P + 1))
    (hiu : i ≤ u) (huv : u ≤ v) (hvj : v ≤ j) (hstrict : i < u ∨ v < j) :
    originalHessenbergDistance (hD := hD) P u v <
      originalHessenbergDistance (hD := hD) P i j := by
  classical
  rw [c.originalHessenbergDistance_interval_sum P u v huv,
    c.originalHessenbergDistance_interval_sum P i j (hiu.trans (huv.trans hvj))]
  apply add_lt_add_right
  have hsub : Finset.Icc u v ⊆ Finset.Icc i j := by
    intro k hk
    obtain ⟨huk, hkv⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hiu.trans huk, hkv.trans hvj⟩
  have hpos (k : Fin (originalSelectedCount (hD := hD) P + 1)) :
      0 < originalHessenbergDistance (hD := hD) P k k - (c.top : ℤ) := by
    have h := c.originalHessenbergDistance_gt_top P hB k k le_rfl
    omega
  rcases hstrict with hi | hj
  · apply Finset.sum_lt_sum_of_subset hsub
      (Finset.mem_Icc.mpr ⟨le_rfl, hiu.trans (huv.trans hvj)⟩)
      (show i ∉ Finset.Icc u v by
        intro h
        exact (not_le_of_gt hi) (Finset.mem_Icc.mp h).1) (hpos i)
    intro k _ _
    exact (hpos k).le
  · apply Finset.sum_lt_sum_of_subset hsub
      (Finset.mem_Icc.mpr ⟨hiu.trans (huv.trans hvj), le_rfl⟩)
      (show j ∉ Finset.Icc u v by
        intro h
        exact (not_le_of_gt hj) (Finset.mem_Icc.mp h).2) (hpos j)
    intro k _ _
    exact (hpos k).le

/-- Bounds on all intervals of one fixed cost produce every shorter distance bound.
The extension is constructed in the actual finite ordered state set, including either end. -/
theorem originalHessenbergDistance_short_of_length_bound {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (m : ℕ) (hm : m ≤ originalSelectedCount (hD := hD) P) (K : ℤ)
    (hbound : ∀ u v : Fin (originalSelectedCount (hD := hD) P + 1),
      u ≤ v → (v : ℕ) - (u : ℕ) = m →
      originalHessenbergDistance (hD := hD) P u v ≤ K)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1))
    (hij : i ≤ j) (hshort : (j : ℕ) - (i : ℕ) < m) :
    originalHessenbergDistance (hD := hD) P i j < K := by
  let u : Fin (originalSelectedCount (hD := hD) P + 1) :=
    ⟨min i.val (originalSelectedCount (hD := hD) P - m),
      (Nat.min_le_left _ _).trans_lt i.isLt⟩
  let v : Fin (originalSelectedCount (hD := hD) P + 1) :=
    ⟨u.val + m, by dsimp [u]; omega⟩
  have hui : u ≤ i := by change u.val ≤ i.val; dsimp [u]; omega
  have hjv : j ≤ v := by
    change j.val ≤ v.val
    change i.val ≤ j.val at hij
    dsimp [u, v]
    have := j.isLt
    omega
  have huv : u ≤ v := hui.trans (hij.trans hjv)
  have hstrict : u < i ∨ j < v := by
    change u.val < i.val ∨ j.val < v.val
    change i.val ≤ j.val at hij
    dsimp [u, v]
    omega
  have hlen : (v : ℕ) - (u : ℕ) = m := by
    dsimp [v]
    omega
  exact (c.originalHessenbergDistance_lt_of_strict_window P hB u i j v hui hij hjv
    hstrict).trans_le (hbound u v huv hlen)

end SelectedCoordinate
end SkewCornerDescent.Matrix
