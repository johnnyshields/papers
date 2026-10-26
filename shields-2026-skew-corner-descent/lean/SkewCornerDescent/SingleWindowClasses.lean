/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TriangularClassCounts

/-!
# Balanced classes in a single full window

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). Coprimality forces the numerator count
of a balanced class to be a multiple of the outer row count. A single full window
has fewer response occurrences than that count, so the class is absent on both sides.

Sorry-free.
-/

namespace SkewCornerDescent

/-- A full response class cannot have more occurrences than the response inventory. -/
theorem triangularClassCount_le {k σ ι : Type*} [Field k] [LinearOrder σ]
    (s : Finset ι) (J : ι → σ) (B : ι → MvPolynomial σ k) (T : MvPolynomial σ k) :
    triangularClassCount s J B T ≤ s.card := by
  classical
  exact Finset.card_filter_le _ _

/-- Every retained occurrence contributes positively to its own full response class. -/
theorem triangularClassCount_pos_of_mem {k σ ι : Type*} [Field k] [LinearOrder σ]
    (s : Finset ι) (J : ι → σ) (B : ι → MvPolynomial σ k) {i : ι} (hi : i ∈ s) :
    0 < triangularClassCount s J B (MvPolynomial.X (J i) + B i) := by
  classical
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, Associated.refl _⟩⟩

/-- Coprime exponents force every balanced single-window class to have zero occurrences. -/
theorem singleWindow_balanced_class_empty {k σ ι κ : Type*} [Field k] [LinearOrder σ]
    (s : Finset ι) (t : Finset κ) (J : ι → σ) (B : ι → MvPolynomial σ k)
    (L : κ → σ) (D : κ → MvPolynomial σ k) (T : MvPolynomial σ k)
    (v b : ℕ) (hcop : b.Coprime v) (hs : s.card + 1 = b)
    (hbalance : v * triangularClassCount s J B T = b * triangularClassCount t L D T) :
    triangularClassCount s J B T = 0 ∧ triangularClassCount t L D T = 0 := by
  have hdiv : b ∣ v * triangularClassCount s J B T := by
    rw [hbalance]
    exact dvd_mul_right _ _
  have hx0 := Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_left hdiv)
    (show triangularClassCount s J B T < b by
      have hle := triangularClassCount_le s J B T
      omega)
  have hb0 : b ≠ 0 := by omega
  rw [hx0, mul_zero] at hbalance
  exact ⟨hx0, (mul_eq_zero.mp hbalance.symm).resolve_left hb0⟩

end SkewCornerDescent
