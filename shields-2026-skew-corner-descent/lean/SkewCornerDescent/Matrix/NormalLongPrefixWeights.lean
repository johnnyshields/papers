/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalPrefixChargeFactorization

/-!
# Full extra-state inverse products at actual prefix starts

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Finite residue periods factor the full inverse window product. The extra
state contributes its actual first inverse letter, with zero letters and
repeated wraps permitted and no derivative or inverse-jet assumption. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open scoped BigOperators

/-- The complete extra-state interval has the uniform full-period inverse
product times its actual first diagonal inverse. No inverse jet is frozen. -/
theorem normalLongPrefixCharge_residue_factor {N T r : ℕ} {F : Type*} [Field F]
    [NeZero T] [NeZero r]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F))
    (δ : PowerSeries F → PowerSeries F) (l k : ℕ)
    (hk : 0 < k) (hlen : l + 1 = k * r) (hT : T ≤ N - (l + 1))
    (hres : ∀ i j : Fin N, j.val = i.val + r →
      PowerSeries.constantCoeff (M i i) = PowerSeries.constantCoeff (M j j)) :
    let hrN : r ≤ N := by
      have ht := NeZero.pos T
      have hnr : l + 1 ≤ N := by omega
      nlinarith
    let Z := (∏ i : Fin r, (PowerSeries.constantCoeff
      (M ⟨i.val, i.isLt.trans_le hrN⟩ ⟨i.val, i.isLt.trans_le hrN⟩))⁻¹)^k
    normalLongPrefixCharge M δ l T hT = Z *
      ∑ s : Fin T, PowerSeries.constantCoeff (δ
        (M ⟨s.val, by have := s.isLt; omega⟩
          ⟨s.val + l + 1, by have := s.isLt; omega⟩)) *
        (PowerSeries.constantCoeff
          (M ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩))⁻¹ := by
  have ht := NeZero.pos T
  have hrN : r ≤ N := by
    have hnr : l + 1 ≤ N := by omega
    nlinarith
  let w := fun i : Fin N => (PowerSeries.constantCoeff (M i i))⁻¹
  let Z := (∏ i : Fin r, w ⟨i.val, i.isLt.trans_le hrN⟩)^k
  have hpw : ∀ i j : Fin N, j.val = i.val + r → w i = w j := by
    intro i j hij
    exact congrArg Inv.inv (hres i j hij)
  have hprod (s : Fin T) :
      (∏ i : Fin (l + 2), w ⟨s.val + i.val, by have := s.isLt; have := i.isLt; omega⟩) =
        Z * w ⟨s.val, by have := s.isLt; omega⟩ := by
    have hb : s.val + (k * r + 1) ≤ N := by have := s.isLt; omega
    have he := finite_periodic_window_product_succ w hrN hpw k s.val hb
    have heq : (∏ i : Fin (l + 2), w ⟨s.val + i.val,
        by have := s.isLt; have := i.isLt; omega⟩) =
        ∏ i : Fin (k * r + 1), w ⟨s.val + i.val, by have := i.isLt; omega⟩ := by
      apply Fintype.prod_equiv (finCongr (show l + 2 = k * r + 1 by omega))
      intro i
      rfl
    exact heq.trans he
  dsimp only [normalLongPrefixCharge]
  change (∑ s : Fin T, PowerSeries.constantCoeff (δ
    (M ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val + l + 1, by have := s.isLt; omega⟩)) *
      ∏ i : Fin (l + 2), w ⟨s.val + i.val, by have := s.isLt; have := i.isLt; omega⟩) =
    Z * ∑ s : Fin T, PowerSeries.constantCoeff (δ
      (M ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val + l + 1, by have := s.isLt; omega⟩)) *
      w ⟨s.val, by have := s.isLt; omega⟩
  simp_rw [hprod]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

end SkewCornerDescent.Matrix
