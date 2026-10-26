/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOrdinaryBetaSpan

/-!
# Exact content of the produced ordinary literal period

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every selected period step uses genuine finite closure states. Their beta
differences telescope across the actual two ordinary source copies.
The original full source span therefore fixes the produced translation’s
content to the negative root span, in either ordinary direction. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The physical original cell translation has exactly its retained endpoint beta shift. -/
theorem originalInternalCellShift_content {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) :
    content (originalInternalCellShift P i j) = originalInternalIntervalShift P i j := by
  unfold originalInternalCellShift content
  ring

private theorem finite_steps_total (b : ℕ) (f : Fin (b + 1) → ℤ) (h : ℤ)
    (hs : ∀ k : Fin b, f k.succ - f k.castSucc = h) :
    f (Fin.last b) - f 0 = (b : ℤ)*h := by
  have hsum : (∑ k : Fin b, (f k.succ - f k.castSucc)) = (b : ℤ)*h := by
    simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hleft := Fin.sum_univ_succ f
  have hright := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib] at hsum
  omega

/-- A produced fixed ordinary phase translation has exactly the negative root-span content. -/
theorem originalOrdinaryClosure_period_content {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    (b r : ℕ) (hb : 2 ≤ b) [NeZero r]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (δ : ℤ) (hspan : P.xi 0 = (b : ℤ) * δ) (v : ℤ × ℤ)
    (hfixed : ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val+r →
      originalInternalCellShift Q i j = v) : content v = -δ := by
  obtain ⟨hCQ, hcopy⟩ := originalOrdinaryClosure_selected_beta_copy_span (hD := hD) P Q z hQ
  have hsource : 0 < originalSelectedCount (hD := hD) P := by
    rw [hB]
    exact Nat.mul_pos (by omega) (NeZero.pos r)
  have htwo : 2 ≤ originalSelectedCount (hD := hD) P := by
    rw [hB]
    nlinarith [NeZero.pos r, Nat.mul_le_mul_right r hb]
  let f : Fin (b+1) → ℤ := fun k => originalSelectedSourceBeta Q ⟨k.val*r, by
    have hk : k.val ≤ b := by have := k.isLt; omega
    have hm := Nat.mul_le_mul_right r hk
    rw [← hB] at hm
    omega⟩
  have hstep (k : Fin b) : f k.succ - f k.castSucc = content v := by
    have hik : k.val*r < originalSelectedCount (hD := hD) P := by
      rw [hB]
      exact Nat.mul_lt_mul_of_pos_right k.isLt (NeZero.pos r)
    have hjk : (k.val+1)*r ≤ originalSelectedCount (hD := hD) P := by
      rw [hB]
      exact Nat.mul_le_mul_right r (Nat.succ_le_of_lt k.isLt)
    let i : Fin (originalSelectedCount (hD := hD) Q - 1) := ⟨k.val*r, by omega⟩
    let j : Fin (originalSelectedCount (hD := hD) Q - 1) := ⟨(k.val+1)*r, by omega⟩
    have hij : j.val = i.val+r := by
      dsimp only [i,j]
      simp only [Nat.add_mul, Nat.one_mul]
    have hh := congrArg content (hfixed i j hij)
    rw [originalInternalCellShift_content, originalInternalIntervalShift_eq_beta] at hh
    exact hh
  have htotal := finite_steps_total b f (content v) hstep
  have hcopies : f (Fin.last b) = f 0 - P.xi 0 := by
    have hh := hcopy ⟨0,hsource⟩
    simpa only [f, Fin.val_last, Fin.val_zero, zero_mul, add_zero, ← hB] using hh
  apply mul_left_cancel₀ (show (b : ℤ) ≠ 0 by omega)
  calc
    (b : ℤ) * content v = f (Fin.last b) - f 0 := htotal.symm
    _ = -P.xi 0 := by rw [hcopies]; ring
    _ = (b : ℤ)*(-δ) := by rw [hspan]; ring

end SkewCornerDescent.Matrix.SelectedCoordinate
