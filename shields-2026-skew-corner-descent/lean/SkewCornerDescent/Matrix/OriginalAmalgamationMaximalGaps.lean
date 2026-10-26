/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationGaps
import SkewCornerDescent.Matrix.OriginalWindowPeriodDistance
import SkewCornerDescent.Matrix.OriginalClosureGapPeriod

/-!
# Maximal-bin bounds inherited by the literal amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Internal
full-period windows have the literal displacement sum. Windows meeting the true
closure position are complete source windows, with every cap retained. No cyclic
period of the source or amalgamation is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At the full internal period, every completed union gap window is bounded by
the source maximum or by the literal period displacement. -/
theorem originalAmalgamation_completed_gap_bound {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u w : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate w W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) A)]
    (j : ℕ) (hj : 0 < j)
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (M : ℤ) (hqM : q ≤ M)
    (hbound : ∀ z : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j z ≤ M)
    (z : ZMod (originalSelectedCount (hD := hD) A)) :
    windowSum (fun s => c.originalCompletedGap A ((ZMod.finEquiv _).symm s)) 1 j z ≤ M := by
  classical
  have hjB : j ≤ originalSelectedCount (hD := hD) P := by
    rw [hjlen]
    exact Nat.sub_le _ _
  obtain ⟨hcount, hinventory, hword⟩ := c.originalAmalgamation_completed_gap_word P W A q
    v u w hq hv hwindow hW hA hcutq hcutLq hC
  have hBA : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + j := by omega
  obtain ⟨hleft, hright⟩ := originalAmalgamation_complete_end_windows P A q v u
    hq hv hwindow hA
  have hlower : A.cells.filter (fun x => 0 ≤ content x ∧ content x < A.xi 0 - q) =
      translate (-u) P.cells := by
    apply translate_injective u
    rw [hleft, translate_translate, add_neg_cancel, translate_zero]
  have hupper : A.cells.filter (fun x => q ≤ content x ∧ content x < A.xi 0) =
      translate v (A.cells.filter fun x => 0 ≤ content x ∧ content x < A.xi 0 - q) := by
    apply translate_injective u
    rw [hright, translate_translate, add_comm u v, ← translate_translate, hleft]
  have hcuts := originalAmalgamation_private_end_cuts P A q v u
    hq hv hwindow hA hcutq hcutLq
  have hzlt := ZMod.val_lt z
  by_cases hnoncross : z.val + j < originalSelectedCount (hD := hD) A
  · let i : Fin (originalSelectedCount (hD := hD) A) := ⟨z.val, hzlt⟩
    let k : Fin (originalSelectedCount (hD := hD) A) := ⟨z.val + j - 1, by omega⟩
    let last : Fin (originalSelectedCount (hD := hD) A) := ⟨z.val + j, hnoncross⟩
    have hdist := c.originalWindow_selected_period_distance A P q (-u) v hv hlower hupper
      (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.1)
      i last (by dsimp only [i, last]; omega)
    have he := c.originalCompletedGap_cyclic_internal_window A i k
      (by change z.val ≤ z.val + j - 1; omega)
      (by change z.val + j - 1 + 1 < originalSelectedCount (hD := hD) A; omega)
    have hk : k.succ = last.castSucc := by
      apply Fin.ext
      change z.val + j - 1 + 1 = z.val + j
      omega
    have hlen : k.val - i.val + 1 = j := by dsimp only [i, k]; omega
    rw [hk, hlen] at he
    have hiz : (i.val : ZMod (originalSelectedCount (hD := hD) A)) = z :=
      ZMod.natCast_zmod_val z
    rw [hiz, hdist] at he
    have hsum : windowSum (fun s => c.originalCompletedGap A ((ZMod.finEquiv _).symm s))
        1 j z = q := (add_left_cancel he).symm
    rw [hsum]
    exact hqM
  · have hcross : originalSelectedCount (hD := hD) P ≤ z.val := by omega
    have hwindoweq : windowSum
        (fun s => c.originalCompletedGap A ((ZMod.finEquiv _).symm s)) 1 j z =
        windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j
          ((z.val - j : ℕ) : ZMod (originalSelectedCount (hD := hD) P)) := by
      unfold windowSum
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      dsimp only
      have hzcast : z + a • 1 = ((z.val + a : ℕ) : ZMod (originalSelectedCount (hD := hD) A)) := by
        simp only [Nat.cast_add, ZMod.natCast_zmod_val, nsmul_eq_mul, mul_one]
      have hscast : ((z.val - j : ℕ) : ZMod (originalSelectedCount (hD := hD) P)) + a • 1 =
          ((z.val - j + a : ℕ) : ZMod (originalSelectedCount (hD := hD) P)) := by
        simp only [Nat.cast_add, nsmul_eq_mul, mul_one]
      rw [hzcast, hscast, hword]
      have hvalA := finEquiv_symm_val ((z.val + a : ℕ) : ZMod (originalSelectedCount (hD := hD) A))
      have hvalP := finEquiv_symm_val
        ((z.val - j + a : ℕ) : ZMod (originalSelectedCount (hD := hD) P))
      simp only [ZMod.val_natCast] at hvalA hvalP
      by_cases hwrap : z.val + a < originalSelectedCount (hD := hD) A
      · have hAmod : (z.val + a) % originalSelectedCount (hD := hD) A = z.val + a :=
          Nat.mod_eq_of_lt hwrap
        have hPmod : (z.val - j + a) % originalSelectedCount (hD := hD) P = z.val - j + a :=
          Nat.mod_eq_of_lt (by omega)
        rw [dite_eq_right (by rw [hvalA, hAmod]; omega)]
        congr 1
        apply Fin.ext
        rw [hvalP, hPmod]
        change (((ZMod.finEquiv _).symm _).val - _) = _
        rw [hvalA, hAmod]
        omega
      · have hAmod : (z.val + a) % originalSelectedCount (hD := hD) A =
            z.val + a - originalSelectedCount (hD := hD) A := by
          have hsum : z.val + a = (z.val + a - originalSelectedCount (hD := hD) A) +
              originalSelectedCount (hD := hD) A := by omega
          rw [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
            Nat.mod_eq_of_lt (by omega)]
          omega
        have hPmod : (z.val - j + a) % originalSelectedCount (hD := hD) P =
            z.val + a - originalSelectedCount (hD := hD) A := by
          have hsum : z.val - j + a = (z.val + a - originalSelectedCount (hD := hD) A) +
              originalSelectedCount (hD := hD) P := by omega
          rw [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
            Nat.mod_eq_of_lt (by omega)]
        rw [dite_eq_left (by rw [hvalA, hAmod]; omega)]
        congr 1
        apply Fin.ext
        rw [hvalP, hPmod]
        change ((ZMod.finEquiv _).symm _).val = _
        rw [hvalA, hAmod]
    rw [hwindoweq]
    exact hbound _

end SkewCornerDescent.Matrix.SelectedCoordinate
