/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCoreWords
import SkewCornerDescent.Matrix.SelectedCoreSeries

/-!
# Full proper-core equality from actual low phase jets

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Actual proper cores have degree below the selected span. The supplied low-jet
period therefore identifies their full polynomials along every bounded period
chain, including both private-cut boundaries. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every bounded chain of actual phase steps identifies both full proper cores.
The coefficients outside the low jet vanish by the actual core construction. -/
theorem originalSelectedCore_phase_chain {n : ℕ} (P : Profile n) (r : ℕ)
    (hstep : ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
      ∀ k, k < (c.top : ℕ) →
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k =
          (c.originalSelectedCoreRight P i).coeff k)
    (m : ℕ) : ∀ i j : Fin (originalSelectedCount (hD := hD) P),
      j.val = i.val + r * m →
      c.originalSelectedCoreLeft P j = c.originalSelectedCoreLeft P i ∧
        c.originalSelectedCoreRight P j = c.originalSelectedCoreRight P i := by
  have step (i j : Fin (originalSelectedCount (hD := hD) P)) (h : j.val = i.val + r) :
      c.originalSelectedCoreLeft P j = c.originalSelectedCoreLeft P i ∧
        c.originalSelectedCoreRight P j = c.originalSelectedCoreRight P i := by
    constructor
    · ext k
      by_cases hk : k < (c.top : ℕ)
      · exact (hstep i j h k hk).1
      · unfold originalSelectedCoreLeft
        rw [c.selected_core_left_coeff_of_top_le _ _ k (not_lt.mp hk),
          c.selected_core_left_coeff_of_top_le _ _ k (not_lt.mp hk)]
    · ext k
      by_cases hk : k < (c.top : ℕ)
      · exact (hstep i j h k hk).2
      · unfold originalSelectedCoreRight
        rw [c.selected_core_right_coeff_of_top_le _ _ k (not_lt.mp hk),
          c.selected_core_right_coeff_of_top_le _ _ k (not_lt.mp hk)]
  induction m with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst j
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro i j h
    have hle : i.val + r * m ≤ j.val := by rw [h, Nat.mul_succ]; omega
    let k : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨i.val + r * m, lt_of_le_of_lt hle j.isLt⟩
    have hki := ih i k rfl
    have hjk := step k j (by dsimp only [k]; rw [h, Nat.mul_succ]; omega)
    exact ⟨hjk.1.trans hki.1, hjk.2.trans hki.2⟩

/-- At any nontrivial period boundary, the left core equals the last core and
 the right core equals the first core. This covers both complementary cuts. -/
theorem originalSelectedCore_private_boundary {n : ℕ} (P : Profile n)
    (r b a : ℕ) (hr : 0 < r) (ha : 0 < a) (hab : a < b)
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hstep : ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
      ∀ k, k < (c.top : ℕ) →
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k =
          (c.originalSelectedCoreRight P i).coeff k)
    (left right first last : Fin (originalSelectedCount (hD := hD) P))
    (hleft : left.val = r * a - 1) (hright : right.val = r * a)
    (hfirst : first.val = 0) (hlast : last.val = originalSelectedCount (hD := hD) P - 1) :
    c.originalSelectedCoreLeft P left = c.originalSelectedCoreLeft P last ∧
      c.originalSelectedCoreRight P right = c.originalSelectedCoreRight P first := by
  have hsplit : r * a + r * (b - a) = r * b := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hab.le]
  have hpos : 0 < r * a := Nat.mul_pos hr ha
  have hlaststep : last.val = left.val + r * (b - a) := by
    omega
  exact ⟨(c.originalSelectedCore_phase_chain P r hstep (b - a) left last hlaststep).1.symm,
    (c.originalSelectedCore_phase_chain P r hstep a first right (by
      rw [hfirst, hright, Nat.zero_add])).2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
