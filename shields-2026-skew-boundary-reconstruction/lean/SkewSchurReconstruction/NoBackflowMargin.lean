/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.FirstSplit

/-!
# Quantitative square-weight no-backflow

Formalizes the quantitative part of "First-split localization and cap-fixed rigidity"
(`sec:localization`, `thm:no-backflow`, `eq:no-backflow-margin`).
Actual parent increments telescope to the stated index margin; the finite first-split
anchor and the actual defect comparison then give the bound in `WithTop` without
subtracting infinite costs.  Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

variable {n : ℕ}

private theorem square_weight_int (a : ℤ) (ha : 0 ≤ a) :
    squareWeight.weight a.toNat = (a : ℝ) ^ 2 := by
  have he : (a.toNat : ℤ) = a := by omega
  have hr : (a.toNat : ℝ) = (a : ℝ) := by exact_mod_cast he
  change (a.toNat : ℝ) ^ 2 = _
  rw [hr]

/-- Antitonic outer boundaries give the quantitative integer row-grid separation. -/
theorem rowParam_sub_ge_index (X : Diagram n) (i k : Fin n) (hik : i ≤ k) :
    (k.val : ℤ) - i.val ≤ X.rowParam k - X.rowParam i := by
  have ho := X.outer_antitone hik
  unfold rowParam
  omega

/-- Strict integral cap grids have adjacent gaps of at least one. -/
theorem capShift_adjacent_gap (X : Diagram n) (k : Fin n) :
    1 ≤ X.capShift k.succ - X.capShift k.castSucc := by
  have h := X.capShift_strictMono (show k.castSucc < k.succ by
    change k.val < k.val + 1
    omega)
  omega

/-- The exact finite tilted-profile increment for the square weight. -/
theorem parentTiltedProfile_square_increment (X : Diagram n) (hX : X.Connected)
    (A : ℤ) (k : Fin n) (hA : A ≤ X.rowParam k) :
    parentTiltedProfile squareWeight X A k.succ -
      parentTiltedProfile squareWeight X A k.castSucc =
        2 * ((X.rowParam k : ℝ) - (A : ℝ)) *
          ((X.capShift k.succ : ℝ) - (X.capShift k.castSucc : ℝ)) := by
  have hdiag := X.diagonal_feasible hX k
  have hgrid := X.capShift_adjacent_gap k
  have h00 : 0 ≤ X.capShift k.castSucc - X.rowParam k := by omega
  have h01 : 0 ≤ X.capShift k.succ - X.rowParam k := by omega
  have h10 : 0 ≤ X.capShift k.castSucc - A := by omega
  have h11 : 0 ≤ X.capShift k.succ - A := by omega
  have hr := parentAction_recurrence squareWeight X hX k
  unfold parentAction at hr
  rw [square_weight_int _ h00, square_weight_int _ h01,
    square_weight_int _ (X.capShift_nonneg k.succ),
    square_weight_int _ (X.capShift_nonneg k.castSucc)] at hr
  unfold parentTiltedProfile
  rw [square_weight_int _ h10, square_weight_int _ h11]
  push_cast at hr ⊢
  nlinarith

/-- Every later square-weight parent step is bounded below by its index separation. -/
theorem parentTiltedProfile_square_step_bound (X : Diagram n) (hX : X.Connected)
    (i k : Fin n) (hik : i ≤ k) :
    2 * ((k.val : ℝ) - i.val) ≤
      parentTiltedProfile squareWeight X (X.rowParam i) k.succ -
        parentTiltedProfile squareWeight X (X.rowParam i) k.castSucc := by
  have hrow := X.rowParam_sub_ge_index i k hik
  have hgrid := X.capShift_adjacent_gap k
  have hidx : 0 ≤ (k.val : ℤ) - i.val := by
    have hv : i.val ≤ k.val := hik
    omega
  have hA : X.rowParam i ≤ X.rowParam k := by omega
  rw [parentTiltedProfile_square_increment X hX _ k hA]
  have hr : (k.val : ℝ) - i.val ≤ (X.rowParam k : ℝ) - X.rowParam i := by exact_mod_cast hrow
  have hg : (1 : ℝ) ≤ (X.capShift k.succ : ℝ) - X.capShift k.castSucc := by exact_mod_cast hgrid
  have hi : (0 : ℝ) ≤ (k.val : ℝ) - i.val := by exact_mod_cast hidx
  have hp := mul_nonneg (show 0 ≤ (X.rowParam k : ℝ) - X.rowParam i by linarith)
    (show 0 ≤ (X.capShift k.succ : ℝ) - X.capShift k.castSucc - 1 by linarith)
  nlinarith

/-- Telescoping actual parent profiles gives the closed index margin. -/
theorem parentTiltedProfile_square_margin (X : Diagram n) (hX : X.Connected)
    (i : Fin n) (q l : Fin (n + 1)) (hiq : i.val ≤ q.val) (hql : q ≤ l) :
    parentTiltedProfile squareWeight X (X.rowParam i) q +
      ((l.val : ℝ) - q.val) * ((l.val : ℝ) + q.val - 2 * i.val - 1) ≤
        parentTiltedProfile squareWeight X (X.rowParam i) l := by
  have hdist : ∀ t (ht : q.val + t < n + 1),
      parentTiltedProfile squareWeight X (X.rowParam i) q +
        (t : ℝ) * (2 * (q.val : ℝ) + t - 2 * i.val - 1) ≤
          parentTiltedProfile squareWeight X (X.rowParam i) ⟨q.val + t, ht⟩ := by
    intro t
    induction t with
    | zero =>
      intro ht
      simp
    | succ t ih =>
      intro ht
      have hprev : q.val + t < n + 1 := by omega
      let k : Fin n := ⟨q.val + t, by omega⟩
      have hik : i ≤ k := by change i.val ≤ q.val + t; omega
      have hs := parentTiltedProfile_square_step_bound X hX i k hik
      have he0 : k.castSucc = (⟨q.val + t, hprev⟩ : Fin (n + 1)) := rfl
      have he1 : k.succ = (⟨q.val + (t + 1), ht⟩ : Fin (n + 1)) := by
        apply Fin.ext
        change q.val + t + 1 = q.val + (t + 1)
        omega
      rw [he0, he1] at hs
      have hp := ih hprev
      dsimp [k] at hs
      push_cast at hs ⊢
      nlinarith
  have hv : q.val ≤ l.val := hql
  have hl := l.isLt
  have hbound : q.val + (l.val - q.val) < n + 1 := by omega
  have h := hdist (l.val - q.val) hbound
  have he : (⟨q.val + (l.val - q.val), hbound⟩ : Fin (n + 1)) = l := by
    apply Fin.ext
    change q.val + (l.val - q.val) = l.val
    omega
  rw [he] at h
  have hc : ((l.val - q.val : ℕ) : ℝ) = (l.val : ℝ) - q.val := by
    exact_mod_cast (show ((l.val - q.val : ℕ) : ℤ) = (l.val : ℤ) - q.val by omega)
  rw [hc] at h
  convert h using 1
  ring

/-- `eq:no-backflow-margin` for actual cofactor defects, including zero later coordinates. -/
theorem defect_no_backflow_square_margin (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ k : Fin n, k.val < v.val → X.rowParam k = Y.rowParam k)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (i : Fin n) (hiv : i < v) (l : Fin (n + 1)) (hvl : v.succ ≤ l) :
    defectTiltedCost squareWeight X Y (X.rowParam i) v.succ +
      ((((l.val : ℝ) - (v.val + 1)) *
        ((l.val : ℝ) + (v.val + 1) - 2 * i.val - 1) : ℝ) : WithTop ℝ) ≤
      defectTiltedCost squareWeight X Y (X.rowParam i) l := by
  have hi : i.val < v.val := hiv
  have hrow := hprefix i hi
  have hfeas : X.rowParam i ≤ X.capShift v.succ := by
    have hr := X.rowParam_strictMono hiv
    have hd := X.diagonal_feasible hX v
    have hc := X.capShift_adjacent_gap v
    omega
  have hfeasl : X.rowParam i ≤ X.capShift l :=
    hfeas.trans (X.capShift_strictMono.monotone hvl)
  have hx := parentTiltedProfile_square_margin X hX i v.succ l
    (by change i.val ≤ v.val + 1; omega) hvl
  have hy := parentTiltedProfile_square_margin Y hY i v.succ l
    (by change i.val ≤ v.val + 1; omega) hvl
  rw [← hrow] at hy
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at hx hy
  let B : ℝ := ((l.val : ℝ) - (v.val + 1)) *
    ((l.val : ℝ) + (v.val + 1) - 2 * i.val - 1)
  have hm : min (parentTiltedProfile squareWeight X (X.rowParam i) v.succ)
      (parentTiltedProfile squareWeight Y (X.rowParam i) v.succ) + B ≤
        min (parentTiltedProfile squareWeight X (X.rowParam i) l)
          (parentTiltedProfile squareWeight Y (X.rowParam i) l) := by
    apply le_min
    · have h := min_le_left (parentTiltedProfile squareWeight X (X.rowParam i) v.succ)
        (parentTiltedProfile squareWeight Y (X.rowParam i) v.succ)
      change _ + B ≤ _ at hx
      linarith
    · have h := min_le_right (parentTiltedProfile squareWeight X (X.rowParam i) v.succ)
        (parentTiltedProfile squareWeight Y (X.rowParam i) v.succ)
      change _ + B ≤ _ at hy
      linarith
  rw [first_split_tilted_anchor squareWeight X Y hX hY hgrid hrows v hprefix hchanged
    (X.rowParam i) hfeas, ← WithTop.coe_min, ← WithTop.coe_add]
  exact (WithTop.coe_le_coe.mpr hm).trans
    (defectTiltedCost_ge_parent_min squareWeight X Y hX hY hgrid (X.rowParam i) l hfeasl)

end Diagram
end SkewSchurReconstruction
