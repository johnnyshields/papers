/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CofactorActions

/-!
# First-split localization

Formalizes “First-split localization” (`subsec:first-split`) in
“First-split localization and cap-fixed rigidity” (`sec:localization`):
`prop:synchronization` and `cor:first-split-anchor`.  Actions are obtained
from the actual signed cofactor determinants through `CofactorActions`.
Zero defect coordinates and infeasible tilted entries retain infinite cost.
The parent tilted increment and qualitative no-backflow are derived from
actual actions (`lem:tail-increase`, `thm:no-backflow`).  The quantitative
square-weight margin is not asserted.
Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

variable {n : ℕ}

/-- Row lengths with multiplicity, rather than the set of distinct row lengths. -/
def rowLengthMultiset (X : Diagram n) : Multiset ℕ :=
  Finset.univ.val.map X.rowLength

theorem parentAction_zero_eq_of_rowLengths (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset) :
    parentAction w X 0 = parentAction w Y 0 := by
  rw [parentAction_zero w X hX, parentAction_zero w Y hY]
  have he := congrArg (fun s : Multiset ℕ => (s.map w.weight).sum) hrows
  simpa only [rowLengthMultiset, Multiset.map_map, Finset.sum_eq_multiset_sum,
    Function.comp_def] using he

/-- Actual normalized actions synchronize through every unchanged row. -/
theorem parentAction_synchronized (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (j : Fin (n + 1)) (hj : j.val ≤ v.val) :
    parentAction w X j = parentAction w Y j := by
  have hall : ∀ k (hk : k < n + 1), k ≤ v.val →
      parentAction w X ⟨k, hk⟩ = parentAction w Y ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk _
      exact parentAction_zero_eq_of_rowLengths w X Y hX hY hrows
    | succ k ih =>
      intro hk hkv
      let r : Fin n := ⟨k, by omega⟩
      have hr : r.val < v.val := by dsimp [r]; omega
      have hprev : parentAction w X r.castSucc = parentAction w Y r.castSucc :=
        ih (by omega) (by omega)
      have hx := parentAction_recurrence w X hX r
      have hy := parentAction_recurrence w Y hY r
      rw [← hgrid r.castSucc, ← hgrid r.succ, ← hprefix r hr] at hy
      change parentAction w X r.succ = parentAction w Y r.succ
      linarith
  exact hall j.val j.isLt hj

/-- The first strict action split has the direction of the changed row parameter,
for every admissible convex weight. -/
theorem parentAction_first_split_lt (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v < Y.rowParam v) :
    parentAction w X v.succ < parentAction w Y v.succ := by
  have hprev := parentAction_synchronized w X Y hX hY hgrid hrows v hprefix
    v.castSucc (by rfl)
  have hx := parentAction_recurrence w X hX v
  have hy := parentAction_recurrence w Y hY v
  rw [← hgrid v.castSucc, ← hgrid v.succ] at hy
  have hfeas : Y.rowParam v ≤ X.capShift v.castSucc := by
    rw [hgrid]
    exact Y.diagonal_feasible hY v
  have hd : X.capShift v.castSucc < X.capShift v.succ :=
    X.capShift_strictMono (by change v.val < v.val + 1; omega)
  have hm := w.strict_monge_int hchanged hd hfeas
  linarith

theorem parentAction_first_split_ne (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    parentAction w X v.succ ≠ parentAction w Y v.succ := by
  rcases lt_or_gt_of_ne hchanged with hlt | hgt
  · exact (parentAction_first_split_lt w X Y hX hY hgrid hrows v hprefix hlt).ne
  · exact (parentAction_first_split_lt w Y X hY hX (fun j => (hgrid j).symm)
      hrows.symm v (fun i hi => (hprefix i hi).symm) hgt).ne'

/-- The actual signed cofactor defect `eq:defect`. -/
noncomputable def cofactorDefect (X Y : Diagram n) (j : Fin (n + 1)) : CompleteRing :=
  X.cofactor j - Y.cofactor j

/-- Normalized defect action; zero polynomials have infinite action. -/
noncomputable def defectAction (w : ConvexWeight) (X Y : Diagram n)
    (j : Fin (n + 1)) : WithTop ℝ :=
  monomialValuation w.generatorWeight (cofactorDefect X Y j) +
    (w.weight (X.capShift j).toNat : WithTop ℝ)

/-- The tilted cost `eq:F-general`, with infinity for an infeasible matrix entry. -/
noncomputable def defectTiltedCost (w : ConvexWeight) (X Y : Diagram n)
    (A : ℤ) (j : Fin (n + 1)) : WithTop ℝ :=
  if A ≤ X.capShift j then
    monomialValuation w.generatorWeight (cofactorDefect X Y j) +
      (w.weight (X.capShift j - A).toNat : WithTop ℝ)
  else ⊤

@[simp] theorem defectAction_eq_top_iff (w : ConvexWeight) (X Y : Diagram n)
    (j : Fin (n + 1)) : defectAction w X Y j = ⊤ ↔ cofactorDefect X Y j = 0 := by
  simp [defectAction, monomialValuation_eq_top_iff]

theorem defectTiltedCost_eq_top_of_infeasible (w : ConvexWeight) (X Y : Diagram n)
    (A : ℤ) (j : Fin (n + 1)) (hj : X.capShift j < A) :
    defectTiltedCost w X Y A j = ⊤ := by
  simp [defectTiltedCost, not_le.mpr hj]

theorem defectTiltedCost_eq_top_of_zero (w : ConvexWeight) (X Y : Diagram n)
    (A : ℤ) (j : Fin (n + 1)) (hj : cofactorDefect X Y j = 0) :
    defectTiltedCost w X Y A j = ⊤ := by
  simp [defectTiltedCost, hj]

/-- Noncancellation at the first split, derived from actual parent actions. -/
theorem first_split_valuation (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    monomialValuation w.generatorWeight (cofactorDefect X Y v.succ) =
      (min (leastWeight w.generatorWeight (X.cofactor v.succ))
        (leastWeight w.generatorWeight (Y.cofactor v.succ)) : WithTop ℝ) := by
  have haction := parentAction_first_split_ne w X Y hX hY hgrid hrows v hprefix hchanged
  have hne : monomialValuation w.generatorWeight (X.cofactor v.succ) ≠
      monomialValuation w.generatorWeight (Y.cofactor v.succ) := by
    intro he
    rw [monomialValuation_eq_coe (X.cofactor_ne_zero w hX v.succ),
      monomialValuation_eq_coe (Y.cofactor_ne_zero w hY v.succ)] at he
    have hl := WithTop.coe_injective he
    apply haction
    unfold parentAction
    rw [hl, hgrid]
  unfold cofactorDefect
  rw [monomialValuation_sub_eq_min hne,
    monomialValuation_eq_coe (X.cofactor_ne_zero w hX v.succ),
    monomialValuation_eq_coe (Y.cofactor_ne_zero w hY v.succ)]

/-- The nonzero coordinate and exact normalized minimum in `cor:first-split-anchor`. -/
theorem first_split_anchor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) :
    cofactorDefect X Y v.succ ≠ 0 ∧
      defectAction w X Y v.succ =
        (min (parentAction w X v.succ) (parentAction w Y v.succ) : WithTop ℝ) := by
  have hv := first_split_valuation w X Y hX hY hgrid hrows v hprefix hchanged
  constructor
  · intro hz
    rw [hz, monomialValuation_zero] at hv
    have hn :
        (min (leastWeight w.generatorWeight (X.cofactor v.succ))
          (leastWeight w.generatorWeight (Y.cofactor v.succ)) : WithTop ℝ) ≠ ⊤ :=
      WithTop.coe_ne_top
    exact hn hv.symm
  · unfold defectAction
    rw [hv]
    simp only [← WithTop.coe_min, ← WithTop.coe_add]
    congr 1
    unfold parentAction
    rw [← hgrid v.succ]
    exact (min_add_add_right _ _ _).symm

/-- Finite parent tilted profile, equal to `eq:F-parent` on feasible entries. -/
noncomputable def parentTiltedProfile (w : ConvexWeight) (X : Diagram n)
    (A : ℤ) (j : Fin (n + 1)) : ℝ :=
  leastWeight w.generatorWeight (X.cofactor j) + w.weight (X.capShift j - A).toNat

theorem parentTiltedProfile_eq_action (w : ConvexWeight) (X : Diagram n)
    (A : ℤ) (j : Fin (n + 1)) :
    parentTiltedProfile w X A j = parentAction w X j +
      w.weight (X.capShift j - A).toNat - w.weight (X.capShift j).toNat := by
  unfold parentTiltedProfile parentAction
  ring

/-- Strict positive parent tilted increment from the actual action recurrence and
connected diagonal feasibility, the local step of `lem:tail-increase`. -/
theorem parentTiltedProfile_step_lt (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (A : ℤ) (k : Fin n) (hA : A < X.rowParam k) :
    parentTiltedProfile w X A k.castSucc < parentTiltedProfile w X A k.succ := by
  have hr := parentAction_recurrence w X hX k
  have hm := w.strict_monge_int hA
    (X.capShift_strictMono
      (show k.castSucc < k.succ from by change k.val < k.val + 1; omega))
    (X.diagonal_feasible hX k)
  unfold parentAction at hr
  unfold parentTiltedProfile
  linarith

private theorem fin_tail_strict (f : Fin (n + 1) → ℝ) (q l : Fin (n + 1))
    (hstep : ∀ k : Fin n, q.val ≤ k.val → f k.castSucc < f k.succ)
    (hql : q < l) : f q < f l := by
  have hdist : ∀ t (ht : q.val + t < n + 1),
      f q ≤ f ⟨q.val + t, ht⟩ ∧
        (0 < t → f q < f ⟨q.val + t, ht⟩) := by
    intro t
    induction t with
    | zero =>
      intro ht
      have he : (⟨q.val + 0, ht⟩ : Fin (n + 1)) = q := by
        apply Fin.ext
        change q.val + 0 = q.val
        omega
      rw [he]
      exact ⟨le_rfl, by omega⟩
    | succ t ih =>
      intro ht
      have ht' : q.val + t < n + 1 := by omega
      let k : Fin n := ⟨q.val + t, by omega⟩
      have hnext := hstep k (by dsimp [k]; omega)
      have he₀ : k.castSucc = (⟨q.val + t, ht'⟩ : Fin (n + 1)) := rfl
      have he₁ : k.succ = (⟨q.val + (t + 1), ht⟩ : Fin (n + 1)) := by
        apply Fin.ext
        change q.val + t + 1 = q.val + (t + 1)
        omega
      rw [he₀, he₁] at hnext
      have hl := lt_of_le_of_lt (ih ht').1 hnext
      exact ⟨hl.le, fun _ => hl⟩
  have ht : q.val + (l.val - q.val) < n + 1 := by
    have := l.isLt
    change q.val < l.val at hql
    omega
  have hl := (hdist (l.val - q.val) ht).2 (by
    change q.val < l.val at hql
    omega)
  have he : (⟨q.val + (l.val - q.val), ht⟩ : Fin (n + 1)) = l := by
    apply Fin.ext
    change q.val + (l.val - q.val) = l.val
    change q.val < l.val at hql
    omega
  simpa only [he] using hl

/-- A common-prefix parent's tilted profile increases strictly beyond the split. -/
theorem parentTiltedProfile_after_split_lt (w : ConvexWeight) (X : Diagram n)
    (hX : X.Connected) (i v : Fin n) (hiv : i < v)
    (l : Fin (n + 1)) (hvl : v.succ < l) :
    parentTiltedProfile w X (X.rowParam i) v.succ <
      parentTiltedProfile w X (X.rowParam i) l := by
  apply fin_tail_strict _ v.succ l _ hvl
  intro k hk
  apply parentTiltedProfile_step_lt w X hX
  apply X.rowParam_strictMono
  change i.val < k.val
  change i.val < v.val at hiv
  change v.val + 1 ≤ k.val at hk
  omega

/-- Cancellation only raises a feasible defect tilted cost above the lesser parent profile. -/
theorem defectTiltedCost_ge_parent_min (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (A : ℤ) (j : Fin (n + 1)) (hj : A ≤ X.capShift j) :
    (min (parentTiltedProfile w X A j) (parentTiltedProfile w Y A j) : WithTop ℝ) ≤
      defectTiltedCost w X Y A j := by
  have hv := monomialValuation_sub_ge w.generatorWeight (X.cofactor j) (Y.cofactor j)
  rw [monomialValuation_eq_coe (X.cofactor_ne_zero w hX j),
    monomialValuation_eq_coe (Y.cofactor_ne_zero w hY j)] at hv
  have hc := add_le_add_right hv (w.weight (X.capShift j - A).toNat : WithTop ℝ)
  unfold parentTiltedProfile defectTiltedCost
  rw [ite_eq_left hj]
  change _ ≤ monomialValuation w.generatorWeight (X.cofactor j - Y.cofactor j) +
    (w.weight (X.capShift j - A).toNat : WithTop ℝ)
  rw [← hgrid j]
  simpa only [min_add_add_right, WithTop.coe_add, WithTop.coe_min, add_comm] using hc

/-- Exact tilted anchor, with feasibility stated for the tilted matrix entry. -/
theorem first_split_tilted_anchor (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v) (A : ℤ)
    (hfeasible : A ≤ X.capShift v.succ) :
    defectTiltedCost w X Y A v.succ =
      (min (parentTiltedProfile w X A v.succ)
        (parentTiltedProfile w Y A v.succ) : WithTop ℝ) := by
  have hv := first_split_valuation w X Y hX hY hgrid hrows v hprefix hchanged
  unfold defectTiltedCost parentTiltedProfile
  rw [ite_eq_left hfeasible, hv, ← hgrid v.succ]
  simp only [← WithTop.coe_min, ← WithTop.coe_add]
  congr 1
  exact (min_add_add_right _ _ _).symm

/-- Qualitative no-backflow for actual cofactor defects, `thm:no-backflow`.
No numerical square-weight margin is asserted. -/
theorem defect_no_backflow (w : ConvexWeight) (X Y : Diagram n)
    (hX : X.Connected) (hY : Y.Connected)
    (hgrid : ∀ j, X.capShift j = Y.capShift j)
    (hrows : X.rowLengthMultiset = Y.rowLengthMultiset)
    (v : Fin n) (hprefix : ∀ i : Fin n, i.val < v.val → X.rowParam i = Y.rowParam i)
    (hchanged : X.rowParam v ≠ Y.rowParam v)
    (i : Fin n) (hiv : i < v) (l : Fin (n + 1)) (hvl : v.succ < l) :
    defectTiltedCost w X Y (X.rowParam i) v.succ <
      defectTiltedCost w X Y (X.rowParam i) l := by
  have hi : i.val < v.val := hiv
  have hrow := hprefix i hi
  have hfeas : X.rowParam i ≤ X.capShift v.succ := by
    have hr := X.rowParam_strictMono hiv
    have hd := X.diagonal_feasible hX v
    have hc := X.capShift_strictMono
      (show v.castSucc < v.succ by change v.val < v.val + 1; omega)
    omega
  have hfeasl : X.rowParam i ≤ X.capShift l :=
    hfeas.trans (X.capShift_strictMono hvl).le
  have hx := parentTiltedProfile_after_split_lt w X hX i v hiv l hvl
  have hy := parentTiltedProfile_after_split_lt w Y hY i v hiv l hvl
  rw [← hrow] at hy
  have hmin : min (parentTiltedProfile w X (X.rowParam i) v.succ)
      (parentTiltedProfile w Y (X.rowParam i) v.succ) <
      min (parentTiltedProfile w X (X.rowParam i) l)
        (parentTiltedProfile w Y (X.rowParam i) l) := by
    apply lt_min
    · exact lt_of_le_of_lt (min_le_left _ _) hx
    · exact lt_of_le_of_lt (min_le_right _ _) hy
  rw [first_split_tilted_anchor w X Y hX hY hgrid hrows v hprefix hchanged
    (X.rowParam i) hfeas]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hmin)
    (defectTiltedCost_ge_parent_min w X Y hX hY hgrid (X.rowParam i) l hfeasl)

end Diagram
end SkewSchurReconstruction
