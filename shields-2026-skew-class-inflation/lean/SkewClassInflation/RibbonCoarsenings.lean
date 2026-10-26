/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonDeterminants

/-!
# Actual adjacent-part ribbon coarsenings

The coarsenings in `eq:ribbon-coarsening` of
`shields-2026-skew-class-inflation.tex`.  A true boundary decision
merges the adjacent positive parts; a false decision retains the
boundary.  Each mask supplies an actual ordered positive word, with
its total size and number of parts preserved exactly.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg
open scoped BigOperators

/-- The actual ordered word obtained by merging precisely the selected adjacent boundaries. -/
def coarsenRows : {n : ℕ} → (Fin (n + 1) → ℕ) → (Fin n → Bool) → List ℕ
  | 0, r, _ => [r 0]
  | n + 1, r, S =>
      if S 0 then
        coarsenRows (Fin.cons (r 0 + r (0 : Fin (n + 1)).succ)
          (fun i : Fin n => r i.succ.succ)) (fun i => S i.succ)
      else r 0 :: coarsenRows (fun i : Fin (n + 1) => r i.succ) (fun i => S i.succ)

/-- Actual coarsening never changes the total sum of the ordered parts. -/
theorem coarsenRows_sum {n : ℕ} (r : Fin (n + 1) → ℕ) (S : Fin n → Bool) :
    (coarsenRows r S).sum = ∑ i, r i := by
  induction n with
  | zero => simp [coarsenRows]
  | succ n ih =>
    rw [coarsenRows]
    split_ifs
    · rw [ih, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      omega
    · rw [List.sum_cons, ih]
      conv_rhs => rw [Fin.sum_univ_succ]

/-- Selected merges remove precisely that many parts, independent of repeated part values. -/
theorem coarsenRows_length {n : ℕ} (r : Fin (n + 1) → ℕ) (S : Fin n → Bool) :
    selectedSeams S + (coarsenRows r S).length = n + 1 := by
  induction n with
  | zero => simp [coarsenRows, selectedSeams]
  | succ n ih =>
    have hs : selectedSeams S = (if S 0 then 1 else 0) +
        selectedSeams (fun i : Fin n => S i.succ) := by
      rw [selectedSeams, Fin.sum_univ_succ]
      rfl
    rw [hs, coarsenRows]
    split_ifs with hS
    · have hh := ih (Fin.cons (r 0 + r (0 : Fin (n + 1)).succ)
        (fun i : Fin n => r i.succ.succ)) (fun i => S i.succ)
      simp only [hS, ite_true] at *
      omega
    · have hh := ih (fun i : Fin (n + 1) => r i.succ) (fun i => S i.succ)
      simp only [hS, List.length_cons] at *
      omega

/-- Every actual coarsening of a positive word is again positive. -/
theorem coarsenRows_pos {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (S : Fin n → Bool) : ∀ a ∈ coarsenRows r S, 0 < a := by
  induction n with
  | zero => simpa only [coarsenRows, List.mem_singleton] using fun a (ha : a = r 0) => ha ▸ hr 0
  | succ n ih =>
    rw [coarsenRows]
    split_ifs
    · apply ih
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · have := hr 0
        change 0 < r 0 + r (0 : Fin (n + 1)).succ
        omega
      · exact hr j.succ.succ
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hr 0
      · exact ih _ (fun i => hr i.succ) _ a ha

/-- Coarsening never produces an empty word. -/
theorem coarsenRows_ne_nil {n : ℕ} (r : Fin (n + 1) → ℕ) (S : Fin n → Bool) :
    coarsenRows r S ≠ [] := by
  induction n with
  | zero => simp [coarsenRows]
  | succ n ih =>
    rw [coarsenRows]
    split_ifs
    · exact ih _ _
    · exact List.cons_ne_nil _ _

/-- The first resulting part contains the entire first original part. -/
theorem coarsenRows_head_lower {n : ℕ} (r : Fin (n + 1) → ℕ) (S : Fin n → Bool) :
    r 0 ≤ (coarsenRows r S).headD 0 := by
  induction n with
  | zero => simp [coarsenRows]
  | succ n ih =>
    rw [coarsenRows]
    split_ifs
    · have hh := ih (Fin.cons (r 0 + r (0 : Fin (n + 1)).succ)
        (fun i : Fin n => r i.succ.succ)) (fun i => S i.succ)
      change r 0 + r (0 : Fin (n + 1)).succ ≤ _ at hh
      omega
    · simp

/-- A positive ordered word recovers every selected boundary from its actual coarsening. -/
theorem coarsenRows_injective {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    Function.Injective (coarsenRows r) := by
  induction n with
  | zero => intro S T _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro S T he
    cases hS : S 0 <;> cases hT : T 0
    · have htail := ih (fun i : Fin (n + 1) => r i.succ) (fun i => hr i.succ)
        (show coarsenRows (fun i : Fin (n + 1) => r i.succ) (fun i => S i.succ) =
          coarsenRows (fun i : Fin (n + 1) => r i.succ) (fun i => T i.succ) from
          (List.cons.inj (by
            simpa only [coarsenRows, hS, hT, Bool.false_eq_true, ite_false] using he)).2)
      funext i
      refine Fin.cases ?_ (fun j => congrFun htail j) i
      rw [hS, hT]
    · have hh := congrArg (fun l : List ℕ => l.headD 0) he
      have hb := coarsenRows_head_lower
        (Fin.cons (r 0 + r (0 : Fin (n + 1)).succ) (fun i : Fin n => r i.succ.succ))
        (fun i => T i.succ)
      simp only [coarsenRows, hS, hT, Bool.false_eq_true, ite_false, ite_true,
        List.headD_cons] at hh
      change r 0 = _ at hh
      change r 0 + r (0 : Fin (n + 1)).succ ≤ _ at hb
      have hp := hr (0 : Fin (n + 1)).succ
      omega
    · have hh := congrArg (fun l : List ℕ => l.headD 0) he
      have hb := coarsenRows_head_lower
        (Fin.cons (r 0 + r (0 : Fin (n + 1)).succ) (fun i : Fin n => r i.succ.succ))
        (fun i => S i.succ)
      simp only [coarsenRows, hS, hT, Bool.false_eq_true, ite_false, ite_true,
        List.headD_cons] at hh
      change _ = r 0 at hh
      change r 0 + r (0 : Fin (n + 1)).succ ≤ _ at hb
      have hp := hr (0 : Fin (n + 1)).succ
      omega
    · let R : Fin (n + 1) → ℕ := Fin.cons (r 0 + r (0 : Fin (n + 1)).succ)
        (fun i : Fin n => r i.succ.succ)
      have hpos : ∀ i : Fin (n + 1), 0 < R i := by
        intro i
        refine Fin.cases ?_ (fun j => hr j.succ.succ) i
        change 0 < r 0 + r (0 : Fin (n + 1)).succ
        have := hr 0
        omega
      have htail := ih R hpos
        (by simpa only [coarsenRows, hS, hT, ite_true] using he)
      funext i
      refine Fin.cases ?_ (fun j => congrFun htail j) i
      rw [hS, hT]

end SkewClassInflation
