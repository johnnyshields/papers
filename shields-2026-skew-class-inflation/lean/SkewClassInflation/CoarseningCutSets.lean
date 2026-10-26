/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonCoarseningRecursion
import SkewClassInflation.RibbonWordComposition

/-!
# Retained cuts of actual adjacent coarsenings

The cut-set reading of the coarsenings in `eq:ribbon-coarsening`
of `shields-2026-skew-class-inflation.tex`.  The masks that define the
actual coarsening inventory retain exactly their original prefix
positions.  Positive parts make these positions genuine proper cuts.
Sorry-free.
-/

namespace SkewClassInflation

/-- The original prefix position at a specified adjacent boundary. -/
def rowPrefixCut {n : ℕ} (r : Fin (n + 1) → ℕ) (i : Fin n) : ℕ :=
  ((List.ofFn r).take (i.val + 1)).sum

/-- The first prefix cut is the actual first row length. -/
theorem rowPrefixCut_zero {n : ℕ} (r : Fin (n + 2) → ℕ) :
    rowPrefixCut r (0 : Fin (n + 1)) = r 0 := by
  simp only [rowPrefixCut, Fin.val_zero, List.ofFn_succ, List.take_succ_cons,
    List.take_zero, List.sum_cons, List.sum_nil, add_zero]

/-- Every later original cut is the first row plus the corresponding tail cut. -/
theorem rowPrefixCut_succ {n : ℕ} (r : Fin (n + 2) → ℕ) (i : Fin n) :
    rowPrefixCut r i.succ = r 0 + rowPrefixCut (fun j : Fin (n + 1) => r j.succ) i := by
  simp only [rowPrefixCut, Fin.val_succ, List.ofFn_succ, List.take_succ_cons, List.sum_cons]

/-- Merging the first boundary preserves all subsequent original prefix positions exactly. -/
theorem rowPrefixCut_merge {n : ℕ} (r : Fin (n + 2) → ℕ) (i : Fin n) :
    rowPrefixCut (Fin.cons (r 0 + r (0 : Fin (n + 1)).succ)
      (fun j : Fin n => r j.succ.succ)) i = rowPrefixCut r i.succ := by
  simp only [rowPrefixCut, Fin.val_succ, List.ofFn_succ, List.take_succ_cons,
    List.sum_cons, Fin.cons_zero, Fin.cons_succ]
  omega

/-- Every actual coarsening retains precisely the original boundary positions not merged. -/
theorem coarsenRows_properCuts {n : ℕ} (r : Fin (n + 1) → ℕ)
    (S : Fin n → Bool) (x : ℕ) :
    x ∈ wordProperCuts (coarsenRows r S) ↔
      ∃ i : Fin n, S i = false ∧ rowPrefixCut r i = x := by
  classical
  induction n generalizing x with
  | zero =>
    simp only [coarsenRows, wordProperCuts_single, Finset.notMem_empty]
    constructor
    · intro h; exact h.elim
    · rintro ⟨i, _⟩; exact i.elim0
  | succ n ih =>
    cases hS : S 0 with
    | false =>
      simp only [coarsenRows, hS, Bool.false_eq_true, ite_false]
      rw [wordProperCuts_cons _ _ (coarsenRows_ne_nil _ _)]
      constructor
      · intro hx
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact ⟨0, hS, by rw [rowPrefixCut_zero]; exact hx.symm⟩
        · obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
          obtain ⟨i, hi, he⟩ := (ih (fun j : Fin (n + 1) => r j.succ)
            (fun j => S j.succ) y).mp hy
          exact ⟨i.succ, hi, by rw [rowPrefixCut_succ, he]; exact hxy⟩
      · rintro ⟨i, hi, he⟩
        revert hi he
        refine Fin.cases ?_ (fun j => ?_) i
        · intro hi he
          rw [rowPrefixCut_zero] at he
          rw [← he]
          exact Finset.mem_insert_self _ _
        · intro hi he
          apply Finset.mem_insert_of_mem
          refine Finset.mem_image.mpr ⟨rowPrefixCut (fun j : Fin (n + 1) => r j.succ) j,
            (ih _ _ _).mpr ⟨j, ?_, rfl⟩, ?_⟩
          · exact hi
          · rw [← rowPrefixCut_succ]
            exact he
    | true =>
      simp only [coarsenRows, hS, ite_true]
      rw [ih]
      constructor
      · rintro ⟨i, hi, he⟩
        exact ⟨i.succ, hi, by rw [← rowPrefixCut_merge]; exact he⟩
      · rintro ⟨i, hi, he⟩
        revert hi he
        refine Fin.cases ?_ (fun j => ?_) i
        · intro hi he
          rw [hS] at hi
          contradiction
        · intro hi he
          exact ⟨j, hi, by rw [rowPrefixCut_merge]; exact he⟩

/-- The original positive row vector, as an actual composition of its full total. -/
def rowComposition {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    Composition (∑ i, r i) where
  blocks := List.ofFn r
  blocks_pos := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hr i
  blocks_sum := List.sum_ofFn

/-- Every selected actual coarsening is a positive composition of that same total. -/
def coarsenedComposition {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (S : Fin n → Bool) : Composition (∑ i, r i) where
  blocks := coarsenRows r S
  blocks_pos := by intro a ha; exact coarsenRows_pos r hr S a ha
  blocks_sum := coarsenRows_sum r S

/-- All original proper cuts are exactly the original finite prefix positions. -/
theorem rowComposition_properCuts {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (x : ℕ) :
    x ∈ properCuts (rowComposition r hr) ↔ ∃ i : Fin n, rowPrefixCut r i = x := by
  rw [← wordProperCuts_blocks (rowComposition r hr)]
  change x ∈ wordProperCuts (List.ofFn r) ↔ _
  have he := congrArg wordProperCuts (coarsenRows_false r)
  rw [← he, coarsenRows_properCuts]
  constructor
  · rintro ⟨i, _, hi⟩; exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, rfl, hi⟩

/-- Every actual coarsening's proper cuts form a subset of the original proper cuts. -/
theorem coarsenedComposition_cuts_subset {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (S : Fin n → Bool) :
    properCuts (coarsenedComposition r hr S) ⊆ properCuts (rowComposition r hr) := by
  intro x hx
  rw [← wordProperCuts_blocks (coarsenedComposition r hr S)] at hx
  obtain ⟨i, _, hi⟩ := (coarsenRows_properCuts r S x).mp hx
  exact (rowComposition_properCuts r hr x).mpr ⟨i, hi⟩

/-- Actual adjacent coarsenings are exactly the positive compositions retaining original cuts. -/
theorem coarsenRows_exists_iff_cuts_subset {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (γ : Composition (∑ i, r i)) :
    (∃ S : Fin n → Bool, coarsenRows r S = γ.blocks) ↔
      properCuts γ ⊆ properCuts (rowComposition r hr) := by
  classical
  constructor
  · rintro ⟨S, he⟩
    have hγ : coarsenedComposition r hr S = γ := Composition.ext he
    rw [← hγ]
    exact coarsenedComposition_cuts_subset r hr S
  · intro hs
    let S : Fin n → Bool := fun i => decide (rowPrefixCut r i ∉ properCuts γ)
    have hc : coarsenedComposition r hr S = γ := by
      apply properCuts_injective
      ext x
      rw [← wordProperCuts_blocks (coarsenedComposition r hr S)]
      change x ∈ wordProperCuts (coarsenRows r S) ↔ x ∈ properCuts γ
      rw [coarsenRows_properCuts]
      constructor
      · rintro ⟨i, hi, he⟩
        have hm : rowPrefixCut r i ∈ properCuts γ := by simpa [S] using hi
        exact he ▸ hm
      · intro hx
        obtain ⟨i, he⟩ := (rowComposition_properCuts r hr x).mp (hs hx)
        exact ⟨i, by simp [S, he, hx], he⟩
    exact ⟨S, congrArg Composition.blocks hc⟩

end SkewClassInflation
