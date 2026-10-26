/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonCoarsenings

/-!
# The ribbon coarsening formula on actual ordered words

Formalizes `eq:ribbon-coarsening` in
`shields-2026-skew-class-inflation.tex`.  The sum runs over the actual
distinct coarsening words.  Positivity, unchanged total size, and
injectivity of the boundary masks justify this indexing, including
when original part values repeat.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg
open scoped BigOperators

/-- Contracting the first zero seam merges exactly the first two ordered row entries. -/
theorem first_contract_rows {n : ℕ} (P : Profile (n + 1)) (hg : P.g 0 = 0) :
    (contract P 0).r = Fin.cons (P.r 0 + P.r (0 : Fin (n + 1)).succ)
      (fun i : Fin n => P.r i.succ.succ) := by
  apply List.ofFn_injective
  rw [contract_first_row_word P hg, List.ofFn_cons]

/-- The right principal piece at the first seam retains exactly the tail row function. -/
theorem right_first_rows {n : ℕ} (P : Profile (n + 1)) :
    (rightOfSeam P (0 : Fin (n + 1))).r = (fun i : Fin (n + 1) => P.r i.succ) := by
  funext i
  change P.r (sliceEmbedding 1 n (by omega) i) = P.r i.succ
  congr 1
  apply Fin.ext
  change 1 + i.val = i.val + 1
  omega

/-- The actual zero-gap interval monomial is the product of the actual merged parts. -/
theorem intervalMask_coarsenRows {R : Type*} [CommRing R] (h : ℤ → R) (h0 : h 0 = 1)
    {n : ℕ} (P : Profile n) (hg : ∀ j, P.g j = 0) (S : Fin n → Bool) :
    intervalMask h P S = ((coarsenRows P.r S).map (fun a : ℕ => h a)).prod := by
  induction n with
  | zero => simp [intervalMask, coarsenRows]
  | succ n ih =>
    rw [intervalMask, coarsenRows]
    by_cases hS : S 0 = true
    · rw [ite_eq_left hS, ite_eq_left hS, hg 0, Nat.cast_zero, h0, one_mul]
      have hC : ∀ j, (contract P 0).g j = 0 := by intro j; rw [contract_gap, hg]
      rw [ih (contract P 0) hC, first_contract_rows P (hg 0)]
    · rw [ite_eq_right hS, ite_eq_right hS, List.map_cons, List.prod_cons]
      let Q : Profile n := rightOfSeam P (0 : Fin (n + 1))
      have hR : ∀ j, Q.g j = 0 := fun j => hg _
      change h (P.r 0) * intervalMask h Q (fun j : Fin n => S j.succ) = _
      rw [ih Q hR]
      have hrows : Q.r = fun i : Fin (n + 1) => P.r i.succ := right_first_rows P
      rw [hrows]

/-- The actual ribbon polynomial is the signed sum over all adjacent-boundary decisions. -/
theorem ribbon_coarsening_expansion {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    ribbonWord (List.ofFn r) = ∑ S : Fin n → Bool,
      (-1 : CompleteRing) ^ selectedSeams S *
        ((coarsenRows r S).map (fun a : ℕ => complete a)).prod := by
  let P : Profile n :=
    { r := r
      g := fun _ => 0
      r_pos := hr
      g_lt_castSucc := fun j => hr j.castSucc
      g_lt_succ := fun j => hr j.succ }
  have he := zero_gaps_ribbon_polynomial P (fun _ => rfl)
  change P.toBetaDiagram.schur = ribbonWord (List.ofFn r) at he
  rw [← he, schur_interval_mask_expansion P (zero_gaps_thick P (fun _ => rfl))]
  apply Finset.sum_congr rfl
  intro S _
  rw [intervalMask_coarsenRows complete complete_zero P (fun _ => rfl)]

/-- The finite set of actual distinct ordered coarsenings. -/
def coarseningWords {n : ℕ} (r : Fin (n + 1) → ℕ) : Finset (List ℕ) :=
  Finset.univ.image (coarsenRows r)

/-- Each indexed coarsening word is an actual positive composition of the unchanged total. -/
theorem coarseningWords_composition {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i)
    (w : List ℕ) (hw : w ∈ coarseningWords r) :
    ∃ γ : Composition (∑ i, r i), γ.blocks = w := by
  obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hw
  exact ⟨⟨coarsenRows r S, fun ha => coarsenRows_pos r hr S _ ha, coarsenRows_sum r S⟩, rfl⟩

/-- The classical ribbon coarsening formula, indexed by actual distinct composition words. -/
theorem ribbon_coarsening_formula {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    ribbonWord (List.ofFn r) = ∑ w ∈ coarseningWords r,
      (-1 : CompleteRing) ^ (n + 1 - w.length) *
        (w.map (fun a : ℕ => complete a)).prod := by
  classical
  rw [coarseningWords, Finset.sum_image (by
    intro S _ T _ he
    exact coarsenRows_injective r hr he)]
  rw [ribbon_coarsening_expansion r hr]
  apply Finset.sum_congr rfl
  intro S _
  have hl := coarsenRows_length r S
  have hs : selectedSeams S = n + 1 - (coarsenRows r S).length := by omega
  rw [hs]

end SkewClassInflation
