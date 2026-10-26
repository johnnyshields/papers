/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedWindowPoles

/-!
# Complete forward-window polynomial inventories

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-period`).
The minimum anchor count is removed as a common power without deleting any start or word
position. Equal residual lengths give a nonzero exposed leading numerator. Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- The least anchor count over every actual cyclic start. -/
def minimalClassWindowCount {G α : Type*} [AddCommGroup G] [Fintype G] [DecidableEq α]
    (word : G → α) (step : G) (j : ℕ) (a : α) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (windowSum (classMask word a) step j)

/-- The complete forward numerator after clearing all response denominators. -/
def forwardWindowNumerator {G α R : Type*} [AddCommGroup G] [Fintype G] [Fintype α]
    [DecidableEq α] [CommRing R] (word : G → α) (step : G) (j : ℕ)
    (num den : α → R) : R :=
  ∑ i, ∏ Y, num Y ^ windowSum (classMask word Y) step j i *
    den Y ^ (maximalClassWindowCount word step j Y -
      windowSum (classMask word Y) step j i)

/-- Removing the least anchor power keeps all starts, class multiplicities and denominators. -/
def forwardWindowLeadingNumerator {G α R : Type*} [AddCommGroup G] [Fintype G] [Fintype α]
    [DecidableEq α] [CommRing R] (word : G → α) (step : G) (j : ℕ) (a : α)
    (num den : α → R) : R :=
  ∑ i, num a ^ (windowSum (classMask word a) step j i -
      minimalClassWindowCount word step j a) *
    (den a ^ (maximalClassWindowCount word step j a -
      windowSum (classMask word a) step j i) *
      ∏ Y ∈ Finset.univ.erase a,
        num Y ^ windowSum (classMask word Y) step j i *
          den Y ^ (maximalClassWindowCount word step j Y -
            windowSum (classMask word Y) step j i))

/-- The minimum is attained, including zero windows and classes absent from the word. -/
theorem exists_minimal_class_window {G α : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq α]
    (word : G → α) (step : G) (j : ℕ) (a : α) :
    ∃ i, windowSum (classMask word a) step j i =
      minimalClassWindowCount word step j a := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (windowSum (classMask word a) step j)
  exact ⟨i, hi.symm⟩

/-- The produced common factor is exactly the least actual anchor count. -/
theorem forwardWindowNumerator_factor {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [CommRing R]
    (word : G → α) (step : G) (j : ℕ) (a : α) (num den : α → R) :
    forwardWindowNumerator word step j num den =
      num a ^ minimalClassWindowCount word step j a *
        forwardWindowLeadingNumerator word step j a num den := by
  classical
  unfold forwardWindowNumerator forwardWindowLeadingNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmin : minimalClassWindowCount word step j a ≤
      windowSum (classMask word a) step j i := Finset.inf'_le _ (Finset.mem_univ i)
  rw [← Finset.mul_prod_erase Finset.univ
    (fun Y => num Y ^ windowSum (classMask word Y) step j i *
      den Y ^ (maximalClassWindowCount word step j Y -
        windowSum (classMask word Y) step j i)) (Finset.mem_univ a)]
  rw [← mul_assoc, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hmin]

/-- Same-sign off-anchor factors give a nonzero leading forward numerator in both chambers. -/
theorem forwardWindowLeadingNumerator_eval_pos {G α R : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α] [CommRing R]
    (word : G → α) (step : G) (j : ℕ) (a : α) (num den : α → R)
    (φ : R →+* ℝ) (sign : ℝ) (hroot : φ (num a) = 0)
    (hden : ∀ Y, 0 < φ (den Y))
    (hsign : ∀ Y, Y ≠ a → 0 < sign * φ (num Y)) :
    0 < sign ^ (j - minimalClassWindowCount word step j a) *
      φ (forwardWindowLeadingNumerator word step j a num den) := by
  classical
  let count := fun Y i => windowSum (classMask word Y) step j i
  let bound := maximalClassWindowCount word step j
  let low := minimalClassWindowCount word step j a
  have hb (Y : α) (i : G) : count Y i ≤ bound Y :=
    Finset.le_sup (Finset.mem_univ i)
  have hl (i : G) : low ≤ count a i := Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨i, hi⟩ := exists_minimal_class_window word step j a
  have hc (i : G) : (bound a - low) - (bound a - count a i) = count a i - low := by
    have := hl i
    have := hb a i
    omega
  have hoff (Y : α) (i : G) : bound Y - (bound Y - count Y i) = count Y i :=
    Nat.sub_sub_self (hb Y i)
  have hpos := clearedInverseResponseSum_eval_pos Finset.univ (Finset.univ.erase a)
    (num a) (den a) (bound a - low) (j - low)
    (fun i => bound a - count a i) bound (fun i Y => bound Y - count Y i) num den φ sign
    hroot (hden a)
    (fun i _ => by have := hl i; omega)
    ⟨i, Finset.mem_univ i, by dsimp only [low, count]; rw [hi]⟩
    (fun Y hY => hsign Y (Finset.mem_erase.mp hY).1) (fun Y _ => hden Y)
    (by
      intro i _ hEq
      have hlow : count a i = low := by have := hb a i; have := hl i; omega
      simp only [hoff]
      have htotal : (∑ Y, count Y i) = j := sum_class_window_counts word step j i
      have herase := Finset.sum_erase_add Finset.univ (fun Y => count Y i)
        (Finset.mem_univ a)
      rw [htotal, hlow] at herase
      omega)
  simpa only [clearedPoleSum, hc, hoff, count, bound, low,
    forwardWindowLeadingNumerator] using hpos

end SkewCornerDescent.CyclicWindows
