/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ReflectedCutTypes

/-!
# Cut counts on actual reflection-closed subsets

The numerical window-count input to factor-reversal classification in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
The actual reflected two-part types preserve cut counts on every finite
reflection-closed set.  In particular, they preserve the total number of
nonmultiple internal cuts of an ordinary product.  Sorry-free.
-/

namespace SkewClassInflation

/-- Inventory equality preserves the cut count on every actual reflection-closed finite set. -/
theorem reflected_subset_cut_card {K : ℕ} (α β : Composition K)
    (he : coarseningInventory α = coarseningInventory β) (S : Finset ℕ)
    (hbound : ∀ x ∈ S, x ≤ K) (href : ∀ x ∈ S, K - x ∈ S) :
    (S.filter (fun x => x ∈ properCuts α)).card =
      (S.filter (fun x => x ∈ properCuts β)).card := by
  classical
  have hsum (γ : Composition K) :
      (∑ x ∈ S, if K - x ∈ properCuts γ then (1 : ℕ) else 0) =
        ∑ x ∈ S, if x ∈ properCuts γ then (1 : ℕ) else 0 := by
    refine Finset.sum_bij (fun x _ => K - x) ?_ ?_ ?_ ?_
    · intro x hx
      exact href x hx
    · intro x hx y hy heq
      have hxb := hbound x hx
      have hyb := hbound y hy
      omega
    · intro y hy
      exact ⟨K - y, href y hy, Nat.sub_sub_self (hbound y hy)⟩
    · intro x hx
      rfl
  have ht : (∑ x ∈ S, compositionCutType α x) = ∑ x ∈ S, compositionCutType β x :=
    Finset.sum_congr rfl (fun x _ => coarseningInventory_cut_type α β he x)
  simp only [compositionCutType, Finset.sum_add_distrib] at ht
  rw [hsum α, hsum β, ← Finset.card_filter, ← Finset.card_filter] at ht
  omega

/-- Actual proper cuts not at whole multiples of the specified inner weight. -/
def nonmultipleCuts {K : ℕ} (α : Composition K) (n : ℕ) : Finset ℕ :=
  (properCuts α).filter (fun x => x % n ≠ 0)

/-- The same count can be taken on the full true proper-weight interval. -/
theorem nonmultipleCuts_as_window {K : ℕ} (α : Composition K) (n : ℕ) :
    nonmultipleCuts α n =
      ((Finset.Ioo 0 K).filter (fun x => x % n ≠ 0)).filter (fun x => x ∈ properCuts α) := by
  ext x
  simp only [nonmultipleCuts, Finset.mem_filter, Finset.mem_Ioo]
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨⟨properCuts_bounds α x hx, hn⟩, hx⟩
  · rintro ⟨⟨_, hn⟩, hx⟩
    exact ⟨hx, hn⟩

/-- Same-inventory mates preserve nonmultiple cut counts at every divisor of their weight. -/
theorem inventory_nonmultiple_cut_card {M N : ℕ} (α β : Composition (M * N))
    (he : coarseningInventory α = coarseningInventory β) :
    (nonmultipleCuts α N).card = (nonmultipleCuts β N).card := by
  rw [nonmultipleCuts_as_window, nonmultipleCuts_as_window]
  apply reflected_subset_cut_card α β he
  · intro x hx
    exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp hx).1).2.le
  · intro x hx
    obtain ⟨hb, hn⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx0, hxK⟩ := Finset.mem_Ioo.mp hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, ?_⟩
    intro hmod
    have hd := Nat.dvd_of_mod_eq_zero hmod
    have htotal : N ∣ x + (M * N - x) := by
      rw [Nat.add_sub_of_le hxK.le]
      exact dvd_mul_of_dvd_right (dvd_refl N) M
    have hdx := (Nat.dvd_add_iff_left hd).mpr htotal
    exact hn (Nat.mod_eq_zero_of_dvd hdx)

end SkewClassInflation
