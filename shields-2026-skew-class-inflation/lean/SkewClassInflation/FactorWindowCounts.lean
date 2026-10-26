/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorWindowBounds
import SkewClassInflation.ReflectedCutCounts
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exact window lengths of ordinary-product mates

The window-count step in factor transport for `thm:sharp-inflation`
of `shields-2026-skew-class-inflation.tex`.  Actual nonmultiple cuts
partition into the copy windows.  The residue bound and the preserved
reflection count force every window to have the original inner length.
Sorry-free.
-/

namespace SkewClassInflation

/-- Actual nonmultiple cuts partition into translated copy-window cuts. -/
theorem nonmultipleCuts_eq_window_union {M N : ℕ} (θ : Composition (M * N))
    (hN : 0 < N) :
    nonmultipleCuts θ N = (Finset.range M).biUnion (fun i =>
      (properCuts (compositionWindow θ N i)).image (fun x => i * N + x)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hc, hn⟩ := Finset.mem_filter.mp hx
    have hb := properCuts_bounds θ x hc
    have hi : x / N < M := (Nat.div_lt_iff_lt_mul hN).mpr hb.2
    have hr : 0 < x % N := Nat.pos_of_ne_zero hn
    have hcut : x % N ∈ properCuts (compositionWindow θ N (x / N)) := by
      rw [compositionWindow_cuts θ N (x / N) _ hr (Nat.mod_lt x hN)]
      have he : x / N * N + x % N = x := by
        simpa only [Nat.mul_comm N (x / N)] using Nat.div_add_mod x N
      rwa [he]
    exact Finset.mem_biUnion.mpr ⟨x / N, Finset.mem_range.mpr hi,
      Finset.mem_image.mpr ⟨x % N, hcut, by
        simpa only [Nat.mul_comm N (x / N)] using Nat.div_add_mod x N⟩⟩
  · intro hx
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hb := properCuts_bounds (compositionWindow θ N i) y hy
    refine Finset.mem_filter.mpr ⟨(compositionWindow_cuts θ N i y hb.1 hb.2).mp hy, ?_⟩
    simpa only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_eq_of_lt hb.2] using Nat.ne_of_gt hb.1

/-- Two distinct copy windows have disjoint translated actual cuts. -/
theorem compositionWindow_images_disjoint {K N : ℕ} (θ : Composition K)
    (hN : 0 < N) {i j : ℕ} (hij : i ≠ j) :
    Disjoint ((properCuts (compositionWindow θ N i)).image (fun x => i * N + x))
      ((properCuts (compositionWindow θ N j)).image (fun x => j * N + x)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hx
  obtain ⟨s, hs, heq'⟩ := Finset.mem_image.mp hy
  have hbr := properCuts_bounds (compositionWindow θ N i) r hr
  have hbs := properCuts_bounds (compositionWindow θ N j) s hs
  have he : i * N + r = j * N + s := heq.trans heq'.symm
  have hrs := congrArg (fun x => x % N) he
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
    Nat.mod_eq_of_lt hbr.2, Nat.mod_eq_of_lt hbs.2] at hrs
  subst s
  exact hij (mul_right_cancel₀ (Nat.ne_of_gt hN) (Nat.add_right_cancel he))

/-- The total nonmultiple count is the sum of the actual window cut counts. -/
theorem nonmultipleCuts_card_eq_sum {M N : ℕ} (θ : Composition (M * N))
    (hN : 0 < N) :
    (nonmultipleCuts θ N).card =
      ∑ i ∈ Finset.range M, (properCuts (compositionWindow θ N i)).card := by
  classical
  rw [nonmultipleCuts_eq_window_union θ hN, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)
  · intro i _ j _ hij
    exact compositionWindow_images_disjoint θ hN hij

/-- Ordinary products have one full set of inner cuts in every copy window. -/
theorem compositionProduct_nonmultiple_card {M N : ℕ}
    (δ : Composition M) (ε : Composition N) (hN : 0 < N) :
    (nonmultipleCuts (compositionProduct δ ε) N).card = M * (properCuts ε).card := by
  rw [nonmultipleCuts_card_eq_sum _ hN]
  calc
    (∑ i ∈ Finset.range M,
        (properCuts (compositionWindow (compositionProduct δ ε) N i)).card) =
        ∑ _i ∈ Finset.range M, (properCuts ε).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [compositionWindow_compositionProduct δ ε i (Finset.mem_range.mp hi)]
    _ = M * (properCuts ε).card := by simp

/-- Positive compositions have one fewer actual proper cut than parts. -/
theorem properCuts_card_add_one {N : ℕ} (α : Composition N) (hN : 0 < N) :
    (properCuts α).card + 1 = α.length := by
  rw [properCuts_eq_suffixSet]
  simpa only [Composition.length, Composition.reverse_blocks, List.length_reverse]
    using suffixSet_card α.reverse hN

/-- Every actual window of a same-inventory mate has exactly the original inner length. -/
theorem compositionWindow_length_eq {M N : ℕ} (δ : Composition M) (ε : Composition N)
    (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε))
    (i : ℕ) (hi : i < M) : (compositionWindow θ N i).length = ε.length := by
  classical
  have hle : ∀ j ∈ Finset.range M,
      (properCuts (compositionWindow θ N j)).card ≤ (properCuts ε).card := by
    intro j hj
    have hlen := compositionWindow_length_le δ ε hN θ hInv j (Finset.mem_range.mp hj)
    have hw := properCuts_card_add_one (compositionWindow θ N j) hN
    have he := properCuts_card_add_one ε hN
    omega
  have hsum : (∑ j ∈ Finset.range M, (properCuts (compositionWindow θ N j)).card) =
      ∑ _j ∈ Finset.range M, (properCuts ε).card := by
    rw [← nonmultipleCuts_card_eq_sum θ hN,
      inventory_nonmultiple_cut_card θ (compositionProduct δ ε) hInv,
      compositionProduct_nonmultiple_card δ ε hN]
    simp
  have hc := (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_range.mpr hi)
  have hw := properCuts_card_add_one (compositionWindow θ N i) hN
  have he := properCuts_card_add_one ε hN
  omega

end SkewClassInflation
