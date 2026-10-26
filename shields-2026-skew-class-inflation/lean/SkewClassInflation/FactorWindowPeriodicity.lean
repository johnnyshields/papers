/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CompositionCutMoments

/-!
# Actual periodic factorization of arbitrary ordinary-product mates

The geometric factor-transport step for `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Monotone prefix positions and
reflected first-moment cancellation identify all actual windows.  Their
common cuts produce a literal ordinary factorization of every mate.
Sorry-free.
-/

namespace SkewClassInflation

/-- The first and last actual windows of an ordinary-product mate coincide. -/
theorem compositionWindow_endpoints_eq {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hM : 0 < M) (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε)) :
    compositionWindow θ N (M - 1) = compositionWindow θ N 0 := by
  by_cases hM1 : M = 1
  · subst M
    rfl
  have hfirst := compositionWindow_length_eq δ ε hN θ hInv 0 hM
  have hlast := compositionWindow_length_eq δ ε hN θ hInv (M - 1) (by omega)
  apply composition_eq_of_ordered_cut_sums _ _ (hlast.trans hfirst.symm)
  · intro t ht
    obtain ⟨ht0, htl⟩ := Finset.mem_Ioo.mp ht
    exact compositionWindow_prefix_antitone δ ε hN θ hInv 0 (M - 1) t
      (by omega) (by omega) ht0 (by omega)
  · exact (compositionWindow_endpoint_cut_sum δ ε hM hN θ hInv).symm

/-- Every actual copy window has the same complete inner composition. -/
theorem compositionWindow_all_eq {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε))
    (i : ℕ) (hi : i < M) : compositionWindow θ N i = compositionWindow θ N 0 := by
  have hM : 0 < M := by omega
  by_cases hi0 : i = 0
  · subst i
    rfl
  have hend := compositionWindow_endpoints_eq δ ε hM hN θ hInv
  by_cases hilast : i = M - 1
  · rw [hilast]
    exact hend
  have hfirst := compositionWindow_length_eq δ ε hN θ hInv 0 hM
  have hlen := compositionWindow_length_eq δ ε hN θ hInv i hi
  apply composition_eq_of_sizeUpTo_internal _ _ (hlen.trans hfirst.symm)
  intro t ht
  obtain ⟨ht0, htl⟩ := Finset.mem_Ioo.mp ht
  have htε : t < ε.length := by omega
  have hupper := compositionWindow_prefix_antitone δ ε hN θ hInv 0 i t
    (by omega) hi ht0 htε
  have hlower := compositionWindow_prefix_antitone δ ε hN θ hInv i (M - 1) t
    (by omega) (by omega) ht0 htε
  rw [hend] at hlower
  exact Nat.le_antisymm hupper hlower

/-- Every mate has the source's full nonmultiple cut period, not just its signed period. -/
theorem inventory_mate_cut_periodic {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε))
    (x : ℕ) (_hx : 0 < x) (hxK : x < M * N) (hmod : x % N ≠ 0) :
    x ∈ properCuts θ ↔ x % N ∈ properCuts θ := by
  have hi : x / N < M := (Nat.div_lt_iff_lt_mul hN).mpr hxK
  have hr : 0 < x % N := Nat.pos_of_ne_zero hmod
  have hrN : x % N < N := Nat.mod_lt x hN
  have hwin := compositionWindow_cuts θ N (x / N) (x % N) hr hrN
  have he : x / N * N + x % N = x := by
    simpa only [Nat.mul_comm N (x / N)] using Nat.div_add_mod x N
  rw [he, compositionWindow_all_eq δ ε hN θ hInv (x / N) hi] at hwin
  have hfirst := compositionWindow_cuts θ N 0 (x % N) hr hrN
  simp only [zero_mul, zero_add] at hfirst
  exact hwin.symm.trans hfirst

/-- The actual sampled factors of an arbitrary inventory mate compose literally to that mate. -/
theorem inventory_mate_periodic_factorization {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε)) :
    compositionProduct (periodicOuter θ) (periodicInner θ) = θ := by
  exact periodic_factorization θ hN (inventory_mate_cut_periodic δ ε hN θ hInv)

end SkewClassInflation
