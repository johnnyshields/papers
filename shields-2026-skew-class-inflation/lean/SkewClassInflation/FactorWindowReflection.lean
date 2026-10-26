/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ReflectedCutMoments

/-!
# Reflected balance between the first and last actual windows

The endpoint-window identification step in factor transport for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Actual two-part inventory coefficients and equal window lengths force
the first and last windows to have the same cut-position sum.  Sorry-free.
-/

namespace SkewClassInflation

/-- The two reflected global cuts in an inner interval belong to the two endpoint windows. -/
theorem compositionCutType_endpoint_windows {M N : ℕ} (θ : Composition (M * N))
    (hM : 0 < M) (x : ℕ) (hx : 0 < x) (hxN : x < N) :
    compositionCutType θ x =
      (if x ∈ properCuts (compositionWindow θ N 0) then 1 else 0) +
      (if N - x ∈ properCuts (compositionWindow θ N (M - 1)) then 1 else 0) := by
  classical
  have hfirst := compositionWindow_cuts θ N 0 x hx hxN
  simp only [zero_mul, zero_add] at hfirst
  have hr0 : 0 < N - x := by omega
  have hrN : N - x < N := by omega
  have hlast := compositionWindow_cuts θ N (M - 1) (N - x) hr0 hrN
  have he : (M - 1) * N + (N - x) = M * N - x := by
    have hh : (M - 1) + 1 = M := by omega
    have hm := congrArg (fun a => a * N) hh
    rw [Nat.add_mul, one_mul] at hm
    omega
  rw [he] at hlast
  simp only [compositionCutType, hfirst, hlast]

/-- The two endpoint windows of an inventory mate have reflected-balanced actual cuts. -/
theorem compositionWindow_endpoint_balance {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hM : 0 < M) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε))
    (x : ℕ) (hx : 0 < x) (hxN : x < N) :
    (if x ∈ properCuts (compositionWindow θ N 0) then (1 : ℕ) else 0) +
      (if N - x ∈ properCuts (compositionWindow θ N (M - 1)) then 1 else 0) =
    (if N - x ∈ properCuts (compositionWindow θ N 0) then 1 else 0) +
      (if x ∈ properCuts (compositionWindow θ N (M - 1)) then 1 else 0) := by
  classical
  have hlast : M - 1 < M := by omega
  have hs (y : ℕ) (hy : 0 < y) (hyN : y < N) :
      compositionCutType (compositionProduct δ ε) y = compositionCutType ε y := by
    rw [compositionCutType_endpoint_windows _ hM y hy hyN,
      compositionWindow_compositionProduct δ ε 0 hM,
      compositionWindow_compositionProduct δ ε (M - 1) hlast]
    rfl
  have he := coarseningInventory_cut_type θ (compositionProduct δ ε) hInv x
  have hr := coarseningInventory_cut_type θ (compositionProduct δ ε) hInv (N - x)
  rw [hs x hx hxN, compositionCutType_endpoint_windows θ hM x hx hxN] at he
  rw [hs (N - x) (by omega) (by omega),
    compositionCutType_endpoint_windows θ hM (N - x) (by omega) (by omega)] at hr
  have hxx : N - (N - x) = x := by omega
  rw [hxx] at hr
  have hsym : compositionCutType ε x = compositionCutType ε (N - x) := by
    simp only [compositionCutType, hxx, Nat.add_comm]
  exact he.trans (hsym.trans hr.symm)

/-- The first and last windows have the same sum of actual proper-cut positions. -/
theorem compositionWindow_endpoint_cut_sum {M N : ℕ} (δ : Composition M)
    (ε : Composition N) (hM : 0 < M) (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε)) :
    (∑ x ∈ properCuts (compositionWindow θ N 0), (x : ℤ)) =
      ∑ x ∈ properCuts (compositionWindow θ N (M - 1)), (x : ℤ) := by
  have hfirst := compositionWindow_length_eq δ ε hN θ hInv 0 hM
  have hlast := compositionWindow_length_eq δ ε hN θ hInv (M - 1) (by omega)
  apply reflected_balanced_cut_sum N
  · intro x hx
    exact Finset.mem_Ioo.mpr (properCuts_bounds _ x hx)
  · intro x hx
    exact Finset.mem_Ioo.mpr (properCuts_bounds _ x hx)
  · have hf := properCuts_card_add_one (compositionWindow θ N 0) hN
    have hl := properCuts_card_add_one (compositionWindow θ N (M - 1)) hN
    omega
  · intro x hx
    have hb := Finset.mem_Ioo.mp hx
    exact compositionWindow_endpoint_balance δ ε hM θ hInv x hb.1 hb.2

end SkewClassInflation
