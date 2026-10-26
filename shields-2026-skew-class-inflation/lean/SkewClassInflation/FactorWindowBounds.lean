/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InventoryResidues
import SkewClassInflation.CompositionPadding

/-!
# Actual inner-weight windows of arbitrary ordinary-product mates

The local part-count step in factor transport for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
A window is constructed from the actual mate cuts.  Whole-weight
endpoint padding realizes it as an actual full-weight coarsening,
so the original product's unordered residue bound applies.
Sorry-free.
-/

namespace SkewClassInflation

/-- The actual proper cuts strictly inside one fixed whole-weight copy interval. -/
noncomputable def compositionWindow {K : ℕ} (θ : Composition K) (n i : ℕ) : Composition n :=
  compositionFromCuts n ((Finset.Ioo 0 n).filter (fun x => i * n + x ∈ properCuts θ))

/-- Every proper window coordinate has exactly its actual translated mate-cut membership. -/
theorem compositionWindow_cuts {K : ℕ} (θ : Composition K) (n i x : ℕ)
    (hx : 0 < x) (hxn : x < n) :
    x ∈ properCuts (compositionWindow θ n i) ↔ i * n + x ∈ properCuts θ := by
  rw [compositionWindow, compositionFromCuts_internal _ _ _ hx hxn]
  simp only [Finset.mem_filter, Finset.mem_Ioo, hx, hxn, and_self, true_and]

/-- Every copy window in an ordinary product has the original inner cuts. -/
theorem compositionWindow_compositionProduct {M N : ℕ}
    (δ : Composition M) (ε : Composition N)
    (i : ℕ) (hi : i < M) :
    compositionWindow (compositionProduct δ ε) N i = ε := by
  apply properCuts_injective
  ext x
  by_cases hx : 0 < x ∧ x < N
  · rw [compositionWindow_cuts _ _ _ _ hx.1 hx.2]
    have hpos : 0 < i * N + x := by omega
    have hle : (i + 1) * N ≤ M * N := Nat.mul_le_mul_right N hi
    have hlt : i * N + x < M * N := by nlinarith
    have hmod : (i * N + x) % N = x := by
      simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hx.2]
    rw [compositionProduct_internal δ ε _ hpos hlt (by rw [hmod]; omega), hmod]
  · constructor
    · intro h
      exact False.elim (hx (properCuts_bounds _ _ h))
    · intro h
      exact False.elim (hx (properCuts_bounds _ _ h))

/-- No actual window of an inventory mate has more parts than the original inner factor. -/
theorem compositionWindow_length_le {M N : ℕ} (δ : Composition M) (ε : Composition N)
    (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε))
    (i : ℕ) (hi : i < M) : (compositionWindow θ N i).length ≤ ε.length := by
  classical
  let W := compositionWindow θ N i
  by_cases hle : W.length ≤ ε.length
  · exact hle
  · have hp : 0 < ε.length := ε.length_pos_of_pos hN
    have hmulti : 2 ≤ W.length := by omega
    let L := i * N
    let R := (M - 1 - i) * N
    have hadd : i + 1 + (M - 1 - i) = M := by omega
    have hweight : L + N + R = M * N := by
      calc
        L + N + R = (i + 1 + (M - 1 - i)) * N := by dsimp [L, R]; ring
        _ = M * N := by rw [hadd]
    let ζ := (paddedComposition W hN L R).cast hweight
    have hcuts : properCuts ζ ⊆ properCuts θ := by
      intro x hx
      change x ∈ properCuts ((paddedComposition W hN L R).cast hweight) at hx
      rw [properCuts_cast, paddedComposition_cuts] at hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hb := properCuts_bounds W y hy
      exact (compositionWindow_cuts θ N i y hb.1 hb.2).mp hy
    let μ := compositionPartition ζ
    have hM : 0 < M := by omega
    have hμ : μ ∈ coarseningInventory (compositionProduct δ ε) := by
      rw [← hInv]
      exact coarseningInventory_contains_composition θ ζ (Nat.mul_pos hM hN) hcuts
    have hL : N ∣ L := dvd_mul_of_dvd_right (dvd_refl N) i
    have hR : N ∣ R := dvd_mul_of_dvd_right (dvd_refl N) (M - 1 - i)
    have hres : residueWord ζ.blocks N = W.blocks :=
      paddedComposition_residueWord W hN hmulti L R hL hR
    have hsumWord := congrArg List.sum hres
    rw [residueWord_sum, W.blocks_sum] at hsumWord
    have hsum : (μ.map (fun a => a.val % N)).sum = N := by
      have hh := congrArg Multiset.sum (compositionPartition_residue_values ζ N)
      change (μ.map (fun a => a.val % N)).sum = (ζ.blocks.map (fun x => x % N)).sum at hh
      exact hh.trans hsumWord
    have hcount := congrArg Multiset.card (positivePartitionResidues_compositionPartition ζ N)
    change (positivePartitionResidues μ N).card = (residueWord ζ.blocks N).length at hcount
    rw [hres] at hcount
    have hbound := coarseningInventory_residue_bound δ ε hM hN μ hμ hsum
    rw [hcount] at hbound
    exact hbound

end SkewClassInflation
