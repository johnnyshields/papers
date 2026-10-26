/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ResiduePrefixWords

/-!
# Single-tour residues of actual ordinary-product coarsenings

The residue-count input to factor-reversal generation in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
If an actual adjacent coarsening's part residues make exactly one inner
weight, their positive residue word is an actual adjacent coarsening
of the inner.  In particular it cannot have more parts.  Sorry-free.
-/

namespace SkewClassInflation

/-- The positive residue word as an actual composition when its total makes one inner tour. -/
def residueComposition {K : ℕ} (ζ : Composition K) (n : ℕ)
    (hsum : (ζ.blocks.map (fun x => x % n)).sum = n) : Composition n where
  blocks := residueWord ζ.blocks n
  blocks_pos := by intro a ha; exact residueWord_pos ζ.blocks n a ha
  blocks_sum := (residueWord_sum ζ.blocks n).trans hsum

/-- The one-tour residue word retains only actual proper cuts of the original inner factor. -/
theorem residue_coarsening_cuts_subset {M N : ℕ} (γ : Composition M) (β : Composition N)
    (ζ : Composition (M * N))
    (hcuts : properCuts ζ ⊆ properCuts (compositionProduct γ β))
    (hsum : (ζ.blocks.map (fun x => x % N)).sum = N) :
    properCuts (residueComposition ζ N hsum) ⊆ properCuts β := by
  intro y hy
  have hb := properCuts_bounds (residueComposition ζ N hsum) y hy
  have hword : y ∈ wordProperCuts (residueWord ζ.blocks N) := by
    change y ∈ wordProperCuts (residueComposition ζ N hsum).blocks
    rw [wordProperCuts_blocks]
    exact hy
  have hpref := (wordProperCuts_prefixEnds_of_lt (residueWord ζ.blocks N) y
    (by rw [residueWord_sum, hsum]; exact hb.2)).mp hword
  rw [residueWord, prefixEnds_filter_nonzero] at hpref
  have hraw := (Finset.mem_erase.mp hpref).2
  obtain ⟨i, hi0, hilen, hpart⟩ :=
    (prefixEnds_mem_partial (ζ.blocks.map (fun x => x % N)) y).mp hraw
  have hlen : i ≤ ζ.blocks.length := by simpa only [List.length_map] using hilen
  have hlt : i < ζ.blocks.length := by
    by_contra he
    have hfull : i = (ζ.blocks.map (fun x => x % N)).length := by
      simp only [List.length_map]
      omega
    rw [hfull, List.take_length, hsum] at hpart
    omega
  let X := (ζ.blocks.take i).sum
  have hX : X ∈ properCuts ζ := by
    rw [← wordProperCuts_blocks]
    exact (wordProperCuts_mem_partial ζ.blocks X).mpr ⟨i, hi0, hlt, rfl⟩
  have hProd := hcuts hX
  have hXbounds := properCuts_bounds (compositionProduct γ β) X hProd
  have hmod : X % N = y := by
    have hh := sum_mod_map (ζ.blocks.take i) N
    rw [← List.map_take] at hpart
    rw [hpart, Nat.mod_eq_of_lt hb.2] at hh
    exact hh.symm
  have hinner := (compositionProduct_internal γ β X hXbounds.1 hXbounds.2
    (by rw [hmod]; exact Nat.ne_of_gt hb.1)).mp hProd
  rwa [hmod] at hinner

/-- A one-tour residue coarsening has at most the inner's actual number of positive parts. -/
theorem residue_coarsening_length_bound {M N : ℕ} (γ : Composition M) (β : Composition N)
    (hN : 0 < N) (ζ : Composition (M * N))
    (hcuts : properCuts ζ ⊆ properCuts (compositionProduct γ β))
    (hsum : (ζ.blocks.map (fun x => x % N)).sum = N) :
    (residueWord ζ.blocks N).length ≤ β.length := by
  let R := residueComposition ζ N hsum
  have hsub := residue_coarsening_cuts_subset γ β ζ hcuts hsum
  have hle := Finset.card_le_card hsub
  change (properCuts R).card ≤ (properCuts β).card at hle
  have hR := suffixSet_card R.reverse hN
  have hβ := suffixSet_card β.reverse hN
  rw [← properCuts_eq_suffixSet R] at hR
  rw [← properCuts_eq_suffixSet β] at hβ
  have hlenR : R.reverse.length = (residueWord ζ.blocks N).length := by
    simp only [Composition.length, Composition.reverse_blocks, List.length_reverse]
    rfl
  have hlenβ : β.reverse.length = β.length := by
    simp only [Composition.length, Composition.reverse_blocks, List.length_reverse]
  rw [hlenR] at hR
  rw [hlenβ] at hβ
  omega

end SkewClassInflation
