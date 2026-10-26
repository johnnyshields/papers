/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PrefixSpliceResidues

/-!
# Ordered prefix positions in ordinary-product mates

The monotone-window step in factor transport for `thm:sharp-inflation`
of `shields-2026-skew-class-inflation.tex`.  A crossing pair of matching
prefix positions supplies an actual full-weight coarsening whose one-tour
residue word has too many parts.  Sorry-free.
-/

namespace SkewClassInflation

/-- The one-tour residue bound holds for every actual coarsening of an inventory mate. -/
theorem mate_coarsening_residue_bound {M N : ℕ} (δ : Composition M) (ε : Composition N)
    (hM : 0 < M) (hN : 0 < N) (θ ζ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε))
    (hcuts : properCuts ζ ⊆ properCuts θ)
    (hsum : (residueWord ζ.blocks N).sum = N) :
    (residueWord ζ.blocks N).length ≤ ε.length := by
  let μ := compositionPartition ζ
  have hμ : μ ∈ coarseningInventory (compositionProduct δ ε) := by
    rw [← hInv]
    exact coarseningInventory_contains_composition θ ζ (Nat.mul_pos hM hN) hcuts
  have hm := congrArg Multiset.sum (compositionPartition_residue_values ζ N)
  have hsum' : (μ.map (fun a => a.val % N)).sum = N := by
    change (μ.map (fun a => a.val % N)).sum = (ζ.blocks.map (fun x => x % N)).sum at hm
    exact hm.trans ((residueWord_sum ζ.blocks N).symm.trans hsum)
  have hc := coarseningInventory_residue_bound δ ε hM hN μ hμ hsum'
  have he := congrArg Multiset.card (positivePartitionResidues_compositionPartition ζ N)
  change (positivePartitionResidues μ N).card = (residueWord ζ.blocks N).length at he
  rwa [he] at hc

/-- Matching internal prefix positions cannot increase from one copy window to a later one. -/
theorem compositionWindow_prefix_antitone {M N : ℕ} (δ : Composition M) (ε : Composition N)
    (hN : 0 < N) (θ : Composition (M * N))
    (hInv : coarseningInventory θ = coarseningInventory (compositionProduct δ ε))
    (i j t : ℕ) (hij : i < j) (hj : j < M) (ht0 : 0 < t) (ht : t < ε.length) :
    ((compositionWindow θ N j).blocks.take t).sum ≤
      ((compositionWindow θ N i).blocks.take t).sum := by
  classical
  let u := compositionWindow θ N i
  let v := compositionWindow θ N j
  have hi : i < M := by omega
  have hul : u.length = ε.length := compositionWindow_length_eq δ ε hN θ hInv i hi
  have hvl : v.length = ε.length := compositionWindow_length_eq δ ε hN θ hInv j hj
  have htu : t < u.length := by omega
  have htv : t < v.length := by omega
  by_contra hle
  have hab : (u.blocks.take t).sum < (v.blocks.take t).sum := Nat.lt_of_not_ge hle
  let a := (u.blocks.take t).sum
  let b := (v.blocks.take t).sum
  let gap := (j - i) * N + (b - a)
  let w := u.blocks.take t ++ gap :: v.blocks.drop t
  have hsumv := List.sum_take_add_sum_drop v.blocks t
  rw [v.blocks_sum] at hsumv
  have hsumw : w.sum = (j - i) * N + N := by
    dsimp only [w]
    rw [List.sum_append, List.sum_cons]
    dsimp only [gap, a, b] at *
    omega
  have hpos : ∀ x ∈ w, 0 < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact u.blocks_pos (List.mem_of_mem_take hx)
    · rcases List.mem_cons.mp hx with rfl | hx
      · dsimp only [gap, a, b]
        omega
      · exact v.blocks_pos (List.mem_of_mem_drop hx)
  let Γ : Composition w.sum := ⟨w, fun {x} hx => hpos x hx, rfl⟩
  have hΓ : 0 < w.sum := by rw [hsumw]; omega
  let L := i * N
  let R := (M - 1 - j) * N
  have hindices : i + (j - i) + 1 + (M - 1 - j) = M := by omega
  have hweight : L + w.sum + R = M * N := by
    rw [hsumw]
    calc
      _ = (i + (j - i) + 1 + (M - 1 - j)) * N := by dsimp [L, R]; ring
      _ = M * N := by rw [hindices]
  let ζ := (paddedComposition Γ hΓ L R).cast hweight
  have hjoin : L + (u.blocks.take t).sum + gap = j * N + (v.blocks.take t).sum := by
    have hji : i + (j - i) = j := by omega
    have hmul := congrArg (fun x => x * N) hji
    dsimp only [L, gap, a, b]
    rw [Nat.add_mul] at hmul
    omega
  have hcuts : properCuts ζ ⊆ properCuts θ := by
    intro x hx
    change x ∈ properCuts ((paddedComposition Γ hΓ L R).cast hweight) at hx
    rw [properCuts_cast, paddedComposition_cuts, ← wordProperCuts_blocks Γ] at hx
    have hs := word_splice_cuts_subset u.blocks v.blocks t gap L (j * N)
      ht0 htu htv hjoin hx
    rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
      rw [wordProperCuts_blocks] at hy
      have hb := properCuts_bounds u y hy
      exact (compositionWindow_cuts θ N i y hb.1 hb.2).mp hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
      rw [wordProperCuts_blocks] at hy
      have hb := properCuts_bounds v y hy
      exact (compositionWindow_cuts θ N j y hb.1 hb.2).mp hy
  have hne : w ≠ [] := fun he => (Nat.ne_of_gt hΓ) (Γ.blocks_eq_nil.mp he)
  have hres : residueWord ζ.blocks N = residueWord w N :=
    residueWord_wordPadEnds w L R N hne
      (dvd_mul_of_dvd_right (dvd_refl N) i)
      (dvd_mul_of_dvd_right (dvd_refl N) (M - 1 - j))
  have hu : 2 ≤ u.length := by omega
  have hv : 2 ≤ v.length := by omega
  have hsum : (residueWord ζ.blocks N).sum = N := by
    rw [hres]
    exact splice_residue_sum u v hN t (j - i) hu hv hab
  have hlen : (residueWord ζ.blocks N).length = ε.length + 1 := by
    rw [hres]
    exact (splice_residue_length u v hN t (j - i) hu hv (hul.trans hvl.symm) htu hab).trans
      (congrArg (fun x => x + 1) hul)
  have hbound := mate_coarsening_residue_bound δ ε (by omega) hN θ ζ hInv hcuts hsum
  omega

end SkewClassInflation
