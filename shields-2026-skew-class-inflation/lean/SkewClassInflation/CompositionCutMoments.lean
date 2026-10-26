/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorWindowReflection

/-!
# Ordered prefix sums and actual cut moments

The finite ordered-set rigidity used for factor transport in
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Coordinatewise ordered cut lists with the same first moment coincide.
The coordinates are actual composition prefix sums, not independent data.
Sorry-free.
-/

namespace SkewClassInflation

/-- Internal prefix ranks enumerate the complete actual proper-cut set. -/
theorem properCuts_eq_sizeUpTo_image {N : ℕ} (α : Composition N) :
    properCuts α = (Finset.Ioo 0 α.length).image α.sizeUpTo := by
  ext x
  rw [← wordProperCuts_blocks, wordProperCuts_mem_partial]
  simp only [Finset.mem_image, Finset.mem_Ioo, Composition.sizeUpTo]
  exact exists_congr (fun _ => and_assoc.symm)

/-- Distinct proper prefix ranks have distinct actual cut coordinates. -/
theorem sizeUpTo_injOn_internal {N : ℕ} (α : Composition N) :
    Set.InjOn α.sizeUpTo (Finset.Ioo 0 α.length : Set ℕ) := by
  intro i hi j hj he
  have hib := (Finset.mem_Ioo.mp hi).2
  have hjb := (Finset.mem_Ioo.mp hj).2
  have hf : α.boundary ⟨i, by omega⟩ = α.boundary ⟨j, by omega⟩ := Fin.ext he
  exact congrArg Fin.val (α.boundary.injective hf)

/-- Summing the actual cut coordinates agrees with summing their ordered prefix ranks. -/
theorem properCuts_sum_sizeUpTo {N : ℕ} (α : Composition N) :
    (∑ x ∈ properCuts α, (x : ℤ)) =
      ∑ t ∈ Finset.Ioo 0 α.length, (α.sizeUpTo t : ℤ) := by
  rw [properCuts_eq_sizeUpTo_image, Finset.sum_image]
  exact sizeUpTo_injOn_internal α

/-- Complete equality at proper prefix ranks identifies the actual composition. -/
theorem composition_eq_of_sizeUpTo_internal {N : ℕ} (α β : Composition N)
    (hlen : α.length = β.length)
    (hprefix : ∀ t ∈ Finset.Ioo 0 α.length, α.sizeUpTo t = β.sizeUpTo t) : α = β := by
  apply properCuts_injective
  rw [properCuts_eq_sizeUpTo_image, properCuts_eq_sizeUpTo_image, ← hlen]
  exact Finset.image_congr hprefix

/-- An ordered pair of complete cut lists with equal first moments is identical. -/
theorem composition_eq_of_ordered_cut_sums {N : ℕ} (α β : Composition N)
    (hlen : α.length = β.length)
    (hprefix : ∀ t ∈ Finset.Ioo 0 α.length, α.sizeUpTo t ≤ β.sizeUpTo t)
    (hsum : (∑ x ∈ properCuts α, (x : ℤ)) = ∑ x ∈ properCuts β, (x : ℤ)) : α = β := by
  rw [properCuts_sum_sizeUpTo, properCuts_sum_sizeUpTo, ← hlen] at hsum
  have hle : ∀ t ∈ Finset.Ioo 0 α.length, (α.sizeUpTo t : ℤ) ≤ β.sizeUpTo t := by
    intro t ht
    exact_mod_cast hprefix t ht
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  apply composition_eq_of_sizeUpTo_internal α β hlen
  intro t ht
  exact_mod_cast he t ht

end SkewClassInflation
