/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PartitionOrderCounts
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm

/-!
# Labeled index permutations of actual partition orders

The arbitrary-length ordered-count input for factor-reversal
reconstruction in `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Sorting identifies an actual
index permutation for every unordered word, including repeated parts.
No distinct-part hypothesis is imposed.  Sorry-free.
-/

namespace SkewClassInflation

/-- Permutation-equivalent finite tuples differ by an actual index permutation. -/
theorem tuple_perm_exists_index_perm {A : Type*} [LinearOrder A] {n : ℕ}
    (f g : Fin n → A) (he : (List.ofFn g).Perm (List.ofFn f)) :
    ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  have hs : (List.ofFn (f ∘ Tuple.sort f)).Perm (List.ofFn (g ∘ Tuple.sort g)) :=
    ((Tuple.sort f).ofFn_comp_perm f).trans
      (he.symm.trans ((Tuple.sort g).ofFn_comp_perm g).symm)
  have hfun : f ∘ Tuple.sort f = g ∘ Tuple.sort g :=
    List.ofFn_injective (hs.eq_of_pairwise'
      (Tuple.monotone_sort f).sortedLE_ofFn.pairwise
      (Tuple.monotone_sort g).sortedLE_ofFn.pairwise)
  refine ⟨(Tuple.sort g).symm.trans (Tuple.sort f), ?_⟩
  funext i
  have hh := congrFun hfun ((Tuple.sort g).symm i)
  simpa only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] using hh

/-- Every unordered natural word of a tuple has an actual labeled index presentation. -/
theorem word_perm_exists_index_perm {n : ℕ} (f : Fin n → ℕ) (w : List ℕ)
    (he : w.Perm (List.ofFn f)) :
    ∃ σ : Equiv.Perm (Fin n), List.ofFn (f ∘ σ) = w := by
  induction w using List.ofFnRec with
  | h m g =>
    have hm : m = n := by simpa only [List.length_ofFn] using he.length_eq
    subst m
    obtain ⟨σ, hσ⟩ := tuple_perm_exists_index_perm f g he
    exact ⟨σ, congrArg List.ofFn hσ⟩

/-- Actual unordered partition orders are the image of all labeled index permutations. -/
theorem partitionOrders_ofFn_perms {n : ℕ} (f : Fin n → ℕ+) :
    partitionOrders (List.ofFn f) =
      Finset.univ.image (fun σ : Equiv.Perm (Fin n) =>
        List.ofFn (fun i => (f (σ i)).val)) := by
  classical
  ext w
  constructor
  · intro hw
    have hp : w.Perm (List.ofFn (fun i => (f i).val)) := by
      have hh := List.mem_permutations.mp (List.mem_toFinset.mp hw)
      simpa only [List.map_ofFn, Function.comp_def] using hh
    obtain ⟨σ, hσ⟩ := word_perm_exists_index_perm (fun i => (f i).val) w hp
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
  · intro hw
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hw
    have hp := σ.ofFn_comp_perm (fun i => (f i).val)
    apply List.mem_toFinset.mpr
    apply List.mem_permutations.mpr
    simpa only [List.map_ofFn, Function.comp_def] using hp

end SkewClassInflation
