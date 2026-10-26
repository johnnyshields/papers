/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.DisconnectedTableau
import SkewGluing.FiniteSchurProduct

/-!
# Component products of complete overlapping diagrams

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). Whole overlapping components are counted once in
the union and once in the intersection. The complete functions retain their multiplicities.
Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- A separated exclusive piece yields the exact union/intersection product identity. -/
theorem cellSchur_complete_overlap (A B : Diagram) (hA : IsSkew A) (hB : IsSkew B)
    (hU : IsSkew (A ∪ B))
    (hsep : ∀ x ∈ A \ B, ∀ y ∈ B, ¬ CellAdj x y) :
    ∃ hI : IsSkew (A ∩ B),
      cellSchur (A ∪ B) hU * cellSchur (A ∩ B) hI = cellSchur A hA * cellSchur B hB := by
  have hAU : (A \ B) ∪ (A ∩ B) = A := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hBU : (A \ B) ∪ B = A ∪ B := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hAs : IsSkew ((A \ B) ∪ (A ∩ B)) := by rwa [hAU]
  have hUs : IsSkew ((A \ B) ∪ B) := by rwa [hBU]
  have hsepI : ∀ x ∈ A \ B, ∀ y ∈ A ∩ B, ¬ CellAdj x y :=
    fun x hx y hy => hsep x hx y (Finset.mem_inter.mp hy).2
  have hX : IsSkew (A \ B) := hAs.union_left_of_noAdj hsepI
  have hI : IsSkew (A ∩ B) :=
    (show IsSkew ((A ∩ B) ∪ (A \ B)) by rwa [Finset.union_comm]).union_left_of_noAdj
      (fun x hx y hy ha => hsepI y hy x hx ha.symm')
  have hdB : Disjoint (A \ B) B := by
    rw [Finset.disjoint_left]
    exact fun x hx hy => (Finset.mem_sdiff.mp hx).2 hy
  have hdI : Disjoint (A \ B) (A ∩ B) := hdB.mono_right Finset.inter_subset_right
  have hprodU := cellSchur_union hX hB hUs hdB hsep
  have hprodA := cellSchur_union hX hI hAs hdI hsepI
  rw [cellSchur_congr hBU hUs hU] at hprodU
  rw [cellSchur_congr hAU hAs hA] at hprodA
  refine ⟨hI, ?_⟩
  rw [hprodU, hprodA]
  ring

end SkewCornerDescent
