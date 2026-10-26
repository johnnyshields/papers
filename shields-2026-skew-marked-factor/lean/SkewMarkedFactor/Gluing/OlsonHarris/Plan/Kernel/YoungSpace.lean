/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/Kernel/YoungSpace.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Kernel.Independence
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Kernel.Ribbons

/-!
# Ribbon addition on Young diagrams and ribbon removal on skew shapes

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.2 (`OlsonHarris2024HopfApplications`).

The free space `YoungSpace` on Young diagrams carries the operators `addRibbon m` (the
multiplication by `p_m`, in the Schur basis) and the linear maps `skewShapeMap λ` sending the
basis element `σ` to the shape `[λ / σ]` (zero unless `σ ≤ λ`).  The two intertwine `addRibbon m`
with the removal `leftOp m` of a ribbon from the northwest, so that the word `p_ν` applied to `∅`
in the Schur basis gives the action of `p_ν` on the Ferrers shape `[λ]` by `leftWord ν`.

Uses `pPoly_mul_cellSchur_ferrers`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace KernelAux

open MvPolynomial Shields

/-- The free space on Young diagrams. -/
abbrev YoungSpace : Type := YoungDiagram →₀ ℚ

/-- `σ ↦ s_σ`. -/
noncomputable def ferrersMap : YoungSpace →ₗ[ℚ] Lambda := Finsupp.linearCombination ℚ ferrersSchur

/-- `σ ↦ [σ]`, the Ferrers shape. -/
noncomputable def ferrersShape : YoungSpace →ₗ[ℚ] ShapeSpace :=
  Finsupp.linearCombination ℚ fun sigma => shape (skewDiagram sigma ⊥)

/-- Adding a ribbon of size `m`: `ρ ↦ Σ_σ (-1)^{ht(σ/ρ)} σ`. -/
noncomputable def addRibbon (m : ℕ) : YoungSpace →ₗ[ℚ] YoungSpace :=
  Finsupp.linearCombination ℚ fun rho =>
    ∑ sigma ∈ ribbonAdds rho m, (ribbonSign (skewDiagram sigma rho) : ℚ) • Finsupp.single sigma 1

/-- Adding the ribbons of a word, the first one first. -/
noncomputable def addWord : List ℕ → YoungSpace →ₗ[ℚ] YoungSpace
  | [] => LinearMap.id
  | m :: nu => (addWord nu).comp (addRibbon m)

open Classical in
/-- `σ ↦ [λ / σ]` for `σ ≤ λ`, and `0` otherwise. -/
noncomputable def skewShapeMap (lam : YoungDiagram) : YoungSpace →ₗ[ℚ] ShapeSpace :=
  Finsupp.linearCombination ℚ fun sigma =>
    if sigma ≤ lam then shape (skewDiagram lam sigma) else 0

theorem ferrersMap_single (sigma : YoungDiagram) (c : ℚ) :
    ferrersMap (Finsupp.single sigma c) = c • ferrersSchur sigma := by
  simp [ferrersMap, Finsupp.linearCombination_single]

theorem addRibbon_single (m : ℕ) (rho : YoungDiagram) (c : ℚ) :
    addRibbon m (Finsupp.single rho c) =
      c • ∑ sigma ∈ ribbonAdds rho m,
        (ribbonSign (skewDiagram sigma rho) : ℚ) • Finsupp.single sigma 1 := by
  simp [addRibbon, Finsupp.linearCombination_single]

theorem ferrersMap_addRibbon {m : ℕ} (hm : 0 < m) (y : YoungSpace) :
    ferrersMap (addRibbon m y) = pPoly m * ferrersMap y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, mul_add]
  | single rho c =>
    rw [addRibbon_single, ferrersMap_single, map_smul, map_sum]
    simp only [map_smul, ferrersMap_single, one_smul]
    rw [Algebra.mul_smul_comm, pPoly_mul_ferrersSchur rho hm]
    congr 1
    exact Finset.sum_congr rfl fun sigma _ => (intCast_mul_eq_smul _ _).symm

theorem skewDiagram_mono_left {rho sigma lam : YoungDiagram} (h : sigma ≤ lam) :
    skewDiagram sigma rho ⊆ skewDiagram lam rho := by
  intro x hx
  obtain ⟨i, j, rfl, h1, h2⟩ := mem_skewDiagram_iff.mp hx
  exact mem_skewDiagram_iff.mpr ⟨i, j, rfl, h h1, h2⟩

theorem skewDiagram_subset_bot {lam rho : YoungDiagram} :
    skewDiagram lam rho ⊆ skewDiagram lam ⊥ := by
  intro x hx
  obtain ⟨i, j, rfl, h1, _⟩ := mem_skewDiagram_iff.mp hx
  exact mem_skewDiagram_bot.mpr h1

/-- A downset of the skew shape `λ / ρ` is a skew shape `σ / ρ` for a Young diagram
`σ` between `ρ` and `λ`. -/
theorem exists_young_of_downset {lam rho : YoungDiagram} (hrl : rho ≤ lam) {Y : Diagram}
    (hY : IsDownsetIn (skewDiagram lam rho) Y) :
    ∃ sigma : YoungDiagram, rho ≤ sigma ∧ sigma ≤ lam ∧ skewDiagram sigma rho = Y := by
  have hYsub : ∀ y ∈ Y, ∃ i j : ℕ, y = ((i : ℤ), (j : ℤ)) ∧ (i, j) ∈ lam ∧ (i, j) ∉ rho :=
    fun y hy => mem_skewDiagram_iff.mp (hY.1 hy)
  have hnn : ∀ x ∈ skewDiagram rho ⊥ ∪ Y, 0 ≤ x.1 ∧ 0 ≤ x.2 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact nonneg_of_mem_skewDiagram hx
    · obtain ⟨i, j, rfl, _⟩ := hYsub x hx
      exact ⟨Int.natCast_nonneg i, Int.natCast_nonneg j⟩
  have hlow : ∀ x ∈ skewDiagram rho ⊥ ∪ Y, ∀ i j : ℕ, (i : ℤ) ≤ x.1 → (j : ℤ) ≤ x.2 →
      ((i : ℤ), (j : ℤ)) ∈ skewDiagram rho ⊥ ∪ Y := by
    intro x hx i j hi hj
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, b, rfl⟩ := nat_cell_of_mem_skewDiagram hx
      have hab := mem_skewDiagram_bot.mp hx
      refine Finset.mem_union_left _ (mem_skewDiagram_bot.mpr (rho.up_left_mem ?_ ?_ hab))
      · simpa using hi
      · simpa using hj
    · obtain ⟨a, b, rfl, h1, h2⟩ := hYsub x hx
      have hi' : i ≤ a := by simpa using hi
      have hj' : j ≤ b := by simpa using hj
      have hij : (i, j) ∈ lam := lam.up_left_mem hi' hj' h1
      by_cases hr : (i, j) ∈ rho
      · exact Finset.mem_union_left _ (mem_skewDiagram_bot.mpr hr)
      · refine Finset.mem_union_right _ (hY.2 _ (mem_skewDiagram_iff.mpr ⟨i, j, rfl, hij, hr⟩)
          _ hx ?_ ?_)
        · exact hi
        · exact hj
  obtain ⟨sigma, hsigma⟩ := exists_young_of_lowerSet hnn hlow
  have hrs : rho ≤ sigma := by
    rw [← skewDiagram_bot_subset_iff, hsigma]
    exact Finset.subset_union_left
  have hsl : sigma ≤ lam := by
    rw [← skewDiagram_bot_subset_iff, hsigma]
    refine Finset.union_subset ?_ ?_
    · exact skewDiagram_bot_subset_iff.mpr hrl
    · exact fun y hy => skewDiagram_subset_bot (hY.1 hy)
  refine ⟨sigma, hrs, hsl, ?_⟩
  rw [skewDiagram_eq_sdiff hrs, hsigma]
  ext x
  rw [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hn⟩
    · exact absurd h hn
    · exact h
  · intro hx
    obtain ⟨i, j, rfl, h1, h2⟩ := hYsub x hx
    exact ⟨Or.inr hx, fun h => h2 (mem_skewDiagram_bot.mp h)⟩

open Classical in
theorem skewShapeMap_single (lam rho : YoungDiagram) (c : ℚ) :
    skewShapeMap lam (Finsupp.single rho c) =
      if rho ≤ lam then c • shape (skewDiagram lam rho) else 0 := by
  classical
  unfold skewShapeMap
  rw [Finsupp.linearCombination_single]
  by_cases h : rho ≤ lam <;> simp [h]

theorem isDownsetIn_skewDiagram {rho sigma lam : YoungDiagram} (h2 : sigma ≤ lam) :
    IsDownsetIn (skewDiagram lam rho) (skewDiagram sigma rho) := by
  refine ⟨skewDiagram_mono_left h2, fun x hx y hy hxy1 hxy2 => ?_⟩
  obtain ⟨i, j, rfl, a1, a2⟩ := mem_skewDiagram_iff.mp hx
  obtain ⟨k, l, rfl, b1, _⟩ := mem_skewDiagram_iff.mp hy
  have hik : i ≤ k := by simpa using hxy1
  have hjl : j ≤ l := by simpa using hxy2
  exact mem_skewDiagram_iff.mpr ⟨i, j, rfl, sigma.up_left_mem hik hjl b1, a2⟩

open Classical in
theorem sum_ribbonAdds_eq_leftOp {lam rho : YoungDiagram} (hrl : rho ≤ lam) (m : ℕ) :
    ∑ sigma ∈ ribbonAdds rho m, (ribbonSign (skewDiagram sigma rho) : ℚ) •
        (if sigma ≤ lam then shape (skewDiagram lam sigma) else 0) =
      leftOp m (shape (skewDiagram lam rho)) := by
  rw [KernelAux.leftOp_shape]
  have hsplit : ∀ sigma ∈ ribbonAdds rho m, ((ribbonSign (skewDiagram sigma rho) : ℚ) •
      if sigma ≤ lam then shape (skewDiagram lam sigma) else 0) =
      if sigma ≤ lam then (ribbonSign (skewDiagram sigma rho) : ℚ) •
        shape (skewDiagram lam sigma) else 0 := by
    intro sigma _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hsplit, ← Finset.sum_filter]
  refine Finset.sum_bij (fun sigma _ => skewDiagram sigma rho) ?_ ?_ ?_ ?_
  · intro sigma hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hr1, hr2, hr3⟩ := mem_ribbonAdds.mp hs.1
    rw [mem_leftRibbons]
    exact ⟨skewDiagram_mono_left hs.2, hr3, hr2, isDownsetIn_skewDiagram hs.2⟩
  · intro s1 h1 s2 h2 h
    rw [Finset.mem_filter] at h1 h2
    have e1 := (mem_ribbonAdds.mp h1.1).1
    have e2 := (mem_ribbonAdds.mp h2.1).1
    have hu : ∀ s : YoungDiagram, rho ≤ s → skewDiagram s ⊥ =
        skewDiagram s rho ∪ skewDiagram rho ⊥ := by
      intro s hs
      rw [skewDiagram_eq_sdiff hs, Finset.sdiff_union_of_subset
        (skewDiagram_bot_subset_iff.mpr hs)]
    apply skewDiagram_bot_injective
    simp only []
    rw [hu s1 e1, hu s2 e2, h]
  · intro Y hY
    rw [mem_leftRibbons] at hY
    obtain ⟨_, hc, hr, hd⟩ := hY
    obtain ⟨sigma, hs1, hs2, rfl⟩ := exists_young_of_downset hrl hd
    refine ⟨sigma, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨mem_ribbonAdds.mpr ⟨hs1, hr, hc⟩, hs2⟩
  · intro sigma hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hr1, _, _⟩ := mem_ribbonAdds.mp hs.1
    rw [skewDiagram_sdiff hr1]

theorem skewShapeMap_addRibbon_single (m : ℕ) (lam rho : YoungDiagram) :
    skewShapeMap lam (addRibbon m (Finsupp.single rho 1)) =
      leftOp m (skewShapeMap lam (Finsupp.single rho 1)) := by
  rw [addRibbon_single, one_smul, map_sum]
  simp only [map_smul, skewShapeMap_single, one_smul]
  by_cases hrl : rho ≤ lam
  · simp only [hrl, ite_true]
    exact sum_ribbonAdds_eq_leftOp hrl m
  · simp only [hrl, ite_false, map_zero]
    refine Finset.sum_eq_zero fun sigma hs => ?_
    have : ¬ sigma ≤ lam := fun h => hrl ((mem_ribbonAdds.mp hs).1.trans h)
    simp [this]

theorem skewShapeMap_addRibbon (m : ℕ) (lam : YoungDiagram) (y : YoungSpace) :
    skewShapeMap lam (addRibbon m y) = leftOp m (skewShapeMap lam y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | single rho c =>
    have : Finsupp.single rho c = c • Finsupp.single rho (1 : ℚ) := by simp
    rw [this, map_smul, map_smul, map_smul, map_smul, skewShapeMap_addRibbon_single]

theorem skewShapeMap_addWord (nu : List ℕ) (lam : YoungDiagram) (y : YoungSpace) :
    skewShapeMap lam (addWord nu y) = leftWord nu (skewShapeMap lam y) := by
  induction nu generalizing y with
  | nil => rfl
  | cons m nu ih =>
    simp only [addWord, leftWord, LinearMap.comp_apply]
    rw [ih, skewShapeMap_addRibbon]

theorem ferrersMap_addWord {nu : List ℕ} (hnu : ∀ m ∈ nu, 0 < m) (y : YoungSpace) :
    ferrersMap (addWord nu y) = pProd nu * ferrersMap y := by
  induction nu generalizing y with
  | nil => simp [addWord, pProd]
  | cons m nu ih =>
    have hm : 0 < m := hnu m List.mem_cons_self
    have hnu' : ∀ k ∈ nu, 0 < k := fun k hk => hnu k (List.mem_cons_of_mem _ hk)
    simp only [addWord, LinearMap.comp_apply]
    rw [ih hnu', ferrersMap_addRibbon hm]
    simp only [pProd, List.map_cons, List.prod_cons]
    ring

end KernelAux

end Plan

end SkewMarkedFactor.Gluing
