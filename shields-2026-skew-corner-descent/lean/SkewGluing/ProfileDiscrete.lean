/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.ComponentOrders

/-!
# Unit row gaps in a saturated discrete interior

Formalizes `shields-2026-skew-corner-descent.tex`, «Period comparison and polynomial
obstructions» (`sec:periods`, `lem:alpha-row-candidate`, `def:discrete-interior`).
The gap conclusion applies to every translated profile presentation.

Sorry-free.
-/

namespace SkewGluing

/-- Isolated interior cells cannot share a row. -/
theorem HasDiscreteInterior.eq_of_same_row {D : Diagram} (hD : IsSkew D)
    (hd : HasDiscreteInterior D) {x y : ℤ × ℤ}
    (hx : x ∈ diagramInterior D) (hy : y ∈ diagramInterior D) (he : x.1 = y.1) : x = y := by
  have hxu : x ∈ (edgeComponents (diagramInterior D)).biUnion id := by
    rw [biUnion_edgeComponents]; exact hx
  have hyu : y ∈ (edgeComponents (diagramInterior D)).biUnion id := by
    rw [biUnion_edgeComponents]; exact hy
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hxu
  obtain ⟨C', hC', hyC⟩ := Finset.mem_biUnion.mp hyu
  have hc := component_eq_of_row hD.interior hC hC' hxC hyC he
  subst C'
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hd C hC)
  simp only [hz, id_eq, Finset.mem_singleton] at hxC hyC
  exact hxC.trans hyC.symm

namespace Profile
variable {n : ℕ}

/-- The interior area is the sum of the profile's adjacent row gaps. -/
theorem interior_card_eq_sum_g (P : Profile n) :
    (diagramInterior P.cells).card = ∑ i : Fin n, P.g i := by
  classical
  rw [P.interior_cells_eq_minorCells]
  unfold minorCells
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_image_of_injective _]
    · rw [Int.card_Ico]
      have hg := P.xi_succ_sub_zeta_castSucc i
      omega
    · intro b c he
      exact (Prod.mk.inj he).2
  · intro i _ j _ hij
    change Disjoint
      ((Finset.Ico (P.zeta i.castSucc + i) (P.xi i.succ + i)).image fun b => ((i : ℤ), b))
      ((Finset.Ico (P.zeta j.castSucc + j) (P.xi j.succ + j)).image fun b => ((j : ℤ), b))
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hz
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hz'
    have he := congrArg Prod.fst (hb.trans hc.symm)
    change ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) at he
    apply hij
    apply Fin.ext
    exact_mod_cast he

/-- Discrete actual interiors make every row gap zero or one. -/
theorem gaps_le_one_of_discrete (P : Profile n) {D : Diagram} (v : ℤ × ℤ)
    (h : D = translate v P.cells) (hd : HasDiscreteInterior D) : ∀ i, P.g i ≤ 1 := by
  classical
  intro i
  by_contra hn
  let b : ℤ := P.zeta i.castSucc + i
  have hg := P.xi_succ_sub_zeta_castSucc i
  have hx : ((i : ℤ), b) ∈ diagramInterior P.cells := by
    rw [P.mem_interior_cells]
    exact ⟨i, rfl, le_rfl, by dsimp [b]; omega⟩
  have hy : ((i : ℤ), b + 1) ∈ diagramInterior P.cells := by
    rw [P.mem_interior_cells]
    exact ⟨i, rfl, by dsimp [b]; omega, by dsimp [b]; omega⟩
  have hxD : ((i : ℤ), b) + v ∈ diagramInterior D := by
    rw [h, interior_translate]
    exact mem_translate.mpr (by simpa only [add_sub_cancel_right] using hx)
  have hyD : ((i : ℤ), b + 1) + v ∈ diagramInterior D := by
    rw [h, interior_translate]
    exact mem_translate.mpr (by simpa only [add_sub_cancel_right] using hy)
  have hD : IsSkew D := h ▸ isSkew_translate v P.isConnectedSkew_cells.1
  have he := hd.eq_of_same_row hD hxD hyD rfl
  have he' := congrArg Prod.snd he
  change b + v.2 = b + 1 + v.2 at he'
  omega

/-- Saturating all adjacent row slots forces every row gap to be one. -/
theorem gaps_eq_one_of_discrete_row_count (P : Profile n) {D : Diagram} (v : ℤ × ℤ)
    (h : D = translate v P.cells) (hd : HasDiscreteInterior D)
    (hr : (D.image Prod.fst).card = (diagramInterior D).card + 1) : ∀ i, P.g i = 1 := by
  classical
  have hn : (diagramInterior P.cells).card = n := by
    rw [h, rowCount_translate, P.rowCount_cells, interior_translate] at hr
    change n + 1 = (GluingCore.translate v (diagramInterior P.cells)).card + 1 at hr
    rw [GluingCore.card_translate] at hr
    omega
  have hsum : (∑ i : Fin n, P.g i) = n := P.interior_card_eq_sum_g.symm.trans hn
  have hle := P.gaps_le_one_of_discrete v h hd
  intro i
  by_contra hi
  have hli := hle i
  have hh : (∑ j : Fin n, P.g j) < ∑ _j : Fin n, 1 := by
    apply Finset.sum_lt_sum
    · intro j _
      exact hle j
    · exact ⟨i, Finset.mem_univ _, by omega⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hh
  omega

end Profile
end SkewGluing
