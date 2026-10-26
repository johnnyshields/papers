/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.IntegralCofactor
import SkewGluing.ProfileStatistics
import SkewGluing.FieldIrreducibility
import SkewCornerDescent.Matrix.GeneratorSpan

/-!
# Geometric corner cofactor assembly

Formalizes `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `lem:cofactor`, `eq:corner-intro`, `eq:corner-factors`). All intermediate
profile and tableau inputs are supplied by proved declarations. The connected diagram,
not a chosen presentation, determines the generator span, row sign, and interior cofactor.
Sorry-free.
-/

namespace SkewGluing
open MvPolynomial
noncomputable section

/-- The integral component product of a connected diagram is its canonical integral function. -/
theorem integralCellSchur_eq_connected {D : Diagram} (hD : IsConnectedSkew D) :
    integralCellSchur D hD.1 = integralConnectedSchur D hD := by
  apply map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
  simpa only [map_integralCellSchur, map_integralConnectedSchur] using
    cellSchur_eq_connected hD

/-- The actual connected cell-diagram Schur polynomial is irreducible over every field. -/
theorem irreducible_integralCellSchur {K : Type*} [Field K]
    {D : Diagram} (hD : IsConnectedSkew D) :
    Irreducible (map (Int.castRingHom K) (integralCellSchur D hD.1)) := by
  rw [integralCellSchur_eq_connected hD]
  exact irreducible_integralConnectedSchur D hD

namespace Profile
variable {n : ℕ}

/-- The rational profile function uses no generator above its top variable. -/
theorem schur_mem_atMost_top (P : Profile n) :
    P.schur ∈ supported ℚ {k : ℕ+ | k ≤ P.topVar} := by
  obtain ⟨R, hR, he⟩ := P.schur_corner_integralRemainder
  have hm : ∀ f : MvPolynomial ℕ+ ℤ,
      f ∈ supported ℤ {k : ℕ+ | k < P.topVar} →
        map (Int.castRingHom ℚ) f ∈ supported ℚ {k : ℕ+ | k ≤ P.topVar} := by
    intro f hf
    apply mem_supported.mpr
    intro k hk
    have hlt : k < P.topVar := (mem_supported.mp hf) (vars_map _ _ hk)
    exact hlt.le
  have hc := hm _ P.integralInterior_mem_below
  rw [map_integralCellSchur] at hc
  rw [he]
  apply Subalgebra.add_mem _ _ (hm R hR)
  apply Subalgebra.mul_mem _ _ hc
  apply Subalgebra.mul_mem
  · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
  · apply X_mem_supported.mpr
    exact (le_rfl : P.topVar ≤ P.topVar)

/-- The largest generator occurring in a profile function is its actual top index. -/
theorem polynomialSpan_schur (P : Profile n) :
    SkewCornerDescent.Matrix.polynomialSpan P.schur = (P.topVar : ℕ) := by
  have ht : P.topVar ∈ P.schur.vars := by
    by_contra h
    have hd := pderiv_eq_zero_of_notMem_vars h
    rw [P.pderiv_schur_top] at hd
    exact P.minor_ne_zero ((mul_eq_zero.mp hd).resolve_left (pow_ne_zero _ (by simp)))
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    exact (mem_supported.mp P.schur_mem_atMost_top hk)
  · exact Finset.le_sup (f := fun k : ℕ+ => (k : ℕ)) ht

end Profile

/-- The actual connected-diagram generator span is its geometric content span. -/
theorem polynomialSpan_cellSchur {D : Diagram} (hD : IsConnectedSkew D) :
    SkewCornerDescent.Matrix.polynomialSpan (cellSchur D hD.1) = span D := by
  obtain ⟨n, P, v, hp⟩ := hD.exists_profile_cells
  rw [cellSchur_eq_profile hD P v hp, P.polynomialSpan_schur, hp, span_translate,
    P.span_cells_eq_topVar]

/-- Integral remainder and nonzero interior coefficient at the actual geometric top generator. -/
theorem cellSchur_corner {D : Diagram} (hD : IsConnectedSkew D) :
    ∃ L : ℕ+, (L : ℕ) = span D ∧
      cellSchur (diagramInterior D) hD.1.interior ≠ 0 ∧
      ∃ R ∈ supported ℤ {k : ℕ+ | k < L},
        cellSchur D hD.1 = (-1) ^ ((D.image Prod.fst).card - 1) * X L *
          cellSchur (diagramInterior D) hD.1.interior + map (Int.castRingHom ℚ) R := by
  obtain ⟨n, P, v, hp⟩ := hD.exists_profile_cells
  have hrow : (D.image Prod.fst).card = n + 1 := by
    rw [hp, rowCount_translate, P.rowCount_cells]
  have hspan : span D = (P.topVar : ℕ) := by
    rw [hp, span_translate, P.span_cells_eq_topVar]
  have hc : cellSchur (diagramInterior D) hD.1.interior =
      cellSchur (diagramInterior P.cells) P.isSkew_cells.interior := by
    have he : diagramInterior D = translate v (diagramInterior P.cells) := by
      rw [hp, interior_translate]
    exact (cellSchur_congr he _ (isSkew_translate v P.isSkew_cells.interior)).trans
      (cellSchur_translate _ _ v)
  refine ⟨P.topVar, hspan.symm, ?_, ?_⟩
  · rw [hc, ← P.minorDet_eq_interiorSchur]
    exact P.minor_ne_zero
  · obtain ⟨R, hR, he⟩ := P.schur_corner_integralRemainder
    refine ⟨R, hR, ?_⟩
    rw [cellSchur_eq_profile hD P v hp, hrow, Nat.add_sub_cancel, hc]
    exact he

/-- Equal connected Schur functions have equal actual interior component products. -/
theorem interiorSchur_eq_of_cellSchur_eq {D E : Diagram}
    (hD : IsConnectedSkew D) (hE : IsConnectedSkew E)
    (he : cellSchur D hD.1 = cellSchur E hE.1) :
    cellSchur (diagramInterior D) hD.1.interior =
      cellSchur (diagramInterior E) hE.1.interior := by
  obtain ⟨n, P, v, hp⟩ := hD.exists_profile_cells
  obtain ⟨m, Q, w, hq⟩ := hE.exists_profile_cells
  have hfun : P.schur = Q.schur := by
    simpa only [cellSchur_eq_profile hD P v hp, cellSchur_eq_profile hE Q w hq] using he
  have hnm := (Profile.rows_eq_of_schur_eq hfun).1
  subst m
  have ht := Profile.topVar_eq_of_schur_eq hfun
  have hd := pderiv_cellSchur_eq_interiorSchur hD P v hp
  rw [he, ht, pderiv_cellSchur_eq_interiorSchur hE Q w hq] at hd
  exact mul_left_cancel₀ (pow_ne_zero n (by simp : (-1 : Lambda) ≠ 0)) hd.symm

end
end SkewGluing
