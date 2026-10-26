/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.ConnectedSchur
import SkewGluing.ProfileGeometry
import SkewGluing.SkewComponents
import SkewGluing.ComponentTranslation
import SkewGluing.Irreducibility

/-!
# Schur functions of skew cell diagrams

Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:jt`, `eq:corner-factors`, `lem:cofactor`).  A skew diagram's function is the
product of the profile functions of its actual connected components.  The skew-convexity argument
is required data, so no arbitrary value is supplied for a diagram outside that domain.

Sorry-free.
-/

namespace SkewGluing
attribute [local instance 10] Classical.propDecidable

/-- A connected diagram has itself as its only component.

TODO-COPIED: adapted from `skew-factor-gluing/lean/SkewGluing/CellSchur.lean`. -/
theorem edgeComponents_eq_singleton {D : Diagram} (hD : IsEdgeConnected D) :
    edgeComponents D = {D} := by
  ext C
  rw [Finset.mem_singleton, mem_edgeComponents]
  constructor
  · rintro ⟨x, hx, rfl⟩
    ext y
    rw [Finset.mem_filter]
    exact ⟨fun h => h.1, fun hy => ⟨hy, hD.2 x hx y hy⟩⟩
  · rintro rfl
    obtain ⟨x, hx⟩ := hD.1
    refine ⟨x, hx, ?_⟩
    ext y
    rw [Finset.mem_filter]
    exact ⟨fun hy => ⟨hy, hD.2 x hx y hy⟩, fun h => h.1⟩

/-- The function of a skew cell diagram, with the empty product equal to one. -/
noncomputable def cellSchur (D : Diagram) (hs : IsSkew D) : Lambda :=
  ∏ C ∈ (edgeComponents D).attach,
    connectedSchur C.1 (isConnectedSkew_component hs C.2)

/-- Cell Schur functions respect equality of diagrams independently of their skew witnesses. -/
@[congr]
theorem cellSchur_congr {D D' : Diagram} (h : D = D') (hs : IsSkew D) (hs' : IsSkew D') :
    cellSchur D hs = cellSchur D' hs' := by
  cases h
  rfl

/-- On a connected skew diagram the component product is its Jacobi--Trudi function. -/
theorem cellSchur_eq_connected {D : Diagram} (hD : IsConnectedSkew D) :
    cellSchur D hD.1 = connectedSchur D hD := by
  have hm : D ∈ edgeComponents D := by rw [edgeComponents_eq_singleton hD.2]; simp
  unfold cellSchur
  rw [Finset.prod_eq_single ⟨D, hm⟩]
  · intro C hC hne
    have hc : C.1 = D := by
      have := C.2
      simpa only [edgeComponents_eq_singleton hD.2, Finset.mem_singleton] using this
    exact False.elim (hne (Subtype.ext hc))
  · simp

/-- The empty skew diagram has Schur function one. -/
theorem cellSchur_empty (hs : IsSkew (∅ : Diagram)) : cellSchur ∅ hs = 1 := by
  simp [cellSchur, edgeComponents]

/-- Every profile presentation computes the full cell-diagram function. -/
theorem cellSchur_eq_profile {D : Diagram} (hD : IsConnectedSkew D) {n : ℕ}
    (P : Profile n) (v : ℤ × ℤ) (h : D = translate v P.cells) :
    cellSchur D hD.1 = P.schur := by
  rw [cellSchur_eq_connected hD, connectedSchur_eq_profile hD P v h]

/-- Realizing a profile as cells and taking its function recovers its determinant. -/
theorem cellSchur_cells {n : ℕ} (P : Profile n) :
    cellSchur P.cells P.isSkew_cells = P.schur :=
  cellSchur_eq_profile P.isConnectedSkew_cells P 0 (translate_zero.symm)

/-- Connected skew cell diagrams have irreducible functions over the rational field. -/
theorem irreducible_cellSchur {D : Diagram} (hD : IsConnectedSkew D) :
    Irreducible (cellSchur D hD.1) := by
  rw [cellSchur_eq_connected hD]
  exact irreducible_schur (diagramProfile D hD).1 (diagramProfile D hD).2

/-- Translating a skew diagram leaves its full component-product function unchanged. -/
theorem cellSchur_translate (D : Diagram) (hs : IsSkew D) (v : ℤ × ℤ) :
    cellSchur (translate v D) (isSkew_translate v hs) = cellSchur D hs := by
  symm
  unfold cellSchur
  let f : {C // C ∈ edgeComponents D} → {C // C ∈ edgeComponents (translate v D)} :=
    fun C => ⟨translate v C.1, by
      rw [edgeComponents_translate]
      exact Finset.mem_image_of_mem (translate v) C.2⟩
  apply Finset.prod_bij (fun C _ => f C)
  · intro C hC
    exact Finset.mem_attach _ _
  · intro C hC C' hC' he
    exact Subtype.ext (translate_injective v (congrArg Subtype.val he))
  · intro C hC
    have hm := C.2
    have hm' : C.1 ∈ (edgeComponents D).image (translate v) := by
      simpa only [edgeComponents_translate] using hm
    obtain ⟨B, hB, he⟩ := Finset.mem_image.mp hm'
    exact ⟨⟨B, hB⟩, Finset.mem_attach _ _, Subtype.ext he⟩
  · intro C hC
    exact (connectedSchur_translate C.1 (isConnectedSkew_component hs C.2) v).symm

end SkewGluing
