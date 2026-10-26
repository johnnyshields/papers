/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.UniversalOmegaCells

/-!
# Universal omega on full skew component products

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Transposition preserves the complete actual component inventory, and universal
omega transports its entire Schur product, including empty diagrams. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- Every actual component transposes to exactly one actual component. -/
theorem edgeComponents_transpose (D : Diagram) :
    edgeComponents (transpose D) = (edgeComponents D).image transpose := by
  apply edgeComponents_image (Equiv.prodComm ℤ ℤ)
  intro a b
  simp only [Equiv.prodComm_apply, cellAdj_iff, Prod.fst_swap, Prod.snd_swap]
  omega

/-- Universal omega transports the entire skew Schur product, retaining all
components and their multiplicities as well as the empty product. -/
theorem schurInvolution_skew_cellSchur (D : Diagram) (hs : IsSkew D) :
    schurInvolution (cellSchur D hs) =
      cellSchur (transpose D) (isSkew_transpose hs) := by
  classical
  unfold cellSchur
  rw [map_prod]
  let f : {C // C ∈ edgeComponents D} → {C // C ∈ edgeComponents (transpose D)} :=
    fun C => ⟨transpose C.1, by
      rw [edgeComponents_transpose]
      exact Finset.mem_image_of_mem transpose C.2⟩
  apply Finset.prod_bij (fun C _ => f C)
  · intro C _
    exact Finset.mem_attach _ _
  · intro C _ C' _ he
    have ht := congrArg Subtype.val he
    change transpose C.1 = transpose C'.1 at ht
    have h := congrArg transpose ht
    simp only [transpose_transpose] at h
    exact Subtype.ext h
  · intro C _
    have hm : C.1 ∈ (edgeComponents D).image transpose := by
      simpa only [edgeComponents_transpose] using C.2
    obtain ⟨B, hB, he⟩ := Finset.mem_image.mp hm
    exact ⟨⟨B, hB⟩, Finset.mem_attach _ _, Subtype.ext he⟩
  · intro C _
    have hc := isConnectedSkew_component hs C.2
    have h := schurInvolution_cellSchur hc
    rw [cellSchur_eq_connected hc,
      cellSchur_eq_connected (isConnectedSkew_transpose hc)] at h
    exact h

end SkewCornerDescent
