/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/FWords.lean
import SkewMarkedFactor.Gluing.Coding

/-!
# Two further bits of the northwest word of a case-(d) composite

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-caps`) as used in thesis Lemma 5.5.7 (`OlsonHarris2024HopfApplications`).

The merged coding module reads the class steps of the first rows of a case-(d) composite at the
switches `t`, `s` and at the first and last block.  Two more values are needed for the corner
case, where the northwest word of the case-(d) composite is the southeast word of the case-(c)
composite read backwards: at the residue `w` of the last block but one, `0` when `s < w`, and at
the residue `0` of the terminal block, `1` when `1 ≤ t`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The first-row class step at the residue `w` of the block `M` of a case-(d) composite is zero
when `s < w`. -/
theorem mix_classBitLo_w (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (hs : s < ω.widthZ) :
    classBitLo ω.period (ω.mixLo D) (maxContent D) ω.widthZ = 0 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D) ω.widthZ :=
    Or.inl ⟨hmM, le_rfl⟩
  have he := D_end_singleton hD (x := maxContent D) (Or.inr rfl)
  unfold classBitLo
  have hv1 := validClass_pred hv
  simp only [show ω.widthZ ≠ 0 by omega, ite_false]
  rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (by omega) hv]
  have F := mix_lo_data h hc hph (a := ω.widthZ) (by omega) le_rfl
  unfold mixGLo profM profS
  split_ifs <;> omega

/-- The first-row class step at the residue `0` of the terminal block of a case-(d) composite is
one when `1 ≤ t`. -/
theorem mix_classBitLo_zero (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (ht : 1 ≤ t) :
    classBitLo ω.period (ω.mixLo D) (maxContent D + 1) 0 = 1 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hlt := h.phases_lt (Or.inr hc) hph
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (maxContent D + 1) 0 :=
    Or.inr ⟨rfl, by omega⟩
  have he := D_end_singleton hD (x := maxContent D) (Or.inr rfl)
  have hp : (maxContent D + 1) * ω.rowShift = maxContent D * ω.rowShift + ω.rowShift := by ring
  unfold classBitLo
  have hv1 := validClass_prev (ω.period - 1) hv (by omega)
  simp only [ite_true]
  rw [mixLo_formula h hD hc hph (by omega) hv1, mixLo_formula h hD hc hph (le_refl _) hv]
  have hcp := (d_caps h hc).2
  have f0 := d_E_facts h hc hph (a := 0) (le_refl _) (by omega)
  have hW0 := h.diagLo_W (a := 0) (le_refl _) (by omega)
  simp only [dLo, dHi, zero_add, add_zero] at hcp f0 hW0
  unfold mixGLo profM profS
  simp only [add_sub_cancel_right, hp, add_zero]
  split_ifs <;> omega

end MarkedInner

end SkewMarkedFactor.Gluing
