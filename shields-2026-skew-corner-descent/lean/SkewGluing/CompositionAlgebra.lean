/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.ShapeAlgebra

/-!
# Modified composition as an algebra homomorphism

Supports `shields-2026-skew-corner-descent.tex`, «Corner transport» (`eq:homomorphism`).
The ordinary and mixed-c geometric modified compositions descend to actual algebra maps.
Their compatibility equations and Schur-kernel containment are proved by the copied substrate,
not supplied as hypotheses of the resulting existence theorems.

Sorry-free.
-/

namespace GluingCore.Plan

attribute [local instance 10] Classical.propDecidable

/-- Ordinary geometric modified composition is an algebra map on every skew Schur function. -/
theorem exists_ordinaryComposition_algHom {ω : MarkedInner} (hω : ω.IsLegal)
    (hc : ω.case = .a ∨ ω.case = .b) :
    ∃ φ : Lambda →ₐ[ℚ] Lambda, ∀ D : Diagram, IsSkew D → φ (cellSchur D) = modComp ω D := by
  have he : EdgeCompat ω := by
    rcases hc with ha | hb
    · exact edgeCompat_a hω ha
    · exact edgeCompat_b hω hb
  refine exists_shape_algHom (modComp ω) ?_ (modComp_translate ω) ?_
    (edge_kernel hω hc he)
  · simp [modComp, edgeComponents]
  · intro A B _ _ hd hn
    exact modComp_union hd hn

/-- Mixed-c geometric modified composition, including its sign, is an algebra map. -/
theorem exists_cornerComposition_algHom {ω : MarkedInner} (hω : ω.IsLegal)
    (hc : ω.case = .c) :
    ∃ φ : Lambda →ₐ[ℚ] Lambda, ∀ D : Diagram, IsSkew D → φ (cellSchur D) = modCompC ω D := by
  refine exists_shape_algHom (modCompC ω) ?_ (modCompC_translate ω) ?_
    (corner_kernel (cornerCompat_c hω hc) (modCompC_translate ω))
  · simp [modCompC, edgeComponents]
  · intro A B _ _ hd hn
    exact Corner.modCompC_union hd hn

/-- A horizontal shape has no northbound supplemental cells, before or after rotation. -/
theorem northbound_eq_zero_of_flatRows (ω : MarkedInner) {D : Diagram} {a : ℤ}
    (hflat : ∀ x ∈ D, x.1 = a) : northbound ω D = 0 := by
  unfold northbound
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx, hn⟩ := Finset.mem_filter.mp hx
  have h1 := hflat x hx
  have h2 := hflat (x.1 - 1, x.2) hn.1
  simp only at h2
  omega

/-- Every legal attachment case yields the geometric component formula, with its actual sign. -/
theorem exists_legalComposition_algHom {ω : MarkedInner} (hω : ω.IsLegal) :
    ∃ φ : Lambda →ₐ[ℚ] Lambda,
      (∀ D : Diagram, IsConnectedSkew D →
        ∃ sign : ℕ, φ (cellSchur D) = (-1 : Lambda) ^ sign * componentT ω D) ∧
      (∀ D : Diagram, IsConnectedSkew D → ∀ a : ℤ, (∀ x ∈ D, x.1 = a) →
        φ (cellSchur D) = componentT ω D) := by
  cases hc : ω.case with
  | a =>
    obtain ⟨φ, hφ⟩ := exists_ordinaryComposition_algHom hω (Or.inl hc)
    refine ⟨φ, ?_, ?_⟩
    · intro D hD
      refine ⟨0, ?_⟩
      simpa [modComp_connected hD] using hφ D hD.1
    · intro D hD _ _
      simpa [modComp_connected hD] using hφ D hD.1
  | b =>
    obtain ⟨φ, hφ⟩ := exists_ordinaryComposition_algHom hω (Or.inr hc)
    refine ⟨φ, ?_, ?_⟩
    · intro D hD
      refine ⟨0, ?_⟩
      simpa [modComp_connected hD] using hφ D hD.1
    · intro D hD _ _
      simpa [modComp_connected hD] using hφ D hD.1
  | c =>
    obtain ⟨φ, hφ⟩ := exists_cornerComposition_algHom hω hc
    refine ⟨φ, ?_, ?_⟩
    · intro D hD
      refine ⟨northbound ω D, ?_⟩
      simpa [modCompC_connected hD, componentTc] using hφ D hD.1
    · intro D hD a hflat
      have hz := northbound_eq_zero_of_flatRows ω hflat
      simpa [modCompC_connected hD, componentTc, hz] using hφ D hD.1
  | d =>
    have hrc : ω.rotate.case = .c := by
      change ω.case.rotate = .c
      rw [hc]
      rfl
    obtain ⟨φ, hφ⟩ := exists_cornerComposition_algHom
      (GluingCore.MarkedInner.isLegal_rotate hω) hrc
    refine ⟨φ, ?_, ?_⟩
    · intro D hD
      refine ⟨northbound ω.rotate (GluingCore.rotate D), ?_⟩
      have hrD := isConnectedSkew_rotate hD
      have hh := hφ (GluingCore.rotate D) hrD.1
      rw [cellSchur_rotate, modCompC_connected hrD, componentTc,
        MarkedInner.componentT_rotate hω.1 hω.2.2.1 hD.2.1] at hh
      exact hh
    · intro D hD a hflat
      have hrD := isConnectedSkew_rotate hD
      have hflat' : ∀ x ∈ GluingCore.rotate D, x.1 = -a := by
        intro x hx
        have hh := hflat (-x) (mem_rotate.mp hx)
        simp only [Prod.fst_neg] at hh
        omega
      have hz := northbound_eq_zero_of_flatRows ω.rotate hflat'
      have hh := hφ (GluingCore.rotate D) hrD.1
      rw [cellSchur_rotate, modCompC_connected hrD, componentTc, hz,
        pow_zero, one_mul, MarkedInner.componentT_rotate hω.1 hω.2.2.1 hD.2.1] at hh
      exact hh

end GluingCore.Plan
