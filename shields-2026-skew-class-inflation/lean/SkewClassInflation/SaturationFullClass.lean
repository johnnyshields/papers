/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationPositionalInverse
import SkewClassInflation.SaturationTotalCore
import SkewClassInflation.DistinguishedContractionRotation
import SkewClassInflation.SaturationLocalizedInjectivity

/-!
# Full unrestricted repeated-block source classes

The class formula of `thm:repeated-block-saturation` and the geometric
inverse of `lem:total-contraction-inverse` in
`shields-2026-skew-class-inflation.tex`.  Actual factor products, total
core rigidity, and positional splitting are all supplied from the original
full-board Schur equality.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewJacobiNegative.Staircase

variable (A : SaturationInner)

/-- Every arbitrary connected mate is an actual source-family member or its global rotation. -/
theorem arbitrary_mate_geometry {M n : ℕ} (α : Composition M) (hM : 2 ≤ M) (Q : Profile n)
    (he : Q.toBetaDiagram.schur = (A.diagram α (by omega)).2.toBetaDiagram.schur) :
    ∃ β : Composition M, (⟨n, Q⟩ : ConnectedProfile) = A.diagram β (by omega) ∨
      (⟨n, Q⟩ : ConnectedProfile) = ConnectedProfile.rotate (A.diagram β (by omega)) := by
  have hdata := A.source_mate_reduction α (by omega) Q he
  have hQ : Thick Q := hdata.2.1
  have hrQ : ∀ i, A.d < Q.r i := hdata.2.2.1
  let fs := A.powerFunctions α.blocks (fun _ h => α.blocks_pos h)
  have hfs : ∀ p ∈ fs, A.IsPowerFunction p := A.powerFunctions_are_actual _ _
  have hconst : eraseGenerator A.largeLabel Q.toBetaDiagram.schur = fs.prod := by
    rw [he]
    exact A.diagram_constant_coefficient α (by omega)
  rcases A.arbitrary_mate_total_core_rigidity α hM Q he with hcore | hcore
  · obtain ⟨β, hβ⟩ := A.oriented_profile_reconstruction (by omega) Q hQ hrQ fs hfs hconst hcore
    exact ⟨β, Or.inl hβ⟩
  · have hrotCore : (contractAllMinimum Q.rotate A.largeLabel : ConnectedProfile) =
        ⟨M * A.k, A.power M (by omega)⟩ := by
      rw [contractAllMinimum_rotate Q A.largeLabel hQ hrQ, hcore,
        ConnectedProfile.rotate_rotate]
    have hrotSchur : Q.rotate.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
      simpa only [Gluing.Profile.toBetaDiagram_schur] using Q.schur_rotate
    have hrotConst : eraseGenerator A.largeLabel Q.rotate.toBetaDiagram.schur = fs.prod := by
      rw [hrotSchur]
      exact hconst
    obtain ⟨β, hβ⟩ := A.oriented_profile_reconstruction (by omega) Q.rotate
      (profile_rotate_thick Q hQ) (fun i => hrQ i.rev) fs hfs hrotConst hrotCore
    have hβ' : ConnectedProfile.rotate (⟨n, Q⟩ : ConnectedProfile) = A.diagram β (by omega) := hβ
    have hh := congrArg ConnectedProfile.rotate hβ'
    rw [ConnectedProfile.rotate_rotate] at hh
    exact ⟨β, Or.inr hh⟩

/-- The full connected Schur class is exactly the two actual outer-ribbon parameter images. -/
theorem full_class {M : ℕ} (α : Composition M) (hM : 2 ≤ M) :
    ConnectedProfile.schurClass (A.diagram α (by omega)) =
      (fun β : Composition M => A.diagram β (by omega)) '' ribbonClass α ∪
        (fun β : Composition M => ConnectedProfile.rotate (A.diagram β (by omega))) ''
          ribbonClass α := by
  ext H
  constructor
  · intro hH
    obtain ⟨n, Q⟩ := H
    have he : Q.toBetaDiagram.schur = (A.diagram α (by omega)).2.toBetaDiagram.schur := by
      change profileSchur Q = profileSchur (A.diagram α (by omega)).2 at hH
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hH
    obtain ⟨β, hβ | hβ⟩ := A.arbitrary_mate_geometry α hM Q he
    · apply Set.mem_union_left
      refine ⟨β, ?_, hβ.symm⟩
      apply (A.diagram_schur_eq_iff_ribbon β α (by omega)).mp
      exact (congrArg (fun D : ConnectedProfile => D.2.toBetaDiagram.schur) hβ).symm.trans he
    · apply Set.mem_union_right
      refine ⟨β, ?_, hβ.symm⟩
      apply (A.diagram_schur_eq_iff_ribbon β α (by omega)).mp
      have hh : ConnectedProfile.schur (A.diagram β (by omega)) =
          ConnectedProfile.schur (A.diagram α (by omega)) := by
        rw [← ConnectedProfile.schur_rotate (A.diagram β (by omega)), ← hβ]
        exact hH
      simpa only [ConnectedProfile.schur, profileSchur_eq_inherited,
        Gluing.Profile.toBetaDiagram_schur] using hh
  · rintro (⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩)
    · have he := (A.diagram_schur_eq_iff_ribbon β α (by omega)).mpr hβ
      change profileSchur (A.diagram β (by omega)).2 = profileSchur (A.diagram α (by omega)).2
      simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using he
    · change ConnectedProfile.schur (ConnectedProfile.rotate (A.diagram β (by omega))) =
        ConnectedProfile.schur (A.diagram α (by omega))
      rw [ConnectedProfile.schur_rotate]
      have he := (A.diagram_schur_eq_iff_ribbon β α (by omega)).mpr hβ
      simpa only [ConnectedProfile.schur, profileSchur_eq_inherited,
        Gluing.Profile.toBetaDiagram_schur] using he

/-- The unrestricted inverse recovers an actual outer-ribbon mate with the same part multiset. -/
theorem total_contraction_inverse {M n : ℕ} (α : Composition M) (hM : 2 ≤ M) (Q : Profile n)
    (he : Q.toBetaDiagram.schur = (A.diagram α (by omega)).2.toBetaDiagram.schur) :
    ∃ β : Composition M, β ∈ ribbonClass α ∧ β.blocks.Perm α.blocks ∧
      ((⟨n, Q⟩ : ConnectedProfile) = A.diagram β (by omega) ∨
        (⟨n, Q⟩ : ConnectedProfile) = ConnectedProfile.rotate (A.diagram β (by omega))) := by
  have hclass : (⟨n, Q⟩ : ConnectedProfile) ∈
      ConnectedProfile.schurClass (A.diagram α (by omega)) := by
    change profileSchur Q = profileSchur (A.diagram α (by omega)).2
    simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using he
  rw [A.full_class α hM] at hclass
  rcases hclass with ⟨β, hβ, hEq⟩ | ⟨β, hβ, hEq⟩
  · exact ⟨β, hβ, ribbon_eq_blocks_perm β α (by omega) (by omega) hβ, Or.inl hEq.symm⟩
  · exact ⟨β, hβ, ribbon_eq_blocks_perm β α (by omega) (by omega) hβ, Or.inr hEq.symm⟩

/-- All-one outer words have complete rotation-only classes for every general inner. -/
theorem full_class_ones (M : ℕ) (hM : 2 ≤ M) :
    ConnectedProfile.schurClass (A.diagram (Composition.ones M) (by omega)) =
      {A.diagram (Composition.ones M) (by omega),
        ConnectedProfile.rotate (A.diagram (Composition.ones M) (by omega))} := by
  rw [A.full_class (Composition.ones M) hM, ribbonClass_ones M (by omega)]
  simp only [Set.image_singleton, Set.union_singleton]
  exact Set.pair_comm _ _

end SkewClassInflation.SaturationInner
