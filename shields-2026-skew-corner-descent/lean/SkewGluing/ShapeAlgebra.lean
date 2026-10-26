/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.ShapeProducts
import GluingCore.OlsonHarris.Plan.Assemble

/-!
# Algebra maps induced by geometric shape functions

Supports `shields-2026-skew-corner-descent.tex`, «Corner transport» (`eq:homomorphism`).
A translation-invariant function multiplicative on separated diagrams descends to an algebra map
when its linear extension kills the Schur relations.  The kernel theorem and geometric product
representatives supply the descent; no modified-composition identity is assumed here.

Sorry-free.
-/

namespace GluingCore.Plan

attribute [local instance 10] Classical.propDecidable

/-- The Schur map restricted to genuine skew-supported shape combinations. -/
noncomputable def skewSchurMap : skewSpace →ₗ[ℚ] Lambda := shapeSchur.domRestrict skewSpace

/-- A skew shape is in the domain of the restricted Schur map. -/
noncomputable def skewShape (D : Diagram) (hD : IsSkew D) : skewSpace :=
  ⟨shape D, shape_mem_skewSpace hD⟩

@[simp]
theorem skewSchurMap_shape (D : Diagram) (hD : IsSkew D) :
    skewSchurMap (skewShape D hD) = cellSchur D :=
  KernelAux.shapeSchur_shape D

/-- Complete generators and separated products make the restricted Schur map surjective. -/
theorem skewSchurMap_surjective : Function.Surjective skewSchurMap := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← skewSchur_span_eq_top]
  apply Submodule.span_le.mpr
  rintro f ⟨D, hD, rfl⟩
  exact ⟨skewShape D hD, skewSchurMap_shape D hD⟩

/-- A shape function killing the geometric relations factors through the restricted Schur map. -/
theorem exists_shape_linearMap (F : Diagram → Lambda)
    (hker : shapeKernelSpan ≤ LinearMap.ker (Flin F)) :
    ∃ l : Lambda →ₗ[ℚ] Lambda, ∀ D : Diagram, IsSkew D → l (cellSchur D) = F D := by
  let T : skewSpace →ₗ[ℚ] Lambda := (Flin F).domRestrict skewSpace
  have hk : LinearMap.ker skewSchurMap ≤ LinearMap.ker T := by
    intro h hh
    have hz : shapeSchur h.1 = 0 := hh
    have hr := kernel_schur (mem_skewSpace.mp h.2) hz
    exact hker hr
  let l : Lambda →ₗ[ℚ] Lambda :=
    ((LinearMap.ker skewSchurMap).liftQ T hk).comp
      (skewSchurMap.quotKerEquivOfSurjective skewSchurMap_surjective).symm.toLinearMap
  refine ⟨l, ?_⟩
  intro D hD
  rw [← skewSchurMap_shape D hD]
  dsimp [l]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact Flin_shape F D

/-- The geometric multiplicativity is preserved by the linear descent, on every polynomial. -/
theorem shape_linearMap_mul (F : Diagram → Lambda) (l : Lambda →ₗ[ℚ] Lambda)
    (hl : ∀ D : Diagram, IsSkew D → l (cellSchur D) = F D)
    (ht : ∀ v D, F (translate v D) = F D)
    (hu : ∀ A B : Diagram, IsSkew A → IsSkew B → Disjoint A B →
      (∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) → F (A ∪ B) = F A * F B)
    (f g : Lambda) : l (f * g) = l f * l g := by
  have hf : f ∈ Submodule.span ℚ {f : Lambda | ∃ D : Diagram, IsSkew D ∧ f = cellSchur D} := by
    rw [skewSchur_span_eq_top]
    trivial
  have hg : g ∈ Submodule.span ℚ {f : Lambda | ∃ D : Diagram, IsSkew D ∧ f = cellSchur D} := by
    rw [skewSchur_span_eq_top]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, hA, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨B, hB, rfl⟩ := hg
      obtain ⟨v, hs, hd, hn⟩ := exists_separated_skew_union A B hA hB
      rw [← cellSchur_translate v B, ← cellSchur_union hd hn,
        hl _ hs, hu A _ hA (isSkew_translate v hB) hd hn, ht v B]
      rw [cellSchur_translate, hl A hA, hl B hB]
    | zero => simp
    | add g h _ _ hg hh => simp only [mul_add, map_add, hg, hh]
    | smul a g _ hg => simp only [mul_smul_comm, map_smul, hg]
  | zero => simp
  | add f h _ _ hf hh => simp only [add_mul, map_add, hf, hh]
  | smul a f _ hf => simp only [smul_mul_assoc, map_smul, hf]

/-- A geometric shape function satisfying the Schur relations is an actual algebra map. -/
theorem exists_shape_algHom (F : Diagram → Lambda) (h0 : F ∅ = 1)
    (ht : ∀ v D, F (translate v D) = F D)
    (hu : ∀ A B : Diagram, IsSkew A → IsSkew B → Disjoint A B →
      (∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) → F (A ∪ B) = F A * F B)
    (hker : shapeKernelSpan ≤ LinearMap.ker (Flin F)) :
    ∃ φ : Lambda →ₐ[ℚ] Lambda, ∀ D : Diagram, IsSkew D → φ (cellSchur D) = F D := by
  obtain ⟨l, hl⟩ := exists_shape_linearMap F hker
  have h1 : l 1 = 1 := by
    have hh := hl ∅ (by simp [IsSkew])
    simpa [cellSchur, edgeComponents, h0] using hh
  let φ : Lambda →ₐ[ℚ] Lambda := {
    toFun := l
    map_one' := h1
    map_mul' := shape_linearMap_mul F l hl ht hu
    map_zero' := l.map_zero
    map_add' := l.map_add
    commutes' := fun a => by
      change l (MvPolynomial.C a) = MvPolynomial.C a
      rw [MvPolynomial.C_eq_smul_one, map_smul, h1] }
  exact ⟨φ, hl⟩

end GluingCore.Plan
