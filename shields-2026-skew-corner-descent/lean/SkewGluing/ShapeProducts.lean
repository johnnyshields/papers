/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import GluingCore.CellSchurTableau
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Separated products of actual skew shapes

Supports `shields-2026-skew-corner-descent.tex`, «Corner transport» (`eq:homomorphism`).
Every product of skew Schur functions has a separated geometric representative.  Consequently,
the linear Schur map on skew-supported shape combinations is surjective.

Sorry-free.
-/

namespace GluingCore

attribute [local instance 10] Classical.propDecidable

/-- Two skew shapes can be placed northeast/southwest without adding cross-order intervals. -/
theorem exists_separated_skew_union (A B : Diagram) (hA : IsSkew A) (hB : IsSkew B) :
    ∃ v : ℤ × ℤ, IsSkew (A ∪ translate v B) ∧ Disjoint A (translate v B) ∧
      (∀ a ∈ A, ∀ b ∈ translate v B, ¬ CellAdj a b) := by
  let SA : ℤ := ∑ x ∈ A, (|x.1| + |x.2|)
  let SB : ℤ := ∑ x ∈ B, (|x.1| + |x.2|)
  let K : ℤ := SA + SB + 2
  have hSA : 0 ≤ SA := Finset.sum_nonneg fun x _ => by positivity
  have hSB : 0 ≤ SB := Finset.sum_nonneg fun x _ => by positivity
  have boundA : ∀ x ∈ A, |x.1| + |x.2| ≤ SA := fun x hx =>
    Finset.single_le_sum (f := fun y : ℤ × ℤ => |y.1| + |y.2|)
      (fun y _ => by positivity) hx
  have boundB : ∀ x ∈ B, |x.1| + |x.2| ≤ SB := fun x hx =>
    Finset.single_le_sum (f := fun y : ℤ × ℤ => |y.1| + |y.2|)
      (fun y _ => by positivity) hx
  have sep : ∀ x ∈ A, ∀ y ∈ translate (K, -K) B,
      x.1 + 1 < y.1 ∧ y.2 + 1 < x.2 := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have ha := boundA x hx
    have hb := boundB z hz
    have a1 := le_abs_self x.1
    have a2 := neg_abs_le x.2
    have b1 := neg_abs_le z.1
    have b2 := le_abs_self z.2
    have ax1 := abs_nonneg x.1
    have ax2 := abs_nonneg x.2
    have bz1 := abs_nonneg z.1
    have bz2 := abs_nonneg z.2
    change x.1 + 1 < z.1 + K ∧ z.2 + -K + 1 < x.2
    dsimp [K]
    omega
  refine ⟨(K, -K), ?_, ?_, ?_⟩
  · intro x hx y hy hxy1 hxy2 i hi j hj
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.mem_union_left _ (hA x hx y hy hxy1 hxy2 i hi j hj)
    · have := sep x hx y hy
      omega
    · have := sep y hy x hx
      omega
    · exact Finset.mem_union_right _
        (isSkew_translate (K, -K) hB x hx y hy hxy1 hxy2 i hi j hj)
  · rw [Finset.disjoint_left]
    intro x hx hy
    have := sep x hx x hy
    omega
  · intro x hx y hy hadj
    have hs := (sep x hx y hy).1
    have hab := neg_abs_le (x.1 - y.1)
    have hnon := abs_nonneg (x.2 - y.2)
    unfold CellAdj at hadj
    omega

/-- Every complete homogeneous generator is the Schur function of a genuine one-row shape. -/
theorem exists_skew_generator (j : ℕ+) : ∃ D : Diagram, IsSkew D ∧ cellSchur D = MvPolynomial.X j := by
  let P : Profile 0 := {
    r := fun _ => j
    g := Fin.elim0
    r_pos := fun _ => j.pos
    g_lt_castSucc := fun i => Fin.elim0 i
    g_lt_succ := fun i => Fin.elim0 i }
  refine ⟨P.cells, P.isConnectedSkew_cells.1, ?_⟩
  rw [cellSchur_cells]
  unfold Profile.schur
  rw [Matrix.det_fin_one]
  change hh (P.xi 0 - P.zeta 0) = _
  have hx : P.xi 0 - P.zeta 0 = (j : ℤ) := by simp [Profile.xi, P]
  rw [hx, hh_pnat]

/-- Skew Schur functions linearly span the polynomial algebra of complete generators. -/
theorem skewSchur_span_eq_top :
    Submodule.span ℚ {f : Lambda | ∃ D : Diagram, IsSkew D ∧ f = cellSchur D} = ⊤ := by
  let S := Submodule.span ℚ {f : Lambda | ∃ D : Diagram, IsSkew D ∧ f = cellSchur D}
  have shape_mem (D : Diagram) (hD : IsSkew D) : cellSchur D ∈ S :=
    Submodule.subset_span ⟨D, hD, rfl⟩
  have h1 : (1 : Lambda) ∈ S := by
    have hh := shape_mem ∅ (by simp [IsSkew])
    simpa [cellSchur, edgeComponents] using hh
  have hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S := by
    intro f hf g hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨A, hA, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨B, hB, rfl⟩ := hg
        obtain ⟨v, hs, hd, hn⟩ := exists_separated_skew_union A B hA hB
        have hh := shape_mem (A ∪ translate v B) hs
        rwa [cellSchur_union hd hn, cellSchur_translate] at hh
      | zero => simp
      | add g h _ _ hg hh => simpa [mul_add] using add_mem hg hh
      | smul a g _ hg => simpa [mul_smul_comm] using Submodule.smul_mem S a hg
    | zero => simp
    | add f h _ _ hf hh => simpa [add_mul] using add_mem hf hh
    | smul a f _ hf => simpa [smul_mul_assoc] using Submodule.smul_mem S a hf
  apply top_unique
  intro f hTop
  clear hTop
  change f ∈ S
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.C_eq_smul_one]
    exact Submodule.smul_mem S a h1
  | add f g hf hg => exact add_mem hf hg
  | mul_X f j hf =>
    obtain ⟨D, hD, hj⟩ := exists_skew_generator j
    exact hmul f hf _ (hj ▸ shape_mem D hD)

end GluingCore
