/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProtectedComponentProfiles
import SkewCornerDescent.Matrix.UnitVertexGeometry
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Protected unit-component profile tops with all earlier blocks retained

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). The
full upper-block inverse introduces the complete earlier-block coupling, but
its contribution is strictly below the current block's least-column top.
No earlier effective incoming vector is frozen. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- The complete tail incoming row after an arbitrary upper-block prefix. -/
theorem upper_block_incoming_tail {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (A : Matrix ν ν F) (U : Matrix ν μ F) (B : Matrix μ μ F)
    (r : Matrix Unit ν F) (s : Matrix Unit μ F)
    [Invertible A] [Invertible B] [Invertible (Matrix.fromBlocks A U 0 B)] (j : μ) :
    (Matrix.fromCols r s * ⅟(Matrix.fromBlocks A U 0 B)) () (.inr j) =
      (s * ⅟B) () j - (r * ⅟A * U * ⅟B) () j := by
  rw [Matrix.invOf_fromBlocks_zero₂₁_eq, Matrix.fromCols_mul_fromBlocks]
  simp only [Matrix.fromCols, Matrix.of_apply, Sum.elim_inr, Matrix.add_apply,
    Matrix.mul_neg, Matrix.neg_apply, Matrix.mul_assoc]
  ring

/-- The complete head outgoing column before an arbitrary upper-block suffix. -/
theorem upper_block_outgoing_head {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (A : Matrix ν ν F) (U : Matrix ν μ F) (B : Matrix μ μ F)
    (r : Matrix ν Unit F) (s : Matrix μ Unit F)
    [Invertible A] [Invertible B] [Invertible (Matrix.fromBlocks A U 0 B)] (i : ν) :
    (⅟(Matrix.fromBlocks A U 0 B) * Matrix.fromRows r s) (.inl i) () =
      (⅟A * r) i () - (⅟A * U * ⅟B * s) i () := by
  rw [Matrix.invOf_fromBlocks_zero₂₁_eq, Matrix.fromBlocks_mul_fromRows]
  change (⅟A * r + -(⅟A * U * ⅟B) * s) i () = _
  simp only [Matrix.neg_mul, Matrix.add_apply, Matrix.neg_apply, sub_eq_add_neg]

private theorem matrix_product_mem_subfield {F ι κ ζ : Type*} [Field F] [Fintype κ]
    (S : Subfield F) (A : Matrix ι κ F) (B : Matrix κ ζ F)
    (hA : ∀ i k, A i k ∈ S) (hB : ∀ k j, B k j ∈ S) (i j) :
    (A * B) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The current unit block's complete incoming coefficients keep their protected
least-column top after every original earlier-block coupling. Its nonzero top
coefficient and the lower remainder are produced, not assumed. -/
theorem ordered_component_incoming_protected_coefficient {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top)
    (row col : ν → ℤ) (τ : ℤ) (J : ℕ+) (hJ : c.top < J)
    (hrow : ∀ i, row i < (J : ℤ) + τ) (hcol : ∀ i, τ < col i)
    [Invertible (vertexBetaMatrix c.residueMap row col)] (j : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    let A := vertexBetaMatrix c.residueMap row col
    let B := (jtMatrix P.xi P.zeta).map c.residueMap
    let U := Matrix.of fun i k => c.residueMap (hh (row i - (P.zeta k + τ)))
    let r := vertexOutgoing c.residueMap col ((J : ℤ) + τ)
    let s := Matrix.of fun (_ : Unit) k => c.residueMap (hh ((J : ℤ) - P.zeta k))
    letI := Matrix.fromBlocksZero₂₁Invertible A U B
    ⅟B (Fin.last n) j ≠ 0 ∧ ⅟B (Fin.last n) j ∈ residueLowerField c.top J ∧
      ∃ R ∈ residueLowerField c.top J,
        (Matrix.fromCols r s * ⅟(Matrix.fromBlocks A U 0 B)) () (.inr j) =
          residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * ⅟B (Fin.last n) j + R := by
  classical
  let := c.profileResidueInverse P hne
  let A := vertexBetaMatrix c.residueMap row col
  let B := (jtMatrix P.xi P.zeta).map c.residueMap
  let U := Matrix.of fun i k => c.residueMap (hh (row i - (P.zeta k + τ)))
  let r := vertexOutgoing c.residueMap col ((J : ℤ) + τ)
  let s := Matrix.of fun (_ : Unit) k => c.residueMap (hh ((J : ℤ) - P.zeta k))
  let := Matrix.fromBlocksZero₂₁Invertible A U B
  have hA (i k) : A i k ∈ residueLowerField c.top J := by
    apply c.residue_hh_mem_lower J hJ
    have hri := hrow i
    have hck := hcol k
    omega
  have hU (i k) : U i k ∈ residueLowerField c.top J := by
    apply c.residue_hh_mem_lower J hJ
    have hr := hrow i
    have hz := P.zeta_nonneg k
    omega
  have hr (i k) : r i k ∈ residueLowerField c.top J := by
    apply c.residue_hh_mem_lower J hJ
    have hc := hcol k
    omega
  have hAI (i k) : ⅟A i k ∈ residueLowerField c.top J :=
    inverse_entries_mem_subfield _ A hA i k
  have hBI (i k) : ⅟B i k ∈ residueLowerField c.top J :=
    c.component_residue_inverse_mem_lower P hne hspan J hJ i k
  have hcorr : (r * ⅟A * U * ⅟B) () j ∈ residueLowerField c.top J := by
    apply matrix_product_mem_subfield _ _ _ _ hBI
    intro i k
    apply matrix_product_mem_subfield _ _ _ _ hU
    intro a b
    exact matrix_product_mem_subfield _ _ _ hr hAI a b
  obtain ⟨hn, hcoeff, R, hR, he⟩ :=
    c.component_incoming_protected_coefficient P hne hspan J hJ j
  refine ⟨hn, hcoeff, R - (r * ⅟A * U * ⅟B) () j,
    (residueLowerField c.top J).sub_mem hR hcorr, ?_⟩
  rw [upper_block_incoming_tail]
  have hs : (s * ⅟B) () j = ∑ i, c.residueMap (hh ((J : ℤ) - P.zeta i)) * ⅟B i j := by
    rw [Matrix.mul_apply]
    rfl
  rw [hs, he]
  ring

/-- The symmetric outgoing coefficient retains its greatest-row top with
every actual later-block coupling. The full suffix inverse is not discarded. -/
theorem ordered_component_outgoing_protected_coefficient {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top)
    (row col : ν → ℤ) (τ : ℤ) (J : ℕ+) (hJ : c.top < J)
    (hrow : ∀ i, row i < P.xi 0 + τ) (hcol : ∀ i, P.xi 0 + τ - (J : ℤ) < col i)
    [Invertible (vertexBetaMatrix c.residueMap row col)] (i : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    let A := (jtMatrix P.xi P.zeta).map c.residueMap
    let B := vertexBetaMatrix c.residueMap row col
    let U := Matrix.of fun k j => c.residueMap (hh (P.xi k + τ - col j))
    let r := Matrix.of fun k (_ : Unit) =>
      c.residueMap (hh (P.xi k - (P.xi 0 - (J : ℤ))))
    let s := vertexIncoming c.residueMap row (P.xi 0 + τ - (J : ℤ))
    letI := Matrix.fromBlocksZero₂₁Invertible A U B
    ⅟A i 0 ≠ 0 ∧ ⅟A i 0 ∈ residueLowerField c.top J ∧
      ∃ R ∈ residueLowerField c.top J,
        (⅟(Matrix.fromBlocks A U 0 B) * Matrix.fromRows r s) (.inl i) () =
          ⅟A i 0 * residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  classical
  let := c.profileResidueInverse P hne
  let A := (jtMatrix P.xi P.zeta).map c.residueMap
  let B := vertexBetaMatrix c.residueMap row col
  let U := Matrix.of fun k j => c.residueMap (hh (P.xi k + τ - col j))
  let r := Matrix.of fun k (_ : Unit) =>
    c.residueMap (hh (P.xi k - (P.xi 0 - (J : ℤ))))
  let s := vertexIncoming c.residueMap row (P.xi 0 + τ - (J : ℤ))
  let := Matrix.fromBlocksZero₂₁Invertible A U B
  have hB (j k) : B j k ∈ residueLowerField c.top J := by
    apply c.residue_hh_mem_lower J hJ
    have hr := hrow j
    have hc := hcol k
    omega
  have hU (j k) : U j k ∈ residueLowerField c.top J := by
    apply c.residue_hh_mem_lower J hJ
    have hx := P.xi_strictAnti.antitone (Fin.zero_le j)
    have hc := hcol k
    omega
  have hs (j k) : s j k ∈ residueLowerField c.top J := by
    apply c.residue_hh_mem_lower J hJ
    have hr := hrow j
    omega
  have hAI (j k) : ⅟A j k ∈ residueLowerField c.top J :=
    c.component_residue_inverse_mem_lower P hne hspan J hJ j k
  have hBI (j k) : ⅟B j k ∈ residueLowerField c.top J :=
    inverse_entries_mem_subfield _ B hB j k
  have hcorr : (⅟A * U * ⅟B * s) i () ∈ residueLowerField c.top J := by
    apply matrix_product_mem_subfield _ _ _ _ hs
    intro j k
    apply matrix_product_mem_subfield _ _ _ _ hBI
    intro a b
    exact matrix_product_mem_subfield _ _ _ hAI hU a b
  obtain ⟨hn, hcoeff, R, hR, he⟩ :=
    c.component_outgoing_protected_coefficient P hne hspan J hJ i
  refine ⟨hn, hcoeff, R - (⅟A * U * ⅟B * s) i (),
    (residueLowerField c.top J).sub_mem hR hcorr, ?_⟩
  rw [upper_block_outgoing_head]
  have hr : (⅟A * r) i () =
      ∑ j, ⅟A i j * c.residueMap (hh (P.xi j - (P.xi 0 - (J : ℤ)))) := by
    rw [Matrix.mul_apply]
    rfl
  rw [hr, he]
  ring

/-- Literal beta separation makes the full prefix-plus-component matrix the
upper-block matrix used above, including its complete off-diagonal rectangle. -/
theorem ordered_component_prefix_matrix {ν : Type*} {n : ℕ} (P : Profile n)
    (row col : ν → ℤ) (τ : ℤ) (hsep : ∀ i j, P.xi i + τ < col j) :
    vertexBetaMatrix c.residueMap (Sum.elim row (fun i => P.xi i + τ))
        (Sum.elim col (fun i => P.zeta i + τ)) =
      Matrix.fromBlocks (vertexBetaMatrix c.residueMap row col)
        (Matrix.of fun i k => c.residueMap (hh (row i - (P.zeta k + τ)))) 0
        ((jtMatrix P.xi P.zeta).map c.residueMap) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j =>
      change c.residueMap (hh (P.xi i + τ - col j)) = 0
      rw [hh_of_neg (by have := hsep i j; omega), map_zero]
    | inr j =>
      change c.residueMap (hh (P.xi i + τ - (P.zeta j + τ))) =
        c.residueMap (hh (P.xi i - P.zeta j))
      congr 2
      ring

/-- The original combined prefix inverse is produced from the full earlier
inverse and the actual nonselected component's residue inverse. -/
@[instance_reducible]
noncomputable def orderedComponentPrefixInverse {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (row col : ν → ℤ) (τ : ℤ)
    (hsep : ∀ i j, P.xi i + τ < col j)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    Invertible (vertexBetaMatrix c.residueMap (Sum.elim row (fun i => P.xi i + τ))
      (Sum.elim col (fun i => P.zeta i + τ))) := by
  let := c.profileResidueInverse P hne
  rw [c.ordered_component_prefix_matrix P row col τ hsep]
  exact Matrix.fromBlocksZero₂₁Invertible _ _ _

/-- The incoming original boundary vector uses the same literal combined
column list as the full prefix matrix; translation cancels exactly. -/
theorem ordered_component_prefix_incoming {ν : Type*} {n : ℕ} (P : Profile n)
    (col : ν → ℤ) (τ : ℤ) (J : ℕ+) :
    vertexOutgoing c.residueMap (Sum.elim col (fun i => P.zeta i + τ)) ((J : ℤ) + τ) =
      Matrix.fromCols (vertexOutgoing c.residueMap col ((J : ℤ) + τ))
        (Matrix.of fun (_ : Unit) k => c.residueMap (hh ((J : ℤ) - P.zeta k))) := by
  ext i k
  cases k with
  | inl k => rfl
  | inr k =>
    change c.residueMap (hh ((J : ℤ) + τ - (P.zeta k + τ))) =
      c.residueMap (hh ((J : ℤ) - P.zeta k))
    congr 2
    ring

/-- Every incoming coefficient of the literal original prefix-plus-component
matrix has the original component's nonzero protected top. All earlier blocks
remain in this matrix and in its constructed full inverse. -/
theorem ordered_component_original_incoming_top {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top)
    (row col : ν → ℤ) (τ : ℤ) (J : ℕ+) (hJ : c.top < J)
    (hrow : ∀ i, row i < (J : ℤ) + τ) (hcol : ∀ i, τ < col i)
    (hsep : ∀ i k, P.xi i + τ < col k)
    [Invertible (vertexBetaMatrix c.residueMap row col)] (j : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    letI := c.orderedComponentPrefixInverse P hne row col τ hsep
    let B := (jtMatrix P.xi P.zeta).map c.residueMap
    let rows := Sum.elim row (fun i => P.xi i + τ)
    let cols := Sum.elim col (fun i => P.zeta i + τ)
    ⅟B (Fin.last n) j ≠ 0 ∧ ⅟B (Fin.last n) j ∈ residueLowerField c.top J ∧
      ∃ R ∈ residueLowerField c.top J,
        (vertexOutgoing c.residueMap cols ((J : ℤ) + τ) *
          ⅟(vertexBetaMatrix c.residueMap rows cols)) () (.inr j) =
          residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * ⅟B (Fin.last n) j + R := by
  let := c.profileResidueInverse P hne
  let := c.orderedComponentPrefixInverse P hne row col τ hsep
  let A := vertexBetaMatrix c.residueMap row col
  let B := (jtMatrix P.xi P.zeta).map c.residueMap
  let U := Matrix.of fun i k => c.residueMap (hh (row i - (P.zeta k + τ)))
  let := Matrix.fromBlocksZero₂₁Invertible A U B
  have hinv :
      ⅟(vertexBetaMatrix c.residueMap (Sum.elim row (fun i => P.xi i + τ))
        (Sum.elim col (fun i => P.zeta i + τ))) = ⅟(Matrix.fromBlocks A U 0 B) := by
    rw [Matrix.invOf_eq_nonsing_inv, c.ordered_component_prefix_matrix P row col τ hsep,
      Matrix.invOf_eq_nonsing_inv]
  dsimp only
  rw [hinv, c.ordered_component_prefix_incoming P col τ J]
  exact c.ordered_component_incoming_protected_coefficient P hne hspan row col τ J hJ hrow hcol j

/-- Literal separation also identifies the component-plus-suffix original beta
matrix with its complete upper-block form. -/
theorem ordered_component_suffix_matrix {ν : Type*} {n : ℕ} (P : Profile n)
    (row col : ν → ℤ) (τ : ℤ) (hsep : ∀ i j, row i < P.zeta j + τ) :
    vertexBetaMatrix c.residueMap (Sum.elim (fun i => P.xi i + τ) row)
        (Sum.elim (fun i => P.zeta i + τ) col) =
      Matrix.fromBlocks ((jtMatrix P.xi P.zeta).map c.residueMap)
        (Matrix.of fun k j => c.residueMap (hh (P.xi k + τ - col j))) 0
        (vertexBetaMatrix c.residueMap row col) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change c.residueMap (hh (P.xi i + τ - (P.zeta j + τ))) =
        c.residueMap (hh (P.xi i - P.zeta j))
      congr 2
      ring
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j =>
      change c.residueMap (hh (row i - (P.zeta j + τ))) = 0
      rw [hh_of_neg (by have := hsep i j; omega), map_zero]
    | inr j => rfl

/-- Constructed full residue inverse of the literal component-plus-suffix. -/
@[instance_reducible]
noncomputable def orderedComponentSuffixInverse {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (row col : ν → ℤ) (τ : ℤ)
    (hsep : ∀ i j, row i < P.zeta j + τ)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    Invertible (vertexBetaMatrix c.residueMap (Sum.elim (fun i => P.xi i + τ) row)
      (Sum.elim (fun i => P.zeta i + τ) col)) := by
  let := c.profileResidueInverse P hne
  rw [c.ordered_component_suffix_matrix P row col τ hsep]
  exact Matrix.fromBlocksZero₂₁Invertible _ _ _

/-- The full literal outgoing vector agrees with its component/suffix split. -/
theorem ordered_component_suffix_outgoing {ν : Type*} {n : ℕ} (P : Profile n)
    (row : ν → ℤ) (τ : ℤ) (J : ℕ+) :
    vertexIncoming c.residueMap (Sum.elim (fun i => P.xi i + τ) row)
        (P.xi 0 + τ - (J : ℤ)) =
      Matrix.fromRows
        (Matrix.of fun k (_ : Unit) => c.residueMap (hh (P.xi k - (P.xi 0 - (J : ℤ)))))
        (vertexIncoming c.residueMap row (P.xi 0 + τ - (J : ℤ))) := by
  ext i k
  cases i with
  | inl i =>
    change c.residueMap (hh (P.xi i + τ - (P.xi 0 + τ - (J : ℤ)))) =
      c.residueMap (hh (P.xi i - (P.xi 0 - (J : ℤ))))
    congr 2
    ring
  | inr i => rfl

/-- Every original outgoing component coefficient retains its nonzero
greatest-row top in the presence of the complete original suffix. -/
theorem ordered_component_original_outgoing_top {ν : Type*}
    [Fintype ν] [DecidableEq ν] {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top)
    (row col : ν → ℤ) (τ : ℤ) (J : ℕ+) (hJ : c.top < J)
    (hrow : ∀ i, row i < P.xi 0 + τ) (hcol : ∀ i, P.xi 0 + τ - (J : ℤ) < col i)
    (hsep : ∀ i k, row i < P.zeta k + τ)
    [Invertible (vertexBetaMatrix c.residueMap row col)] (i : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    letI := c.orderedComponentSuffixInverse P hne row col τ hsep
    let A := (jtMatrix P.xi P.zeta).map c.residueMap
    let rows := Sum.elim (fun i => P.xi i + τ) row
    let cols := Sum.elim (fun i => P.zeta i + τ) col
    ⅟A i 0 ≠ 0 ∧ ⅟A i 0 ∈ residueLowerField c.top J ∧
      ∃ R ∈ residueLowerField c.top J,
        (⅟(vertexBetaMatrix c.residueMap rows cols) *
          vertexIncoming c.residueMap rows (P.xi 0 + τ - (J : ℤ))) (.inl i) () =
          ⅟A i 0 * residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  let := c.profileResidueInverse P hne
  let := c.orderedComponentSuffixInverse P hne row col τ hsep
  let A := (jtMatrix P.xi P.zeta).map c.residueMap
  let B := vertexBetaMatrix c.residueMap row col
  let U := Matrix.of fun k j => c.residueMap (hh (P.xi k + τ - col j))
  let := Matrix.fromBlocksZero₂₁Invertible A U B
  have hinv :
      ⅟(vertexBetaMatrix c.residueMap (Sum.elim (fun i => P.xi i + τ) row)
        (Sum.elim (fun i => P.zeta i + τ) col)) = ⅟(Matrix.fromBlocks A U 0 B) := by
    rw [Matrix.invOf_eq_nonsing_inv, c.ordered_component_suffix_matrix P row col τ hsep,
      Matrix.invOf_eq_nonsing_inv]
  dsimp only
  rw [hinv, c.ordered_component_suffix_outgoing P row τ J]
  exact c.ordered_component_outgoing_protected_coefficient P hne hspan row col τ J hJ hrow hcol i

end SelectedCoordinate
end SkewCornerDescent.Matrix
