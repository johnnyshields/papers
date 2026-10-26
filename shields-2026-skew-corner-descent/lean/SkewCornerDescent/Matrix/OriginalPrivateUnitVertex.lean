/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.ProfileInvariant
import SkewGluing.InteriorBounds
import SkewGluing.InteriorProfile
import SkewCornerDescent.Matrix.InteriorBlockComponents

/-!
# A private vertical cut has its literal original unit vertex

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Two actual singleton consecutive diagonals determine whether the beta lists
contain a literal `h₀` pivot at their cut. It occurs exactly when their two
cells share a column, without assuming an interior-component realization.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Two actual cells on a singleton diagonal are the same literal cell. -/
theorem private_diagonal_cells_eq {D : Diagram} {k : ℤ} {x y : ℤ × ℤ}
    (hsingle : diagLo D k = diagHi D k) (hx : x ∈ D) (hy : y ∈ D)
    (hcx : content x = k) (hcy : content y = k) : x = y := by
  have hxlo := diagLo_le hx hcx
  have hxhi := le_diagHi hx hcx
  have hylo := diagLo_le hy hcy
  have hyhi := le_diagHi hy hcy
  have hr : x.1 = y.1 := by omega
  apply Prod.ext hr
  dsimp only [content] at hcx hcy
  omega

/-- A singleton original diagonal contains no actual southeast-interior cell.
Both the cell and its southeast neighbor would occupy that same diagonal. -/
theorem private_diagonal_no_interior {D : Diagram} {k : ℤ}
    (hsingle : diagLo D k = diagHi D k) :
    ∀ x ∈ diagramInterior D, content x ≠ k := by
  intro x hx hcontent
  have hm : x ∈ D ∧ x + eCell ∈ D := Finset.mem_filter.mp hx
  have hp : content (x + eCell) = k := by
    simpa [content, eCell] using hcontent
  have he := private_diagonal_cells_eq hsingle hm.1 hm.2 hcontent hp
  have hrow : x.1 = x.1 + 1 := by
    simpa [eCell] using congrArg Prod.fst he
  omega

/-- In a skew diagram, the absence of a southeast-interior cell on a
diagonal forces that diagonal to be empty or a singleton. -/
theorem private_diagonal_of_no_interior {D : Diagram} {k : ℤ}
    (hshape : IsSkew D) (hno : ∀ x ∈ diagramInterior D, content x ≠ k) :
    diagLo D k = diagHi D k := by
  classical
  by_cases hnonempty : (diagRows D k).Nonempty
  · have hk := mem_contents.mpr hnonempty
    have hx := diagLo_mem hk
    have hy := diagHi_mem hk
    have hle := diagLo_le_diagHi hk
    by_contra hne
    have hlt : diagLo D k < diagHi D k := lt_of_le_of_ne hle hne
    have hn : (diagLo D k, diagLo D k + k) + eCell ∈ D := by
      apply hshape _ hx _ hy (by omega) (by omega)
      · simp only [eCell, Finset.mem_Icc]
        constructor <;> omega
      · simp only [eCell, Finset.mem_Icc]
        constructor <;> omega
    have hi : (diagLo D k, diagLo D k + k) ∈ diagramInterior D :=
      Finset.mem_filter.mpr ⟨hx, hn⟩
    exact hno _ hi (by simp [content])
  · simp [diagLo, diagHi, hnonempty]

/-- Every complete interior component lies strictly on one side of a private
singleton cut. No nonrow component can cross or touch its boundary. -/
theorem private_diagonal_interior_components_separated {D : Diagram} {k : ℤ}
    (hshape : IsSkew D) (hsingle : diagLo D k = diagHi D k) :
    ∀ C ∈ edgeComponents (diagramInterior D), maxContent C < k ∨ k < minContent C := by
  intro C hC
  have hc := isConnectedSkew_component hshape.interior hC
  by_cases hleft : maxContent C < k
  · exact Or.inl hleft
  · right
    by_contra hright
    have hk : k ∈ contents C := (isConnectedSkew_iff_diagonal.mp hc).mem_contents_iff.mpr
      ⟨le_of_not_gt hright, le_of_not_gt hleft⟩
    obtain ⟨x, hx, hcontent⟩ := Finset.mem_image.mp hk
    exact private_diagonal_no_interior hsingle x (component_subset hC hx) hcontent

/-- Every original corner-core beta pair lies strictly below or above a
two-diagonal private cut, except for its literal zero-index unit vertex.
No other row or column can touch the separating coordinate. -/
theorem profile_private_beta_pair_trichotomy {n : ℕ} (P : Profile n) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1)) (i : Fin n) :
    (P.xi i.succ < k ∧ P.zeta i.castSucc < k) ∨
      (k < P.xi i.succ ∧ k < P.zeta i.castSucc) ∨
      (P.xi i.succ = k ∧ P.zeta i.castSucc = k) := by
  have hexclude (a : ℤ) (hsingle : diagLo P.cells a = diagHi P.cells a) :
      ¬ (P.zeta i.castSucc ≤ a ∧ a < P.xi i.succ) := by
    intro h
    have hx : ((i : ℤ), (i : ℤ) + a) ∈ diagramInterior P.cells := by
      rw [P.mem_interior_cells]
      exact ⟨i, rfl, by omega, by omega⟩
    exact private_diagonal_no_interior hsingle _ hx (by simp [content])
  have h0 := hexclude k hcur
  have h1 := hexclude (k - 1) hprev
  have horder := P.zeta_le_xi_succ i
  omega

/-- Any retained row and column from one complete original block have the same
strict side of a private cut. An empty block is the single literal unit pair. -/
theorem profile_private_same_block_endpoints_trichotomy {n : ℕ} (P : Profile n) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (i j : Fin n) (hlabel : interiorBlock P j = interiorBlock P i) :
    (P.xi j.succ < k ∧ P.zeta i.castSucc < k) ∨
      (k < P.xi j.succ ∧ k < P.zeta i.castSucc) ∨
      (P.xi j.succ = k ∧ P.zeta i.castSucc = k) := by
  by_cases hi : P.zeta i.castSucc < P.xi i.succ
  · have hj := interior_block_row_nonempty P hi hlabel
    let C := interiorBlockCells P i
    have hmem := interiorBlockCells_mem_components P i hi
    have hleft : ((i : ℤ), P.zeta i.castSucc + (i : ℤ)) ∈ C := by
      apply (mem_interiorBlockCells P i _ _).mpr
      exact ⟨i, rfl, rfl, le_rfl, by omega⟩
    have hright : ((j : ℤ), P.xi j.succ + (j : ℤ) - 1) ∈ C := by
      apply (mem_interiorBlockCells P i _ _).mpr
      exact ⟨j, hlabel, rfl, by omega, by omega⟩
    have hcol : P.zeta i.castSucc ∈ contents C := by
      exact Finset.mem_image.mpr ⟨_, hleft, by dsimp only [content]; omega⟩
    have hrow : P.xi j.succ - 1 ∈ contents C := by
      exact Finset.mem_image.mpr ⟨_, hright, by dsimp only [content]; omega⟩
    have hcmin := minContent_le hcol
    have hcmax := le_maxContent hcol
    have hrmin := minContent_le hrow
    have hrmax := le_maxContent hrow
    have hs := private_diagonal_interior_components_separated P.isSkew_cells hcur C hmem
    have hp := private_diagonal_interior_components_separated P.isSkew_cells hprev C hmem
    change maxContent C < k ∨ k < minContent C at hs
    change maxContent C < k - 1 ∨ k - 1 < minContent C at hp
    omega
  · have he : P.xi i.succ = P.zeta i.castSucc := by
      have h := P.zeta_le_xi_succ i
      omega
    have hj := interior_empty_row_isolated P i he j hlabel
    subst j
    exact profile_private_beta_pair_trichotomy P k hcur hprev i

/-- A literal beta unit at a genuine two-diagonal private cut occurs exactly
when its two actual cells share a column. Horizontal private edges have none. -/
theorem profile_private_unit_vertex_iff_vertical {n : ℕ} (P : Profile n) (k : ℤ)
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = k) (hp : content prev = k - 1)
    (hsingle : diagLo P.cells k = diagHi P.cells k)
    (hprevsingle : diagLo P.cells (k - 1) = diagHi P.cells (k - 1)) :
    (∃ i : Fin n, P.xi i.succ = k ∧ P.zeta i.castSucc = k) ↔ cur.2 = prev.2 := by
  constructor
  · rintro ⟨i, hxi, hzeta⟩
    have hx := P.row_left_mem_cells i.castSucc
    have hy := P.row_right_mem_cells i.succ
    rw [hzeta] at hx
    rw [hxi] at hy
    have hcx : content ((i.castSucc : ℤ), k + (i.castSucc : ℤ)) = k := by
      simp only [content]; omega
    have hcy : content ((i.succ : ℤ), k + (i.succ : ℤ) - 1) = k - 1 := by
      simp only [content]; omega
    have he := private_diagonal_cells_eq hsingle hx hcur hcx hc
    have hf := private_diagonal_cells_eq hprevsingle hy hprev hcy hp
    have hec := congrArg Prod.snd he
    have hfc := congrArg Prod.snd hf
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hec hfc
    omega
  · intro hcol
    have hbcur := P.row_bounds_of_mem_cells hcur
    have hbprev := P.row_bounds_of_mem_cells hprev
    have hrows : prev.1 = cur.1 + 1 := by
      dsimp only [content] at hc hp
      omega
    let i : Fin n := ⟨cur.1.toNat, by omega⟩
    have hi : (i : ℤ) = cur.1 := Int.toNat_of_nonneg hbcur.1
    have his : (i.succ : ℤ) = cur.1 + 1 := by
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega
    have hcpoint : cur = ((i.castSucc : ℤ), (i.castSucc : ℤ) + k) := by
      apply Prod.ext
      · exact hi.symm
      · dsimp only [content] at hc
        change cur.2 = (i : ℤ) + k
        omega
    have hppoint : prev = ((i.succ : ℤ), (i.castSucc : ℤ) + k) := by
      apply Prod.ext
      · omega
      · change prev.2 = (i : ℤ) + k
        dsimp only [content] at hc hp
        omega
    have hcmem := hcpoint ▸ hcur
    have hpmem := hppoint ▸ hprev
    have hcb := (P.mem_cells_fin i.castSucc _).mp hcmem
    have hpb := (P.mem_cells_fin i.succ _).mp hpmem
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hcb hpb
    have hzeta : P.zeta i.castSucc = k := by
      by_contra he
      have hlt : P.zeta i.castSucc < k := by omega
      have hx : ((i.castSucc : ℤ), (i.castSucc : ℤ) + k - 1) ∈ P.cells := by
        rw [P.mem_cells_fin]
        exact ⟨by omega, by omega⟩
      have heq := private_diagonal_cells_eq hprevsingle hx hprev
        (by simp only [content]; omega) hp
      have hr := congrArg Prod.fst heq
      change (i : ℤ) = prev.1 at hr
      omega
    have hxi : P.xi i.succ = k := by
      by_contra he
      have hlt : k < P.xi i.succ := by omega
      have hx : ((i.succ : ℤ), (i.succ : ℤ) + k) ∈ P.cells := by
        rw [P.mem_cells_fin]
        exact ⟨by omega, by omega⟩
      have heq := private_diagonal_cells_eq hsingle hx hcur
        (by simp only [content]; omega) hc
      have hr := congrArg Prod.fst heq
      change (i.succ : ℤ) = cur.1 at hr
      omega
    exact ⟨i, hxi, hzeta⟩

/-- The original beta lists have exactly one unit pivot at a private vertical
cut and none at a horizontal cut. The count is produced, not supplied. -/
theorem profile_private_unit_vertex_count {n : ℕ} (P : Profile n) (k : ℤ)
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = k) (hp : content prev = k - 1)
    (hsingle : diagLo P.cells k = diagHi P.cells k)
    (hprevsingle : diagLo P.cells (k - 1) = diagHi P.cells (k - 1)) :
    (Finset.univ.filter (fun i : Fin n => P.xi i.succ = k ∧ P.zeta i.castSucc = k)).card =
      if cur.2 = prev.2 then 1 else 0 := by
  classical
  have hiff := profile_private_unit_vertex_iff_vertical P k cur prev hcur hprev hc hp
    hsingle hprevsingle
  by_cases hcol : cur.2 = prev.2
  · obtain ⟨i, hxi, hzeta⟩ := hiff.mpr hcol
    have hf : Finset.univ.filter (fun j : Fin n => P.xi j.succ = k ∧ P.zeta j.castSucc = k) =
        {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hj⟩
        have he := P.zeta_strictAnti.injective (hj.trans hzeta.symm)
        exact Fin.castSucc_inj.mp he
      · intro he
        subst j
        exact ⟨hxi, hzeta⟩
    rw [hf, Finset.card_singleton, ite_eq_left hcol]
  · have hf : Finset.univ.filter (fun i : Fin n =>
        P.xi i.succ = k ∧ P.zeta i.castSucc = k) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      exact hcol (hiff.mp ⟨i, (Finset.mem_filter.mp hi).2⟩)
    rw [hf, Finset.card_empty, ite_eq_right hcol]

end SkewCornerDescent.Matrix
