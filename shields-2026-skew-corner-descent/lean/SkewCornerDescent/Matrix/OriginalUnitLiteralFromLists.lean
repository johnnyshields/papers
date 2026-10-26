/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitNormalizedLists
import SkewCornerDescent.Matrix.ProfileBetaRigidity
import SkewCornerDescent.Matrix.LiteralComponentBetaRecovery

/-!
# Complete original unit lists recover literal paired endpoints

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Both recovered source lists identify the literal normalized component and
its actual translated beta frame. The resulting finite equivalence preserves
every paired original row and column. Component Schur equality is not used
as a replacement for literal equality. Producing the opposite list from the
literal prefix or suffix remains the recursive reconstruction step. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Both complete original unit lists recover the literal normalized component
and produce a paired original endpoint equivalence in the actual source frame.
No equality of component Schur functions is substituted for literal equality. -/
theorem original_unit_endpoint_equiv_of_lists {n m : ℕ} (P : Profile n) (Q : Profile m)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (a' b' : OriginalSelectedBlocks (hD := hD) Q)
    (u : OriginalBlocks P) (v : OriginalBlocks Q)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) Q v)
    (hune : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hvne : Q.zeta v.val.castSucc < Q.xi v.val.succ)
    (hheight : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) =
      Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))))
    (hrows : originalUnitRowDistances P a u = originalUnitRowDistances Q a' v)
    (hcols : originalUnitColDistances P b u = originalUnitColDistances Q b' v) :
    ∃ e : Fin (originalRemovedSize (hD := hD) P u) ≃
        Fin (originalRemovedSize (hD := hD) Q v),
      ∀ k, originalRemainingRowBeta Q ⟨v, e k⟩ = originalRemainingRowBeta P ⟨u, k⟩ +
          (Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
            P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))) ∧
        originalRemainingColBeta Q ⟨v, e k⟩ = originalRemainingColBeta P ⟨u, k⟩ +
          (Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
            P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))) := by
  classical
  let U := interiorBlockProfile P u.val hune
  let V := interiorBlockProfile Q v.val hvne
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  let τ := originalComponentTau P u
  let υ := originalComponentTau Q v
  let K := x - y
  have hKQ : K = x' - y' := hheight
  have hr := hrows
  rw [original_unit_row_distances_normalized P a u hu hune,
    original_unit_row_distances_normalized Q a' v hv hvne] at hr
  change Finset.univ.image (fun i => x - (U.xi i + τ)) =
    Finset.univ.image (fun i => x' - (V.xi i + υ)) at hr
  have hri := congrArg (Finset.image (fun z : ℤ => K - z)) hr
  have hrP (i) : K - (x - (U.xi i + τ)) = U.xi i + (τ - y) := by dsimp only [K]; omega
  have hrQ (i) : K - (x' - (V.xi i + υ)) = V.xi i + (υ - y') := by omega
  simp only [Finset.image_image, Function.comp_def, hrP, hrQ] at hri
  have hc := hcols
  rw [original_unit_col_distances_normalized P b u hu hune,
    original_unit_col_distances_normalized Q b' v hv hvne] at hc
  change Finset.univ.image (fun i => U.zeta i + τ - y) =
    Finset.univ.image (fun i => V.zeta i + υ - y') at hc
  have hcP (i) : U.zeta i + τ - y = U.zeta i + (τ - y) := add_sub_assoc _ _ _
  have hcQ (i) : V.zeta i + υ - y' = V.zeta i + (υ - y') := add_sub_assoc _ _ _
  simp only [hcP, hcQ] at hc
  obtain ⟨_, hshift, hcells⟩ := literal_component_of_beta_sets U V (τ - y) (υ - y') hri hc
  have hτ : originalComponentTau Q v = originalComponentTau P u + (x' - x) := by
    change τ - y = υ - y' at hshift
    change υ = τ + (x' - x)
    dsimp only [K] at hKQ
    omega
  exact original_unit_endpoint_equiv_of_core_cells P Q u v hu hv hune hvne hcells (x' - x) hτ

end SkewCornerDescent.Matrix.SelectedCoordinate
