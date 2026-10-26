/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryCoreSets

/-!
# The full first-boundary parent beta sets

Formalizes `eq:boundary-beta-lists` in
`shields-2026-skew-class-inflation.tex`.  The actual inflation of the
literal thin composition and the parent restored from its suffix core
have exactly the same full beta supports.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Positive integer grid positions are the shifted zero-based arithmetic grid. -/
theorem positive_grid_eq (q z : ℤ) (M : ℕ) :
    (Finset.Icc 1 M).image (fun k : ℕ => q * k + z) = arithmeticGrid (q + z) q M := by
  classical
  ext x
  simp only [arithmeticGrid, Finset.mem_image, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨hk0, hkM⟩, hx⟩
    refine ⟨k - 1, by omega, ?_⟩
    have hs : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rw [hs]
    nlinarith [hx]
  · rintro ⟨j, hj, hx⟩
    refine ⟨j + 1, ⟨by omega, by omega⟩, ?_⟩
    push_cast
    nlinarith [hx]

/-- Whole-grid translation preserves every point and changes only its origin. -/
theorem arithmeticGrid_shift (z q t : ℤ) (M : ℕ) :
    (arithmeticGrid z q M).image (fun x => x + t) = arithmeticGrid (z + t) q M := by
  unfold arithmeticGrid
  rw [Finset.image_image]
  apply Finset.image_congr
  intro j _
  simp only [Function.comp_apply]
  ring

/-- The full row-beta support is translated by the actual inflation parameter. -/
theorem inflate_rowSet {n : ℕ} (P : Profile n) (t : ℕ) :
    (Profile.inflate t P).toBetaDiagram.rowSet =
      P.toBetaDiagram.rowSet.image (fun x => x + (t : ℤ)) := by
  change Finset.univ.image (Profile.inflate t P).xi = (Finset.univ.image P.xi).image _
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact Profile.xi_inflate t P i

/-- Inflation leaves every full column beta unchanged. -/
theorem inflate_colSet {n : ℕ} (P : Profile n) (t : ℕ) :
    (Profile.inflate t P).toBetaDiagram.colSet = P.toBetaDiagram.colSet := by
  change Finset.univ.image (Profile.inflate t P).zeta = Finset.univ.image P.zeta
  apply congrArg (fun f : Fin (n + 1) → ℤ => Finset.univ.image f)
  funext i
  exact Profile.zeta_inflate t P i

namespace BoundaryParameters

variable (B : BoundaryParameters)

/-- Restoring every deleted suffix grid point fills exactly the complete unshifted grid. -/
theorem restoredParent_rowSet (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) :
    (B.restoredParent M hM T hT).rowSet = arithmeticGrid B.q B.q M ∪
      (insert M T).image (fun k : ℕ => (B.q : ℤ) * k + B.p) := by
  classical
  have ht : T ⊆ Finset.Icc 1 M := by
    intro k hk
    have h := Finset.mem_Ioo.mp (hT hk)
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.le⟩
  have hg : (Finset.Icc 1 M).image (fun k : ℕ => (B.q : ℤ) * k) =
      arithmeticGrid B.q B.q M := by
    simpa only [add_zero] using positive_grid_eq B.q 0 M
  unfold restoredParent
  rw [BetaDiagram.restore_rowSet, B.core_rowSet M hM T hT]
  unfold commonBetas
  rw [show ((Finset.Icc 1 M \ T).image (fun k : ℕ => (B.q : ℤ) * k) ∪
      (insert M T).image (fun k : ℕ => (B.q : ℤ) * k + B.p)) ∪
        T.image (fun k : ℕ => (B.q : ℤ) * k) =
      ((Finset.Icc 1 M \ T).image (fun k : ℕ => (B.q : ℤ) * k) ∪
        T.image (fun k : ℕ => (B.q : ℤ) * k)) ∪
          (insert M T).image (fun k : ℕ => (B.q : ℤ) * k + B.p) by ac_rfl]
  rw [← Finset.image_union, Finset.sdiff_union_of_subset ht, hg]

/-- The lower beta list contains the fixed residue grid and exactly the restored suffix grid. -/
theorem restoredParent_colSet (M : ℕ) (hM : 0 < M) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) :
    (B.restoredParent M hM T hT).colSet = arithmeticGrid ((B.q : ℤ) - B.a) B.q M ∪
      (insert 0 T).image (fun k : ℕ => (B.q : ℤ) * k) := by
  classical
  have hg : (Finset.Icc 1 M).image (fun k : ℕ => (B.q : ℤ) * k - B.a) =
      arithmeticGrid ((B.q : ℤ) - B.a) B.q M := by
    simpa only [sub_eq_add_neg] using positive_grid_eq B.q (-(B.a : ℤ)) M
  unfold restoredParent
  rw [BetaDiagram.restore_colSet, B.core_colSet, hg]
  simp only [commonBetas, Finset.insert_eq, Finset.image_union, Finset.image_singleton,
    Nat.cast_zero, mul_zero]
  ac_rfl

/-- All restored common coordinates are distinct; no row-count loss is hidden in a set image. -/
theorem commonBetas_card (T : Finset ℕ) : (B.commonBetas T).card = T.card := by
  unfold commonBetas
  apply Finset.card_image_of_injective
  intro k l he
  have hq : (B.q : ℤ) ≠ 0 := by have := B.q_pos; omega
  have hh := mul_left_cancel₀ hq he
  exact_mod_cast hh

end BoundaryParameters

namespace ThinParameters

variable (B : ThinParameters)

/-- The actual boundary row-beta set, obtained by inflating the full original lists. -/
theorem boundary_rowSet {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.rowSet =
      arithmeticGrid B.boundary.q B.boundary.q M ∪
        (insert M (suffixSet α)).image
          (fun k : ℕ => (B.boundary.q : ℤ) * k + B.boundary.p) := by
  have hbp : (B.b : ℤ) + B.boundary.p = B.boundary.q := by
    have hq := B.boundary_q_eq
    have hc := B.c_lt_a
    dsimp [boundary, BoundaryParameters.ofThin] at *
    omega
  rw [inflate_rowSet, B.diagram_rowSet, Finset.image_union, arithmeticGrid_shift, hbp,
    Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro k _
  simp only [Function.comp_apply]
  ring

/-- The actual boundary column-beta set remains the original full column list. -/
theorem boundary_colSet {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.colSet =
      arithmeticGrid ((B.boundary.q : ℤ) - B.a) B.boundary.q M ∪
        (insert 0 (suffixSet α)).image (fun k : ℕ => (B.boundary.q : ℤ) * k) := by
  have hq : (B.b : ℤ) - B.c = (B.boundary.q : ℤ) - B.a := by
    have h := B.boundary_q_eq
    omega
  rw [inflate_colSet, B.diagram_colSet, hq]
  congr 1
  apply Finset.image_congr
  intro k _
  ring

end ThinParameters
end SkewClassInflation
