/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.CaseDWeighted

/-!
# The two-sided weighted Murnaghan–Nakayama rule

«The algebra map and the weighted operator» of `shields-2026-skew-marked-factor.tex`.
For every skew diagram `X` and `r > 0`,
`V_r s_X = Σ_{Y ∈ right} (-1)^{ht Y} y(Y) s_{X \ Y} - Σ_{Y ∈ left} (-1)^{ht Y} y(Y) s_{X \ Y}`,
the sums running over the `r`-cell ribbons removable on the right and on the left, `y(Y)` the least
content of `Y`.  The row-move terms of `wDeriv_jtDet` are the right sum, by rotation.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.Plan.MN MvPolynomial

theorem maxContent_ribbon {Y : Diagram} (hY : IsRibbon Y) :
    maxContent Y = minContent Y + (Y.card : ℤ) - 1 := by
  have hsY := isConnectedSkew_iff_diagonal.mp hY.1
  have hne : Y.Nonempty := hY.1.2.1
  have h1 : contents Y = Finset.Icc (minContent Y) (maxContent Y) := hsY.contents_eq
  have h2 : span Y = (Finset.Icc (minContent Y) (maxContent Y)).card := by
    unfold span; rw [h1]
  rw [Int.card_Icc] at h2
  have hle : minContent Y ≤ maxContent Y := minContent_le (maxContent_mem hne)
  have h3 : (Y.card : ℤ) = (span Y : ℤ) := by rw [hY.2]
  omega

/-- The row-move sum is the weighted sum over the ribbons removable on the right. -/
theorem rowMoveSum_eq_rightRibbons {lam mu : YoungDiagram} (hmu : mu ≤ lam) {r : ℕ}
    (hr : 0 < r) :
    rowMoveSum lam mu r =
      ∑ Y ∈ rightRibbons (skewDiagram lam mu) r,
        (ribbonSign Y : Lambda) * ((minContent Y : ℤ) : Lambda) *
          cellSchur (skewDiagram lam mu \ Y) := by
  obtain ⟨lam', mu', w, c, hle, hcol, hcells, hA, hB, hcw⟩ := exists_rotated_pair hmu
  unfold rowMoveSum
  simp only
  rw [rowMove_sum_rotate c]
  refine (sum_column_moves_weighted_cast hle hr (fun y => ((c - y - r : ℤ) : Lambda)) hcol
    (rotA c _) (rotB c _) (fun i => ?_) (fun i => ?_)).trans ?_
  · exact hA i
  · exact hB i
  rw [hcells, leftRibbons_translate, rightRibbons_eq_image_rotate,
    Finset.image_image]
  rw [Finset.sum_image (g := Gluing.translate w ∘ rotate) (fun A _ B _ h =>
      rotate_injective (translate_injective' w h))]
  refine Finset.sum_congr rfl fun Y hY => ?_
  obtain ⟨hsub, hcard, hrib, -⟩ := mem_rightRibbons.mp hY
  have hne : Y.Nonempty := hrib.1.2.1
  have hne' : (rotate Y).Nonempty := hne.image _
  have e : translate w (rotate (skewDiagram lam mu)) \ translate w (rotate Y) =
      translate w (rotate (skewDiagram lam mu \ Y)) := by
    rw [Gluing.rotate_sdiff]
    unfold Gluing.translate
    rw [Finset.image_sdiff _ _ (add_left_injective _)]
  have hmax := maxContent_ribbon hrib
  rw [hcard] at hmax
  have hsg : ribbonSign (rotate Y) = ribbonSign Y := by
    unfold ribbonSign ribbonHeight
    rw [numRows_rotate]
  simp only [Function.comp_apply]
  rw [ribbonSign_translate, hsg, minContent_translate hne', minContent_rotate hne,
    e, cellSchur_translate, cellSchur_rotate, hcw, hmax]
  congr 2
  push_cast
  ring

/-- **Two-sided weighted Murnaghan–Nakayama rule** for a skew Young diagram. -/
theorem wDeriv_cellSchur_young {lam mu : YoungDiagram} (hmu : mu ≤ lam) {r : ℕ} (hr : 0 < r) :
    wDeriv r (cellSchur (skewDiagram lam mu)) =
      ∑ Y ∈ rightRibbons (skewDiagram lam mu) r,
        (ribbonSign Y : Lambda) * ((minContent Y : ℤ) : Lambda) *
          cellSchur (skewDiagram lam mu \ Y) -
      ∑ Y ∈ leftRibbons (skewDiagram lam mu) r,
        (ribbonSign Y : Lambda) * ((minContent Y : ℤ) : Lambda) *
          cellSchur (skewDiagram lam mu \ Y) := by
  have hM : ∀ i, lam.colLen 0 ≤ i → lam.rowLen i = 0 := rowLen_eq_zero_of_colLen_le lam
  rw [cellSchur_skewDiagram_eq_jtDet hmu hM, wDeriv_jtDet]
  have h := sum_column_moves_weighted hmu hr (fun y => ((y : ℤ) : Lambda))
  have h2 := rowMoveSum_eq_rightRibbons hmu hr
  unfold rowMoveSum at h2
  simp only at h h2
  rw [h2, h]


theorem mem_rightRibbons_translate {X Y : Diagram} {m : ℕ} (v : ℤ × ℤ)
    (h : Y ∈ rightRibbons X m) : Gluing.translate v Y ∈ rightRibbons (Gluing.translate v X) m := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_rightRibbons.mp h
  exact mem_rightRibbons.mpr ⟨Finset.image_subset_image h1, by rw [card_translate, h2],
    (isRibbon_translate v).mpr h3, isUpsetIn_translate v h4⟩

theorem rightRibbons_translate (v : ℤ × ℤ) (X : Diagram) (m : ℕ) :
    rightRibbons (Gluing.translate v X) m = (rightRibbons X m).image (Gluing.translate v) := by
  ext Z
  rw [Finset.mem_image]
  constructor
  · intro hZ
    refine ⟨Gluing.translate (-v) Z, ?_, ?_⟩
    · have := mem_rightRibbons_translate (-v) hZ
      rwa [Gluing.translate_neg_translate_cancel] at this
    · rw [Gluing.translate_translate]
      simp [Gluing.translate_zero]
  · rintro ⟨Y, hY, rfl⟩
    exact mem_rightRibbons_translate v hY

/-- **Two-sided weighted Murnaghan–Nakayama rule** for an arbitrary skew diagram. -/
theorem wDeriv_cellSchur_skew {X : Diagram} (hX : IsSkew X) {r : ℕ} (hr : 0 < r) :
    wDeriv r (cellSchur X) =
      ∑ Y ∈ rightRibbons X r, (ribbonSign Y : Lambda) * ((minContent Y : ℤ) : Lambda) *
          cellSchur (X \ Y) -
      ∑ Y ∈ leftRibbons X r, (ribbonSign Y : Lambda) * ((minContent Y : ℤ) : Lambda) *
          cellSchur (X \ Y) := by
  obtain ⟨v, lam, mu, hmu, hv⟩ := KernelAux.exists_translate_skewDiagram hX
  have h0 := wDeriv_cellSchur_young hmu hr
  set S := skewDiagram lam mu with hSdef
  have hR := pDeriv_cellSchur_right_of_isSkew (isSkew_skewDiagram lam mu) hr
  have hL := pDeriv_cellSchur_left_of_isSkew (isSkew_skewDiagram lam mu) hr
  unfold ribbonSumRight at hR
  unfold ribbonSumLeft at hL
  have eR : ∑ Y ∈ rightRibbons (Gluing.translate v S) r, (ribbonSign Y : Lambda) *
      ((minContent Y : ℤ) : Lambda) * cellSchur (Gluing.translate v S \ Y) =
      ∑ Y ∈ rightRibbons S r, (ribbonSign Y : Lambda) * ((minContent Y : ℤ) : Lambda) *
        cellSchur (S \ Y) + ((content v : ℤ) : Lambda) * pDeriv r (cellSchur S) := by
    rw [rightRibbons_translate, Finset.sum_image (fun A _ B _ h => Gluing.translate_injective' v h), hR,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y hY => ?_
    obtain ⟨hsub, hcard, hrib, -⟩ := mem_rightRibbons.mp hY
    have hne : Y.Nonempty := Finset.card_pos.mp (by omega)
    have e : translate v S \ Gluing.translate v Y = Gluing.translate v (S \ Y) := by
      unfold Gluing.translate
      rw [Finset.image_sdiff _ _ (add_left_injective _)]
    rw [ribbonSign_translate, minContent_translate hne, e, Gluing.cellSchur_translate]
    push_cast
    ring
  have eL : ∑ Y ∈ leftRibbons (Gluing.translate v S) r, (ribbonSign Y : Lambda) *
      ((minContent Y : ℤ) : Lambda) * cellSchur (Gluing.translate v S \ Y) =
      ∑ Y ∈ leftRibbons S r, (ribbonSign Y : Lambda) * ((minContent Y : ℤ) : Lambda) *
        cellSchur (S \ Y) + ((content v : ℤ) : Lambda) * pDeriv r (cellSchur S) := by
    rw [leftRibbons_translate, Finset.sum_image (fun A _ B _ h => Gluing.translate_injective' v h), hL,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y hY => ?_
    obtain ⟨hsub, hcard, hrib, -⟩ := mem_leftRibbons.mp hY
    have hne : Y.Nonempty := Finset.card_pos.mp (by omega)
    have e : translate v S \ Gluing.translate v Y = Gluing.translate v (S \ Y) := by
      unfold Gluing.translate
      rw [Finset.image_sdiff _ _ (add_left_injective _)]
    rw [ribbonSign_translate, minContent_translate hne, e, Gluing.cellSchur_translate]
    push_cast
    ring
  rw [hv, eR, eL, Gluing.cellSchur_translate, h0]
  ring

end SkewMarkedFactor
