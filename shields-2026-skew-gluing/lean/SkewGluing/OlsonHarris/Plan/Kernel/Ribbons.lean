import SkewGluing.OlsonHarris.Plan.Defs

/-!
# Removal of left and right ribbons

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.2 (`OlsonHarris2024HopfApplications`), the
combinatorial part: a downset or an upset of a skew diagram leaves a skew diagram, and the
removal of a downset and of an upset commute.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace KernelAux

theorem isSkew_sdiff_of_isDownsetIn {X Y : Diagram} (hX : IsSkew X) (hY : IsDownsetIn X Y) :
    IsSkew (X \ Y) := by
  intro x hx y hy h1 h2 i hi j hj
  rw [Finset.mem_sdiff] at hx hy ⊢
  have hc : (i, j) ∈ X := hX x hx.1 y hy.1 h1 h2 i hi j hj
  refine ⟨hc, fun hcY => hx.2 (hY.2 x hx.1 _ hcY ?_ ?_)⟩
  · exact (Finset.mem_Icc.mp hi).1
  · exact (Finset.mem_Icc.mp hj).1

theorem isSkew_sdiff_of_isUpsetIn {X Y : Diagram} (hX : IsSkew X) (hY : IsUpsetIn X Y) :
    IsSkew (X \ Y) := by
  intro x hx y hy h1 h2 i hi j hj
  rw [Finset.mem_sdiff] at hx hy ⊢
  have hc : (i, j) ∈ X := hX x hx.1 y hy.1 h1 h2 i hi j hj
  refine ⟨hc, fun hcY => hy.2 (hY.2 y hy.1 _ hcY ?_ ?_)⟩
  · exact (Finset.mem_Icc.mp hi).2
  · exact (Finset.mem_Icc.mp hj).2

/-- A downset of `X \ Z` is a downset of `X` when `Z` is an upset of `X`. -/
theorem isDownsetIn_of_upset {X Y Z : Diagram} (hZ : IsUpsetIn X Z) (hY : IsDownsetIn (X \ Z) Y) :
    IsDownsetIn X Y := by
  refine ⟨fun y hy => (Finset.mem_sdiff.mp (hY.1 hy)).1, fun x hx y hy h1 h2 => ?_⟩
  have hyZ : y ∉ Z := (Finset.mem_sdiff.mp (hY.1 hy)).2
  have hyX : y ∈ X := (Finset.mem_sdiff.mp (hY.1 hy)).1
  have hxZ : x ∉ Z := fun hxZ => hyZ (hZ.2 y hyX x hxZ h1 h2)
  exact hY.2 x (Finset.mem_sdiff.mpr ⟨hx, hxZ⟩) y hy h1 h2

/-- An upset `Z` of `X` is an upset of `X \ Y` when `Y` is a downset of `X \ Z`. -/
theorem isUpsetIn_of_downset {X Y Z : Diagram} (hZ : IsUpsetIn X Z) (hY : IsDownsetIn (X \ Z) Y) :
    IsUpsetIn (X \ Y) Z := by
  refine ⟨fun z hz => Finset.mem_sdiff.mpr ⟨hZ.1 hz, fun hzY => ?_⟩, fun x hx z hz h1 h2 => ?_⟩
  · exact (Finset.mem_sdiff.mp (hY.1 hzY)).2 hz
  · exact hZ.2 x (Finset.mem_sdiff.mp hx).1 z hz h1 h2

/-- An upset of `X \ Y` is an upset of `X` when `Y` is a downset of `X`. -/
theorem isUpsetIn_of_downset' {X Y Z : Diagram} (hY : IsDownsetIn X Y) (hZ : IsUpsetIn (X \ Y) Z) :
    IsUpsetIn X Z := by
  refine ⟨fun z hz => (Finset.mem_sdiff.mp (hZ.1 hz)).1, fun x hx z hz h1 h2 => ?_⟩
  have hzY : z ∉ Y := (Finset.mem_sdiff.mp (hZ.1 hz)).2
  have hzX : z ∈ X := (Finset.mem_sdiff.mp (hZ.1 hz)).1
  have hxY : x ∉ Y := fun hxY => hzY (hY.2 z hzX x hxY h1 h2)
  exact hZ.2 x (Finset.mem_sdiff.mpr ⟨hx, hxY⟩) z hz h1 h2

/-- A downset `Y` of `X` is a downset of `X \ Z` when `Z` is an upset of `X \ Y`. -/
theorem isDownsetIn_of_upset' {X Y Z : Diagram} (hY : IsDownsetIn X Y) (hZ : IsUpsetIn (X \ Y) Z) :
    IsDownsetIn (X \ Z) Y := by
  refine ⟨fun y hy => Finset.mem_sdiff.mpr ⟨hY.1 hy, fun hyZ => ?_⟩, fun x hx y hy h1 h2 => ?_⟩
  · exact (Finset.mem_sdiff.mp (hZ.1 hyZ)).2 hy
  · exact hY.2 x (Finset.mem_sdiff.mp hx).1 y hy h1 h2

end KernelAux

namespace KernelAux

/-- Removing a ribbon removable on the left from a skew diagram leaves a skew diagram. -/
theorem isSkew_sdiff_of_mem_leftRibbons {X Y : Diagram} {m : ℕ} (hX : IsSkew X)
    (hY : Y ∈ leftRibbons X m) : IsSkew (X \ Y) :=
  isSkew_sdiff_of_isDownsetIn hX (mem_leftRibbons.mp hY).2.2.2

/-- Removing a ribbon removable on the right from a skew diagram leaves a skew diagram. -/
theorem isSkew_sdiff_of_mem_rightRibbons {X Y : Diagram} {m : ℕ} (hX : IsSkew X)
    (hY : Y ∈ rightRibbons X m) : IsSkew (X \ Y) :=
  isSkew_sdiff_of_isUpsetIn hX (mem_rightRibbons.mp hY).2.2.2

theorem leftOp_shape (m : ℕ) (X : Diagram) :
    leftOp m (shape X) = ∑ Y ∈ leftRibbons X m, (ribbonSign Y : ℚ) • shape (X \ Y) := by
  simp [leftOp, shape, Finsupp.linearCombination_single]

theorem rightOp_shape (m : ℕ) (X : Diagram) :
    rightOp m (shape X) = ∑ Y ∈ rightRibbons X m, (ribbonSign Y : ℚ) • shape (X \ Y) := by
  simp [rightOp, shape, Finsupp.linearCombination_single]

/-- The left and right removals commute (the proof does not use skewness of `X`). -/
theorem leftOp_rightOp_comm_shape {X : Diagram} (m n : ℕ) :
    leftOp m (rightOp n (shape X)) = rightOp n (leftOp m (shape X)) := by
  rw [rightOp_shape, leftOp_shape, map_sum, map_sum]
  simp only [map_smul, leftOp_shape, rightOp_shape, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => (⟨p.2, p.1⟩ : (_ : Diagram) × Diagram))
    (fun p _ => (⟨p.2, p.1⟩ : (_ : Diagram) × Diagram)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨Z, Y⟩ hp
    rw [Finset.mem_sigma] at hp ⊢
    obtain ⟨hZ, hY⟩ := hp
    rw [mem_rightRibbons] at hZ
    rw [mem_leftRibbons] at hY
    obtain ⟨hZs, hZc, hZr, hZu⟩ := hZ
    obtain ⟨hYs, hYc, hYr, hYd⟩ := hY
    refine ⟨mem_leftRibbons.mpr ⟨fun y hy => (Finset.mem_sdiff.mp (hYs hy)).1, hYc, hYr,
      isDownsetIn_of_upset hZu hYd⟩, mem_rightRibbons.mpr ⟨?_, hZc, hZr,
      isUpsetIn_of_downset hZu hYd⟩⟩
    exact fun z hz => Finset.mem_sdiff.mpr ⟨hZs hz, fun hzY =>
      (Finset.mem_sdiff.mp (hYs hzY)).2 hz⟩
  · rintro ⟨Y, Z⟩ hp
    rw [Finset.mem_sigma] at hp ⊢
    obtain ⟨hY, hZ⟩ := hp
    rw [mem_leftRibbons] at hY
    rw [mem_rightRibbons] at hZ
    obtain ⟨hYs, hYc, hYr, hYd⟩ := hY
    obtain ⟨hZs, hZc, hZr, hZu⟩ := hZ
    refine ⟨mem_rightRibbons.mpr ⟨fun z hz => (Finset.mem_sdiff.mp (hZs hz)).1, hZc, hZr,
      isUpsetIn_of_downset' hYd hZu⟩, mem_leftRibbons.mpr ⟨?_, hYc, hYr,
      isDownsetIn_of_upset' hYd hZu⟩⟩
    exact fun y hy => Finset.mem_sdiff.mpr ⟨hYs hy, fun hyZ =>
      (Finset.mem_sdiff.mp (hZs hyZ)).2 hy⟩
  · rintro ⟨Z, Y⟩ _; rfl
  · rintro ⟨Y, Z⟩ _; rfl
  · rintro ⟨Z, Y⟩ _
    simp only [mul_comm, sdiff_right_comm X Z Y]

end KernelAux

end Plan

end SkewGluing
