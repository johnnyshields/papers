/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.UnitExpansionRest
import SkewCoframeRigidity.UnitRestoration.UnitRegularity
import SkewCoframeRigidity.Stationary.TopSupport

/-!
# Unit positions and zero-free cores

Formalizes the positional facts about the zero-free core in the unit case of `sc:positive-power`
in `shields-2026-skew-coframe-rigidity.tex`.  Positions are measured from the last column beta.  A
position carrying both a row and a column is a common beta (a unit position); the rows and columns
of the zero-free core are exactly the rows and columns that are not unit positions.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.UnitRestoration Polynomial

/-- The position of a core row is the position of the corresponding row of `D`. -/
theorem rowPos_core' {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) (k : Fin m) : rowPos C k = rowPos D (P.ρ k) := by
  unfold rowPos
  rw [P.row_eq, P.col_eq, CoreData.succ_ρ, CoreData.ce_last]

/-- A row below the top one is a unit row iff its position is a column position. -/
theorem succ_mem_unitRows_iff {n : ℕ} (D : BetaDiagram (n + 1)) (i : Fin n) :
    i.succ ∈ unitRows D.row D.col ↔ rowPos D i ∈ colSet D := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨j', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
    · refine Finset.mem_image.mpr ⟨j', Finset.mem_univ _, ?_⟩
      have := rowPos_cast D i
      have := colPos_cast D j'
      omega
    · have := rowPos_pos D i
      have := rowPos_cast D i
      omega
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    refine ⟨j.castSucc, ?_⟩
    have := rowPos_cast D i
    have := colPos_cast D j
    omega

/-- A column other than the last is a common beta iff its position is a row position. -/
theorem castSucc_mem_unitCols_iff {n : ℕ} (D : BetaDiagram (n + 1)) (j : Fin n) :
    j.castSucc ∈ unitCols D.row D.col ↔ colPos D j ∈ rowSet D := by
  constructor
  · rintro ⟨i, hi⟩
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact CoreData.top_not_unit D ⟨j.castSucc, hi⟩
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
    refine Finset.mem_image.mpr ⟨i', Finset.mem_univ _, ?_⟩
    have := rowPos_cast D i'
    have := colPos_cast D j
    omega
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    refine ⟨i.succ, ?_⟩
    have := rowPos_cast D i
    have := colPos_cast D j
    omega

/-- The row positions of the core are the row positions of `D` that are not column positions. -/
theorem rowSet_core {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) : rowSet C = rowSet D \ colSet D := by
  ext x
  simp only [rowSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨P.ρ k, (rowPos_core' P k).symm⟩, fun h => ?_⟩
    rw [rowPos_core'] at h
    exact P.ρ_not_unit k ((succ_mem_unitRows_iff D _).mpr h)
  · rintro ⟨⟨i, rfl⟩, h⟩
    have hi : i.succ ∉ unitRows D.row D.col := fun hu => h ((succ_mem_unitRows_iff D i).mp hu)
    obtain ⟨k, rfl⟩ := P.exists_ρ hi
    exact ⟨k, rowPos_core' P k⟩

/-- The column positions of the core are the column positions of `D` that are not row positions. -/
theorem colSet_core {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) : colSet C = colSet D \ rowSet D := by
  ext x
  simp only [colSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨P.ι k, (colPos_core P k).symm⟩, fun h => ?_⟩
    rw [colPos_core] at h
    exact P.ι_not_unit k ((castSucc_mem_unitCols_iff D _).mpr h)
  · rintro ⟨⟨j, rfl⟩, h⟩
    have hj : j.castSucc ∉ unitCols D.row D.col := fun hu =>
      h ((castSucc_mem_unitCols_iff D j).mp hu)
    obtain ⟨k, rfl⟩ := P.exists_ι hj
    exact ⟨k, colPos_core P k⟩

/-- The core has the same span as the diagram. -/
theorem span_core {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) : span C = span D := by
  unfold span BetaDiagram.largestLabel
  rw [P.row_eq, P.col_eq, P.re_zero, P.ce_last]

/-- Two normalized diagrams with the same row positions, column positions and span agree. -/
theorem eq_of_flag_sets {n : ℕ} {D E : BetaDiagram (n + 1)} (hDn : D.col (Fin.last n) = 0)
    (hEn : E.col (Fin.last n) = 0) (hr : rowSet D = rowSet E) (hc : colSet D = colSet E)
    (hs : span D = span E) : D = E := by
  have hrp : rowPos D = rowPos E := eq_of_image_eq (rowPos_strictAnti D) (rowPos_strictAnti E) hr
  have hcp : colPos D = colPos E := eq_of_image_eq (colPos_strictAnti D) (colPos_strictAnti E) hc
  have hrow : D.row = E.row := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · have h1 := span_cast D
      have h2 := span_cast E
      unfold BetaDiagram.largestLabel at h1 h2
      rw [hDn] at h1
      rw [hEn] at h2
      rw [hs] at h1
      omega
    · have h1 := rowPos_cast D i
      have h2 := rowPos_cast E i
      rw [hDn] at h1
      rw [hEn] at h2
      rw [hrp] at h1
      omega
  have hcol : D.col = E.col := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [hDn, hEn]
    · have h1 := colPos_cast D j
      have h2 := colPos_cast E j
      rw [hDn] at h1
      rw [hEn] at h2
      rw [hcp] at h1
      omega
  cases D
  cases E
  simp_all

/-- A connected diagram has a presented zero-free core with any index the core count allows. -/
theorem core_presented {n m : ℕ} {D : BetaDiagram (n + 1)} (hD : D.Connected)
    (hm : coreCount D = m + 1) :
    ∃ (C : BetaDiagram (m + 1)) (_ : CoreData D C), C.Connected ∧ (∀ i j, C.row i ≠ C.col j) ∧
      C.schur = (coreDiagram D).schur := by
  classical
  refine ⟨coreOfEq D hm, coreDataOfEq D hm, ⟨Nat.succ_pos m, fun i hi => ?_⟩, ?_,
    schur_coreOfEq D hm⟩
  · have hc := (coreDiagram_connected hD).2 (Fin.cast hm.symm i) (by simp [hm]; omega)
    exact hc
  · intro i j hij
    have P := coreDataOfEq D hm
    exact P.re_range (P.re i) |>.mpr ⟨i, rfl⟩ |> fun h => h ⟨P.ce j, by
      rw [← P.row_eq, ← P.col_eq]; exact hij⟩

/-- The core of a normalized diagram is normalized. -/
theorem core_isNorm {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) (hDn : D.col (Fin.last n) = 0) : C.col (Fin.last m) = 0 := by
  rw [P.col_eq, P.ce_last, hDn]

end SkewCoframeRigidity.UnitCase
