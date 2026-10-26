/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.SpliceNonzeroMain.CellTop
import SkewCoframeRigidity.UnitRestoration.SpliceNonzeroMain.Grades

/-!
# The zero-free core under the cell splice and the half-turn

For a diagram `D` the zero-free core `coreDiagram D` deletes every common beta.  The cell splice
`CELL ◁ D` changes only the top row, which is never a common beta, so it has the same unit
positions, the same sorting sign and the cell splice of the core as its core.  The half-turn
exchanges unit rows and unit columns, so the core of `D*` is the half-turn of the core of `D`.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe Finset
open scoped Classical

variable {m : ℕ}

/-! ### The sorting permutation -/

theorem sortPerm_apply (row col : Fin m → ℤ)
    (φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col})
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col}) (i : Fin m) :
    sortPerm row col φ e i =
      if h : i ∈ unitRows row col then (φ ⟨i, h⟩).1 else (e ⟨i, h⟩).1 := by
  unfold sortPerm
  by_cases h : i ∈ unitRows row col
  · simp [Equiv.sumCompl_symm_apply_of_pos h, h]
  · simp [Equiv.sumCompl_symm_apply_of_neg h, h]

theorem sortPerm_unit (D : BetaDiagram m) {i : Fin m} (h : i ∈ unitRows D.row D.col) :
    D.col (sortPerm D.row D.col (unitPairing D) (corePairing D) i) = D.row i := by
  rw [sortPerm_apply, dite_eq_left h]
  exact (unitPairing_spec D ⟨i, h⟩).symm

theorem rank_unique (S : Finset (Fin m)) {j j' : Fin m} (hj : j ∈ S) (hj' : j' ∈ S)
    (h : (S.filter (· < j)).card = (S.filter (· < j')).card) : j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : S.filter (· < j) ⊂ S.filter (· < j') := by
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hlt⟩
      · have := hsub (mem_filter.mpr ⟨hj, hlt⟩)
        simp at this
    have := Finset.card_lt_card this
    omega
  · have : S.filter (· < j') ⊂ S.filter (· < j) := by
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hlt⟩
      · have := hsub (mem_filter.mpr ⟨hj', hlt⟩)
        simp at this
    have := Finset.card_lt_card this
    omega

theorem sortPerm_core (D : BetaDiagram m) {i : Fin m} (h : i ∉ unitRows D.row D.col) :
    sortPerm D.row D.col (unitPairing D) (corePairing D) i ∈ coreCols D ∧
      ((coreCols D).filter
        (· < sortPerm D.row D.col (unitPairing D) (corePairing D) i)).card =
        ((coreRows D).filter (· < i)).card := by
  rw [sortPerm_apply, dite_eq_right h]
  set k := (coreRowEquiv D).symm ⟨i, h⟩ with hk
  have hi : coreRowEmb D k = i :=
    congrArg Subtype.val ((coreRowEquiv D).apply_symm_apply ⟨i, h⟩)
  have hj : ((corePairing D ⟨i, h⟩).1) = coreColEmb D k := by
    simp [corePairing, ← hk, coreColEquiv]
  rw [hj]
  refine ⟨Finset.orderEmbOfFin_mem _ _ k, ?_⟩
  have h1 := card_filter_lt_orderEmbOfFin (coreCols D) (card_coreCols_eq D) k
  have h2 := card_filter_lt_orderEmbOfFin (coreRows D) (card_coreRows_eq_count D) k
  have e1 : coreColEmb D k = (coreCols D).orderEmbOfFin (card_coreCols_eq D) k := rfl
  have e2 : coreRowEmb D k = (coreRows D).orderEmbOfFin (card_coreRows_eq_count D) k := rfl
  rw [e1, h1, ← hi, e2, h2]

/-- Diagrams with the same column list and the same unit rows, agreeing on them, have the same
sorting sign. -/
theorem sortingSign_congr {D D' : BetaDiagram m} (hc : D'.col = D.col)
    (hu : ∀ i, i ∈ unitRows D.row D.col ↔ i ∈ unitRows D'.row D'.col)
    (hr : ∀ i ∈ unitRows D.row D.col, D'.row i = D.row i) :
    sortingSign D' = sortingSign D := by
  have hcu : ∀ j, j ∈ unitCols D.row D.col ↔ j ∈ unitCols D'.row D'.col := by
    intro j
    constructor
    · rintro ⟨i, hij⟩
      have hi : i ∈ unitRows D.row D.col := ⟨j, hij⟩
      exact ⟨i, by rw [hr i hi, hc]; exact hij⟩
    · rintro ⟨i, hij⟩
      have hi : i ∈ unitRows D'.row D'.col := ⟨j, hij⟩
      have hi' := (hu i).mpr hi
      exact ⟨i, by rw [← hr i hi', ← hc]; exact hij⟩
  have hR : coreRows D' = coreRows D := by
    ext i; simp [mem_coreRows, hu]
  have hC : coreCols D' = coreCols D := by
    ext j; simp [mem_coreCols, hcu]
  unfold sortingSign
  congr 1
  ext i : 1
  by_cases hi : i ∈ unitRows D.row D.col
  · have h1 := sortPerm_unit D hi
    have h2 := sortPerm_unit D' ((hu i).mp hi)
    exact D.col_strictAnti.injective
      (((congrFun hc _).symm.trans (h2.trans (hr i hi))).trans h1.symm)
  · have hi' : i ∉ unitRows D'.row D'.col := fun h => hi ((hu i).mpr h)
    obtain ⟨a1, a2⟩ := sortPerm_core D hi
    obtain ⟨b1, b2⟩ := sortPerm_core D' hi'
    rw [hC, hR] at b2
    rw [hC] at b1
    exact rank_unique (coreCols D) b1 a1 (b2.trans a2.symm)

/-! ### The cell splice -/

theorem not_mem_unitRows_of_val_zero (D : BetaDiagram m) {i : Fin m} (hi : i.val = 0) :
    i ∉ unitRows D.row D.col := by
  rintro ⟨j, hj⟩
  have h1 : D.col j ≤ D.col i := D.col_strictAnti.antitone (by rw [Fin.le_def]; omega)
  have := D.row_nonempty i
  omega

theorem unitRows_cellTop (D : BetaDiagram m) (i : Fin m) :
    i ∈ unitRows (cellTop D).row (cellTop D).col ↔ i ∈ unitRows D.row D.col := by
  by_cases hi : i.val = 0
  · exact iff_of_false (not_mem_unitRows_of_val_zero (cellTop D) hi)
      (not_mem_unitRows_of_val_zero D hi)
  · simp only [unitRows, Set.mem_setOf_eq, cellTop_col]
    constructor
    · rintro ⟨j, hj⟩; exact ⟨j, by rwa [cellTop_row_of_ne D hi] at hj⟩
    · rintro ⟨j, hj⟩; exact ⟨j, by rwa [cellTop_row_of_ne D hi]⟩

theorem cellTop_row_unit (D : BetaDiagram m) {i : Fin m} (hi : i ∈ unitRows D.row D.col) :
    (cellTop D).row i = D.row i :=
  cellTop_row_of_ne D (fun h => not_mem_unitRows_of_val_zero D h hi)

theorem sortingSign_cellTop (D : BetaDiagram m) : sortingSign (cellTop D) = sortingSign D :=
  sortingSign_congr rfl (fun i => (unitRows_cellTop D i).symm) (fun _ hi => cellTop_row_unit D hi)

theorem coreRows_cellTop (D : BetaDiagram m) : coreRows (cellTop D) = coreRows D := by
  ext i; rw [mem_coreRows, mem_coreRows, unitRows_cellTop D i]

theorem unitCols_cellTop (D : BetaDiagram m) (j : Fin m) :
    j ∈ unitCols (cellTop D).row (cellTop D).col ↔ j ∈ unitCols D.row D.col := by
  constructor
  · rintro ⟨i, hij⟩
    have hi : i ∈ unitRows (cellTop D).row (cellTop D).col := ⟨j, hij⟩
    have hi' := (unitRows_cellTop D i).mp hi
    exact ⟨i, by rw [← cellTop_row_unit D hi']; exact hij⟩
  · rintro ⟨i, hij⟩
    have hi : i ∈ unitRows D.row D.col := ⟨j, hij⟩
    exact ⟨i, by rw [cellTop_row_unit D hi]; exact hij⟩

theorem coreCols_cellTop (D : BetaDiagram m) : coreCols (cellTop D) = coreCols D := by
  ext j; rw [mem_coreCols, mem_coreCols, unitCols_cellTop D j]

theorem coreCount_cellTop (D : BetaDiagram m) : coreCount (cellTop D) = coreCount D := by
  unfold coreCount; rw [coreRows_cellTop]

theorem unitVals_cellTop (D : BetaDiagram m) : unitVals (cellTop D) = unitVals D := by
  ext b
  simp only [mem_unitVals]
  constructor
  · rintro ⟨i, j, hi, hj⟩
    have hu : i ∈ unitRows D.row D.col :=
      (unitRows_cellTop D i).mp ⟨j, by rw [hi, hj]⟩
    exact ⟨i, j, by rw [← cellTop_row_unit D hu]; exact hi, hj⟩
  · rintro ⟨i, j, hi, hj⟩
    have hu : i ∈ unitRows D.row D.col := ⟨j, by rw [hi, hj]⟩
    exact ⟨i, j, by rw [cellTop_row_unit D hu]; exact hi, hj⟩

theorem coreRowEmb_zero_iff (D : BetaDiagram m) (k : Fin (coreCount D)) :
    (coreRowEmb D k).val = 0 ↔ k.val = 0 := by
  have hm : 0 < m := Fin.pos (coreRowEmb D k)
  set i0 : Fin m := ⟨0, hm⟩ with hi0
  obtain ⟨k0, hk0⟩ := exists_coreRowEmb D (not_mem_unitRows_of_val_zero D (i := i0) rfl)
  have hk0' : k0.val = 0 := by
    by_contra hne
    have hlt := k0.isLt
    have h1 : (⟨0, by omega⟩ : Fin (coreCount D)) < k0 := by
      show 0 < k0.val
      omega
    have h2 := (coreRowEmb D).strictMono h1
    rw [hk0, Fin.lt_def] at h2
    simp [hi0] at h2
  constructor
  · intro h
    have : coreRowEmb D k = coreRowEmb D k0 := by rw [hk0]; exact Fin.ext (by simpa [hi0] using h)
    have := (coreRowEmb D).injective this
    rw [this]; exact hk0'
  · intro h
    have : k = k0 := Fin.ext (by omega)
    rw [this, hk0]

theorem orderEmbOfFin_congr {S S' : Finset (Fin m)} (hS : S' = S) {a a' : ℕ}
    (h : S.card = a) (h' : S'.card = a') (haa : a' = a) (k : Fin a') :
    S'.orderEmbOfFin h' k = S.orderEmbOfFin h (Fin.cast haa k) := by
  subst hS; subst haa; rfl

theorem coreRowEmb_congr {D D' : BetaDiagram m} (hR : coreRows D' = coreRows D)
    (hh : coreCount D' = coreCount D) (k : Fin (coreCount D')) :
    coreRowEmb D' k = coreRowEmb D (Fin.cast hh k) :=
  orderEmbOfFin_congr hR _ _ hh k

theorem coreColEmb_congr {D D' : BetaDiagram m} (hC : coreCols D' = coreCols D)
    (hh : coreCount D' = coreCount D) (k : Fin (coreCount D')) :
    coreColEmb D' k = coreColEmb D (Fin.cast hh k) :=
  orderEmbOfFin_congr hC _ _ hh k

/-- The core of the cell splice is the cell splice of the core. -/
theorem sameLists_coreDiagram_cellTop (D : BetaDiagram m) :
    SameLists (coreDiagram (cellTop D)) (cellTop (coreDiagram D)) := by
  have hh := coreCount_cellTop D
  refine SameLists.of_eq hh (fun k => ?_) (fun k => ?_)
  · rw [coreDiagram_row, coreRowEmb_congr (coreRows_cellTop D) hh k]
    set k' := Fin.cast hh k
    have hz := coreRowEmb_zero_iff D k'
    show (if (coreRowEmb D k').val = 0 then D.row (coreRowEmb D k') + 1
      else D.row (coreRowEmb D k')) =
      if k'.val = 0 then (coreDiagram D).row k' + 1 else (coreDiagram D).row k'
    simp only [hz, coreDiagram_row]
  · rw [coreDiagram_col, coreColEmb_congr (coreCols_cellTop D) hh k]
    rfl

/-! ### The half-turn -/

theorem orderEmbOfFin_image_rev {S : Finset (Fin m)} {a a' : ℕ} (h : S.card = a)
    (h' : (S.image Fin.rev).card = a') (hh : a' = a) (k : Fin a') :
    (S.image Fin.rev).orderEmbOfFin h' k =
      Fin.rev (S.orderEmbOfFin h (Fin.rev (Fin.cast hh k))) := by
  subst hh
  have hmem : ∀ x : Fin a', Fin.rev (S.orderEmbOfFin h (Fin.rev x)) ∈ S.image Fin.rev :=
    fun x => Finset.mem_image_of_mem _ (Finset.orderEmbOfFin_mem _ _ _)
  have hmono : StrictMono fun x : Fin a' => Fin.rev (S.orderEmbOfFin h (Fin.rev x)) := by
    intro x y hxy
    have := (S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hxy)
    exact Fin.rev_lt_rev.mpr this
  have := Finset.orderEmbOfFin_unique h' hmem hmono
  exact (congrFun this k).symm

theorem unitRows_rotation {n : ℕ} (D : BetaDiagram (n + 1)) (i : Fin (n + 1)) :
    i ∈ unitRows D.rotation.row D.rotation.col ↔ Fin.rev i ∈ unitCols D.row D.col := by
  constructor
  · rintro ⟨j, hj⟩
    simp only [BetaDiagram.rotation_row, BetaDiagram.rotation_col] at hj
    exact ⟨Fin.rev j, by omega⟩
  · rintro ⟨j, hj⟩
    refine ⟨Fin.rev j, ?_⟩
    simp only [BetaDiagram.rotation_row, BetaDiagram.rotation_col, Fin.rev_rev]
    omega

theorem unitCols_rotation {n : ℕ} (D : BetaDiagram (n + 1)) (j : Fin (n + 1)) :
    j ∈ unitCols D.rotation.row D.rotation.col ↔ Fin.rev j ∈ unitRows D.row D.col := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [BetaDiagram.rotation_row, BetaDiagram.rotation_col] at hi
    exact ⟨Fin.rev i, by omega⟩
  · rintro ⟨i, hi⟩
    refine ⟨Fin.rev i, ?_⟩
    simp only [BetaDiagram.rotation_row, BetaDiagram.rotation_col, Fin.rev_rev]
    omega

theorem coreRows_rotation {n : ℕ} (D : BetaDiagram (n + 1)) :
    coreRows D.rotation = (coreCols D).image Fin.rev := by
  ext i
  simp only [mem_coreRows, unitRows_rotation, Finset.mem_image, mem_coreCols]
  constructor
  · intro h; exact ⟨Fin.rev i, h, Fin.rev_rev i⟩
  · rintro ⟨j, hj, rfl⟩; simpa using hj

theorem coreCols_rotation {n : ℕ} (D : BetaDiagram (n + 1)) :
    coreCols D.rotation = (coreRows D).image Fin.rev := by
  ext i
  simp only [mem_coreCols, unitCols_rotation, Finset.mem_image, mem_coreRows]
  constructor
  · intro h; exact ⟨Fin.rev i, h, Fin.rev_rev i⟩
  · rintro ⟨j, hj, rfl⟩; simpa using hj

theorem coreCount_rotation {n : ℕ} (D : BetaDiagram (n + 1)) :
    coreCount D.rotation = coreCount D := by
  unfold coreCount
  rw [coreRows_rotation, Finset.card_image_of_injective _ Fin.rev_injective, card_coreRows_eq]

theorem coreRowEmb_rotation {n : ℕ} (D : BetaDiagram (n + 1)) (k : Fin (coreCount D.rotation)) :
    coreRowEmb D.rotation k =
      Fin.rev (coreColEmb D (Fin.rev (Fin.cast (coreCount_rotation D) k))) := by
  unfold coreRowEmb coreColEmb
  have := orderEmbOfFin_image_rev (S := coreCols D) (card_coreCols_eq D)
    (a' := coreCount D.rotation) (by rw [← coreRows_rotation]; exact card_coreRows_eq_count _)
    (coreCount_rotation D) k
  simp only [coreRows_rotation]
  exact this

theorem coreColEmb_rotation {n : ℕ} (D : BetaDiagram (n + 1)) (k : Fin (coreCount D.rotation)) :
    coreColEmb D.rotation k =
      Fin.rev (coreRowEmb D (Fin.rev (Fin.cast (coreCount_rotation D) k))) := by
  unfold coreRowEmb coreColEmb
  have := orderEmbOfFin_image_rev (S := coreRows D) (card_coreRows_eq_count D)
    (a' := coreCount D.rotation) (by rw [← coreCols_rotation]; exact card_coreCols_eq _)
    (coreCount_rotation D) k
  simp only [coreCols_rotation]
  exact this

theorem coreColEmb_last_iff (D : BetaDiagram m) (k : Fin (coreCount D)) :
    (coreColEmb D k).val + 1 = m ↔ k.val + 1 = coreCount D := by
  have hm : 0 < m := Fin.pos (coreColEmb D k)
  set i0 : Fin m := ⟨m - 1, by omega⟩ with hi0
  have hnu : i0 ∉ unitCols D.row D.col := by
    rintro ⟨i, hi⟩
    have := lt_of_row_eq_col D hi
    have := i.isLt
    rw [Fin.lt_def] at *
    simp [hi0] at *
    omega
  obtain ⟨k0, hk0⟩ := exists_coreColEmb D hnu
  have hk0' : k0.val + 1 = coreCount D := by
    by_contra hne
    have hlt := k0.isLt
    have h1 : k0 < (⟨k0.val + 1, by omega⟩ : Fin (coreCount D)) := by
      show k0.val < k0.val + 1; omega
    have h2 := (coreColEmb D).strictMono h1
    rw [hk0, Fin.lt_def] at h2
    have := (coreColEmb D ⟨k0.val + 1, by omega⟩).isLt
    simp [hi0] at h2
    omega
  constructor
  · intro h
    have : coreColEmb D k = coreColEmb D k0 := by
      rw [hk0]; exact Fin.ext (by simp [hi0]; omega)
    have := (coreColEmb D).injective this
    rw [this]; exact hk0'
  · intro h
    have : k = k0 := Fin.ext (by omega)
    rw [this, hk0]; simp [hi0]; omega

/-- The core has the same span as the diagram. -/
theorem largestLabel_of_sameLists_core {n b : ℕ} (D : BetaDiagram (n + 1))
    (B : BetaDiagram (b + 1)) (hB : SameLists (coreDiagram D) B) :
    B.largestLabel = D.largestLabel := by
  obtain ⟨hcc, hr, hc⟩ := hB
  have e1 : (coreRowEmb D (Fin.cast hcc.symm 0)).val = 0 :=
    (coreRowEmb_zero_iff D _).mpr (by simp)
  have e2 : (coreColEmb D (Fin.cast hcc.symm (Fin.last b))).val + 1 = n + 1 :=
    (coreColEmb_last_iff D _).mpr (by simp [hcc])
  have r0 := hr (Fin.cast hcc.symm 0)
  have c0 := hc (Fin.cast hcc.symm (Fin.last b))
  have ez : Fin.cast hcc (Fin.cast hcc.symm (0 : Fin (b + 1))) = 0 := Fin.ext (by simp)
  have el : Fin.cast hcc (Fin.cast hcc.symm (Fin.last b)) = Fin.last b := Fin.ext (by simp)
  simp only [coreDiagram_row, coreDiagram_col] at r0 c0
  rw [ez] at r0
  rw [el] at c0
  unfold BetaDiagram.largestLabel
  rw [← r0, ← c0]
  have : coreRowEmb D (Fin.cast hcc.symm 0) = 0 := Fin.ext e1
  have h2 : coreColEmb D (Fin.cast hcc.symm (Fin.last b)) = Fin.last n :=
    Fin.ext (by simp; omega)
  rw [this, h2]

/-- The core of the half-turn is the half-turn of the core. -/
theorem sameLists_coreDiagram_rotation {n b : ℕ} (D : BetaDiagram (n + 1))
    (B : BetaDiagram (b + 1)) (hB : SameLists (coreDiagram D) B) :
    SameLists (coreDiagram D.rotation) B.rotation := by
  have hL := largestLabel_of_sameLists_core D B hB
  obtain ⟨hcc, hr, hc⟩ := hB
  have h1 := coreCount_rotation D
  refine SameLists.of_eq (h1.trans hcc) (fun k => ?_) (fun k => ?_)
  · rw [coreDiagram_row, coreRowEmb_rotation, BetaDiagram.rotation_row, Fin.rev_rev,
      BetaDiagram.rotation_row, hL]
    have := hc (Fin.rev (Fin.cast h1 k))
    simp only [coreDiagram_col] at this
    rw [this]
    congr 3
    ext; simp [Fin.val_rev]; omega
  · rw [coreDiagram_col, coreColEmb_rotation, BetaDiagram.rotation_col, Fin.rev_rev,
      BetaDiagram.rotation_col, hL]
    have := hr (Fin.rev (Fin.cast h1 k))
    simp only [coreDiagram_row] at this
    rw [this]
    congr 3
    ext; simp [Fin.val_rev]; omega

/-! ### Unit values -/

theorem mem_unitVals_rotation {n : ℕ} (D : BetaDiagram (n + 1)) (b : ℤ) :
    b ∈ unitVals D.rotation ↔ D.largestLabel - b ∈ unitVals D := by
  simp only [mem_unitVals, BetaDiagram.rotation_row, BetaDiagram.rotation_col]
  constructor
  · rintro ⟨i, j, hi, hj⟩
    exact ⟨Fin.rev j, Fin.rev i, by omega, by omega⟩
  · rintro ⟨i, j, hi, hj⟩
    exact ⟨Fin.rev j, Fin.rev i, by simp; omega, by simp; omega⟩

theorem unitVals_pos_lt {n : ℕ} {D : BetaDiagram (n + 1)} (hD : IsNorm D) {b : ℤ}
    (hb : b ∈ unitVals D) : 0 < b ∧ b < D.largestLabel := by
  obtain ⟨i, j, hi, hj⟩ := mem_unitVals.mp hb
  have hi0 : i.val ≠ 0 := fun h => not_mem_unitRows_of_val_zero D h ⟨j, by rw [hi, hj]⟩
  have hlast : D.col (Fin.last n) = 0 := hD
  have h1 := D.row_nonempty i
  have h2 : D.col (Fin.last n) ≤ D.col i := D.col_strictAnti.antitone (Fin.le_last i)
  have h3 : D.row 0 > D.row i :=
    D.row_strictAnti (Fin.pos_iff_ne_zero.mpr (by intro h; apply hi0; simp [h]))
  have : D.largestLabel = D.row 0 := by simp [BetaDiagram.largestLabel, hlast]
  omega

/-- A unit value is neither a core row nor a core column beta. -/
theorem unitVals_ne_core {D : BetaDiagram m} {b : ℤ} (hb : b ∈ unitVals D)
    (k : Fin (coreCount D)) : (coreDiagram D).row k ≠ b ∧ (coreDiagram D).col k ≠ b := by
  obtain ⟨i, j, hi, hj⟩ := mem_unitVals.mp hb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : coreRowEmb D k = i :=
      D.row_strictAnti.injective (by rw [coreDiagram_row] at h; rw [h, hi])
    exact coreRowEmb_mem D k ⟨j, by rw [this, hi, hj]⟩
  · have : coreColEmb D k = j :=
      D.col_strictAnti.injective (by rw [coreDiagram_col] at h; rw [h, hj])
    exact coreColEmb_mem D k ⟨i, by rw [this, hi, hj]⟩

/-- The indicator weight of a finite set of positions. -/
noncomputable def indWeight (S : Finset ℤ) : ℤ →₀ ℚ := ∑ b ∈ S, Finsupp.single b 1

theorem indWeight_apply (S : Finset ℤ) (b : ℤ) : indWeight S b = if b ∈ S then 1 else 0 := by
  unfold indWeight
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

theorem dotW_indWeight {m : ℕ} (D : BetaDiagram m) (S : Finset ℤ) :
    dotW D (indWeight S) = ∑ b ∈ S, dotS D b := by
  unfold dotW indWeight
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; simp [add_mul])]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem dotW_sub {m : ℕ} (D : BetaDiagram m) (ρ σ : ℤ →₀ ℚ) :
    dotW D (ρ - σ) = dotW D ρ - dotW D σ := by
  unfold dotW
  rw [Finsupp.sum_sub_index (by intros; rw [map_sub, sub_mul])]

/-! ### Rebuilding a diagram from its image -/

theorem strictAnti_eq_of_image_eq {k : ℕ} {f g : Fin k → ℤ} (hf : StrictAnti f) (hg : StrictAnti g)
    (h : Finset.univ.image f = Finset.univ.image g) : f = g := by
  have hcard : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf.injective]; simp
  have hf' : StrictMono fun x => f (Fin.rev x) := fun x y hxy => hf (Fin.rev_lt_rev.mpr hxy)
  have hg' : StrictMono fun x => g (Fin.rev x) := fun x y hxy => hg (Fin.rev_lt_rev.mpr hxy)
  have e1 := Finset.orderEmbOfFin_unique hcard (f := fun x => f (Fin.rev x))
    (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ _)) hf'
  have e2 := Finset.orderEmbOfFin_unique hcard (f := fun x => g (Fin.rev x))
    (fun x => h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)) hg'
  funext x
  have := congrFun (e1.trans e2.symm) (Fin.rev x)
  simpa using this

theorem SameLists.image_row {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) : Finset.univ.image D.row = Finset.univ.image E.row := by
  obtain ⟨rfl, hr, -⟩ := h
  rw [show D.row = E.row from funext hr]

theorem SameLists.image_col {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) : Finset.univ.image D.col = Finset.univ.image E.col := by
  obtain ⟨rfl, -, hc⟩ := h
  rw [show D.col = E.col from funext hc]

theorem image_coreDiagram_row (D : BetaDiagram m) :
    Finset.univ.image (coreDiagram D).row = (coreRows D).image D.row := by
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and, coreDiagram_row]
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨_, Finset.orderEmbOfFin_mem _ _ k, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨k, hk⟩ := exists_coreRowEmb D (mem_coreRows.mp hi)
    exact ⟨k, by rw [hk]⟩

theorem image_coreDiagram_col (D : BetaDiagram m) :
    Finset.univ.image (coreDiagram D).col = (coreCols D).image D.col := by
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and, coreDiagram_col]
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨_, Finset.orderEmbOfFin_mem _ _ k, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨k, hk⟩ := exists_coreColEmb D (mem_coreCols.mp hi)
    exact ⟨k, by rw [hk]⟩

theorem image_row_eq (D : BetaDiagram m) :
    Finset.univ.image D.row = Finset.univ.image (coreDiagram D).row ∪ unitVals D := by
  rw [image_coreDiagram_row]
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, mem_coreRows,
    mem_unitVals]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i ∈ unitRows D.row D.col
    · obtain ⟨j, hj⟩ := hi; exact Or.inr ⟨i, j, rfl, hj.symm⟩
    · exact Or.inl ⟨i, hi, rfl⟩
  · rintro (⟨i, -, rfl⟩ | ⟨i, j, rfl, -⟩) <;> exact ⟨i, rfl⟩

theorem image_col_eq (D : BetaDiagram m) :
    Finset.univ.image D.col = Finset.univ.image (coreDiagram D).col ∪ unitVals D := by
  rw [image_coreDiagram_col]
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, mem_coreCols,
    mem_unitVals]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hj : j ∈ unitCols D.row D.col
    · obtain ⟨i, hi⟩ := hj; exact Or.inr ⟨i, j, hi, rfl⟩
    · exact Or.inl ⟨j, hj, rfl⟩
  · rintro (⟨j, -, rfl⟩ | ⟨i, j, -, rfl⟩) <;> exact ⟨j, rfl⟩

/-- Two diagrams with the same core lists and the same unit values coincide. -/
theorem eq_of_core_unit {m : ℕ} {D E : BetaDiagram m}
    (hcore : SameLists (coreDiagram D) (coreDiagram E)) (hu : unitVals D = unitVals E) : D = E := by
  refine BetaDiagram.eq_of_rows_cols (strictAnti_eq_of_image_eq D.row_strictAnti
    E.row_strictAnti ?_) (strictAnti_eq_of_image_eq D.col_strictAnti E.col_strictAnti ?_)
  · rw [image_row_eq D, image_row_eq E, hcore.image_row, hu]
  · rw [image_col_eq D, image_col_eq E, hcore.image_col, hu]

end SkewCoframeRigidity.UnitRestoration
