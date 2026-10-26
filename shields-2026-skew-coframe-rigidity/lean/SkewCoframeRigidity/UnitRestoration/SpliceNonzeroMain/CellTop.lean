/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.SpliceNonzero

/-!
# The cell splices on the nose

The two literal cell splices of `sc:splice-nonzero` in `shields-2026-skew-coframe-rigidity.tex`.
The `00`-splice `CELL ◁ X` has top row `X₁ + 1` and the lists of `X` otherwise, so it is
presented here as `cellTop X` on the same index type `Fin (n + 1)`; the splice `X ◁ CELL` is the
half-turn of the cell splice of the half-turn,
`s_{X ◁ CELL} = s_{CELL ◁ X*}` (`schur_splice_cell`).  Two diagrams on index types that are
only propositionally equal are compared through `SameLists`.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe

/-- Two diagrams with the same lists, the index types identified by `Fin.cast`. -/
def SameLists {m m' : ℕ} (D : BetaDiagram m) (E : BetaDiagram m') : Prop :=
  ∃ h : m = m', (∀ i, D.row i = E.row (Fin.cast h i)) ∧ ∀ i, D.col i = E.col (Fin.cast h i)

theorem BetaDiagram.eq_of_rows_cols {m : ℕ} {D E : BetaDiagram m} (hr : D.row = E.row)
    (hc : D.col = E.col) : D = E := by
  cases D; cases E; simp only at hr hc; subst hr; subst hc; rfl

theorem SameLists.exists_eq {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) : ∃ h : m = m', h ▸ D = E := by
  obtain ⟨rfl, hr, hc⟩ := h
  exact ⟨rfl, BetaDiagram.eq_of_rows_cols (funext hr) (funext hc)⟩

theorem SameLists.schur_eq {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) : D.schur = E.schur := by
  obtain ⟨rfl, hr, hc⟩ := h
  rw [BetaDiagram.eq_of_rows_cols (funext hr) (funext hc)]

theorem SameLists.dotS_eq {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) (b : ℤ) : dotS D b = dotS E b := by
  obtain ⟨rfl, hr, hc⟩ := h
  rw [BetaDiagram.eq_of_rows_cols (funext hr) (funext hc)]

theorem SameLists.dotW_eq {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) (ρ : ℤ →₀ ℚ) : dotW D ρ = dotW E ρ := by
  obtain ⟨rfl, hr, hc⟩ := h
  rw [BetaDiagram.eq_of_rows_cols (funext hr) (funext hc)]

theorem SameLists.refl {m : ℕ} (D : BetaDiagram m) : SameLists D D :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem SameLists.symm {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    (h : SameLists D E) : SameLists E D := by
  obtain ⟨rfl, hr, hc⟩ := h
  exact ⟨rfl, fun i => (hr i).symm, fun i => (hc i).symm⟩

theorem SameLists.trans {m m' m'' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'}
    {F : BetaDiagram m''} (h : SameLists D E) (h' : SameLists E F) : SameLists D F := by
  obtain ⟨rfl, hr, hc⟩ := h
  obtain ⟨rfl, hr', hc'⟩ := h'
  exact ⟨rfl, fun i => (hr i).trans (hr' i), fun i => (hc i).trans (hc' i)⟩

theorem SameLists.of_eq {m m' : ℕ} {D : BetaDiagram m} {E : BetaDiagram m'} (h : m = m')
    (hr : ∀ i, D.row i = E.row (Fin.cast h i)) (hc : ∀ i, D.col i = E.col (Fin.cast h i)) :
    SameLists D E := ⟨h, hr, hc⟩

/-- The cell splice `CELL ◁ X`: the top row is lengthened by one. -/
def cellTop {n : ℕ} (D : BetaDiagram n) : BetaDiagram n where
  row i := if i.val = 0 then D.row i + 1 else D.row i
  col := D.col
  row_strictAnti := by
    intro i j hij
    have h := D.row_strictAnti hij
    have hj : j.val ≠ 0 := by have : i.val < j.val := hij; omega
    by_cases hi : i.val = 0
    · simp only [hi, hj, ite_true, ite_false]; omega
    · simpa [hi, hj] using h
  col_strictAnti := D.col_strictAnti
  row_nonempty i := by
    have := D.row_nonempty i
    by_cases hi : i.val = 0
    · simp only [hi, ite_true]; omega
    · simpa [hi] using this

@[simp] theorem cellTop_col {n : ℕ} (D : BetaDiagram n) : (cellTop D).col = D.col := rfl

theorem cellTop_row_zero {n : ℕ} (D : BetaDiagram (n + 1)) : (cellTop D).row 0 = D.row 0 + 1 := by
  simp [cellTop]

theorem cellTop_row_of_ne {n : ℕ} (D : BetaDiagram n) {i : Fin n} (hi : i.val ≠ 0) :
    (cellTop D).row i = D.row i := by
  simp [cellTop, hi]

theorem cellTop_connected {n : ℕ} {D : BetaDiagram n} (hD : D.Connected) :
    (cellTop D).Connected := by
  refine ⟨hD.1, fun i hi => ?_⟩
  have := hD.2 i hi
  rw [cellTop_col, cellTop_row_of_ne D (by simp)]; exact this

theorem cellTop_isNorm {n : ℕ} {D : BetaDiagram (n + 1)} (hD : IsNorm D) : IsNorm (cellTop D) := hD

/-- The `00`-splice with the cell cap is the cell splice, on the nose. -/
theorem sameLists_splice_cell {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D) :
    SameLists (splice cellCap D cellCap_isNorm hD) (cellTop D) := by
  refine SameLists.of_eq (by omega) (fun i => ?_) (fun i => ?_)
  · by_cases h : i.val < 0 + 1
    · have hi0 : i.val = 0 := by omega
      have h0 : Fin.cast (by omega) i = (0 : Fin (n + 1)) := Fin.ext (by simp [hi0])
      rw [h0, cellTop_row_zero]
      simp only [splice, spliceRow, cellCap, hi0]
      simp [add_comm]
    · have hne : (Fin.cast (by omega) i : Fin (n + 1)).val ≠ 0 := by
        simp only [Fin.val_cast]; omega
      rw [cellTop_row_of_ne D hne]
      simp only [splice, spliceRow, h, dite_false]
      congr 1
  · simp only [splice, spliceCol, cellTop_col]
    split_ifs with h
    · omega
    · congr 1

@[simp] theorem splice_row {k b : ℕ} (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
    (hK : IsNorm K) (hB : IsNorm B) (i : Fin (k + b + 1)) :
    (splice K B hK hB).row i = spliceRow K B i := rfl

@[simp] theorem splice_col {k b : ℕ} (K : BetaDiagram (k + 1)) (B : BetaDiagram (b + 1))
    (hK : IsNorm K) (hB : IsNorm B) (i : Fin (k + b + 1)) :
    (splice K B hK hB).col i = spliceCol K B i := rfl

@[simp] theorem cellCap_row (i : Fin 1) : cellCap.row i = 1 := rfl

@[simp] theorem cellCap_col (i : Fin 1) : cellCap.col i = 0 := rfl

/-- The half-turn of `X ◁ CELL` is `CELL ◁ X*`, for a normalized `X`. -/
theorem sameLists_rotation_splice_cell {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D) :
    SameLists (splice D cellCap hD cellCap_isNorm).rotation (cellTop D.rotation) := by
  have hM : D.largestLabel = D.row 0 := by simp [BetaDiagram.largestLabel, hD]
  have hZ : (splice D cellCap hD cellCap_isNorm).largestLabel = D.row 0 + 1 := by
    simp [BetaDiagram.largestLabel, spliceRow, spliceCol, add_comm]
  refine SameLists.of_eq rfl (fun i => ?_) (fun i => ?_)
  · rw [Fin.cast_eq_self]
    by_cases hi : i = 0
    · subst hi
      rw [cellTop_row_zero, BetaDiagram.rotation_row, BetaDiagram.rotation_row, hZ, hM]
      simp only [Fin.rev_zero, splice_col, spliceCol, hD, cellCap_col]
      have : ¬ ((Fin.last n).val < n) := by simp
      simp only [Fin.val_last, lt_irrefl, dite_false]
      omega
    · rw [cellTop_row_of_ne _ (fun h => hi (Fin.ext h)), BetaDiagram.rotation_row, BetaDiagram.rotation_row, hZ, hM]
      have hr : (Fin.rev i).val < n := by
        have := Fin.val_rev i
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      simp only [splice_col, spliceCol, hr, dite_true, cellCap_row, Fin.eta]
      omega
  · rw [Fin.cast_eq_self]
    rw [cellTop_col, BetaDiagram.rotation_col, BetaDiagram.rotation_col, hZ, hM]
    have hr : (Fin.rev i).val < n + 1 := (Fin.rev i).isLt
    simp only [splice_row, spliceRow, hr, dite_true, cellCap_row, Fin.eta]
    omega

/-- `s_{X ◁ CELL} = s_{CELL ◁ X*}`: rotate the first splice. -/
theorem schur_splice_cell {n : ℕ} (D : BetaDiagram (n + 1)) (hD : IsNorm D) :
    (splice D cellCap hD cellCap_isNorm).schur = (cellTop D.rotation).schur := by
  rw [← (sameLists_rotation_splice_cell D hD).schur_eq]
  exact (BetaDiagram.schur_rotation _).symm

end SkewCoframeRigidity.UnitRestoration
