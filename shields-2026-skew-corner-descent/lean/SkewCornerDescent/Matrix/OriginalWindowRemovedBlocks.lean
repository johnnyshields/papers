/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowBlockOccurrences

/-!
# Actual remaining indices of whole translated nonempty blocks

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
Exact divisibility supplies selection. The produced remaining-index equivalence
preserves both selected boundary proper minors and every unselected nonempty block.
All original off-diagonal coupling entries are retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Whole matching blocks have the same actual remaining size, with selection produced. -/
theorem originalTranslatedBlock_removed_size {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val) :
    originalRemovedSize (hD := hD) P b = originalRemovedSize (hD := hD) Q d := by
  classical
  have hs := originalBlockSelected_translated_iff (hD := hD) P Q b d hb hd v he
  have hl := interiorBlockCells_translated_length P Q b.val d.val hb hd v he
  simp only [originalRemovedSize, hs, hl]

/-- Complete remaining-position equivalence, not a map of component function classes. -/
noncomputable def originalTranslatedRemovedIndexEquiv {n m : ℕ} (P : Profile n)
    (Q : Profile m) (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val) :
    Fin (originalRemovedSize (hD := hD) P b) ≃ Fin (originalRemovedSize (hD := hD) Q d) :=
  (Fin.castOrderIso (originalTranslatedBlock_removed_size (hD := hD)
    P Q b d hb hd v he)).toEquiv

/-- The omitted first selected row is preserved under the full remaining-index map. -/
theorem originalTranslatedBlock_removed_row_position {n m : ℕ} (P : Profile n)
    (Q : Profile m) (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val)
    (k : Fin (originalRemovedSize (hD := hD) P b)) :
    let e := originalTranslatedRemovedIndexEquiv (hD := hD) P Q b d hb hd v he
    (originalRemovedRowPosition (hD := hD) Q d (e k)).val =
      (originalRemovedRowPosition (hD := hD) P b k).val := by
  classical
  have heval : (originalTranslatedRemovedIndexEquiv (hD := hD) P Q b d hb hd v he k).val =
      k.val := rfl
  have hs := originalBlockSelected_translated_iff (hD := hD) P Q b d hb hd v he
  by_cases hp : originalBlockSelected (hD := hD) P b
  · have hq := hs.mp hp
    simp only [originalRemovedRowPosition, dite_eq_left hp, dite_eq_left hq, heval]
  · have hq : ¬ originalBlockSelected (hD := hD) Q d := fun h => hp (hs.mpr h)
    simp only [originalRemovedRowPosition, dite_eq_right hp, dite_eq_right hq, heval]

/-- Both entire remaining endpoint lists are translated, including selected proper minors. -/
theorem originalTranslatedBlock_removed_endpoints {n m : ℕ} (P : Profile n)
    (Q : Profile m) (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val)
    (k : Fin (originalRemovedSize (hD := hD) P b)) :
    let e := originalTranslatedRemovedIndexEquiv (hD := hD) P Q b d hb hd v he
    originalResponseRows Q ⟨d, e k⟩ = originalResponseRows P ⟨b, k⟩ + content v ∧
      originalResponseCols Q ⟨d, e k⟩ = originalResponseCols P ⟨b, k⟩ + content v := by
  let e := originalTranslatedRemovedIndexEquiv (hD := hD) P Q b d hb hd v he
  have hf := (interiorBlockCells_translated_row_extremes P Q b.val d.val hb hd v he).1
  have hr := originalTranslatedBlock_removed_row_position (hD := hD) P Q b d hb hd v he k
  have hrow : (originalRemovedRow (hD := hD) Q d (e k) : ℤ) =
      (originalRemovedRow (hD := hD) P b k : ℤ) + v.1 := by
    dsimp only [originalRemovedRow, interiorSliceIndex]
    simp only [Nat.cast_add]
    change (originalRemovedRowPosition (hD := hD) Q d (e k)).val =
      (originalRemovedRowPosition (hD := hD) P b k).val at hr
    omega
  have hcol : (originalRemovedCol (hD := hD) Q d (e k) : ℤ) =
      (originalRemovedCol (hD := hD) P b k : ℤ) + v.1 := by
    dsimp only [originalRemovedCol, originalRemovedColPosition, interiorSliceIndex]
    have hk : (e k).val = k.val := rfl
    simp only [Nat.cast_add, hk]
    omega
  have hx := interiorBlockCells_translated_row_endpoints P Q b.val
    (originalRemovedRow (hD := hD) P b k) d.val (originalRemovedRow (hD := hD) Q d (e k))
    hb hd (originalRemovedRow_block P b k) (originalRemovedRow_block Q d (e k)) v hrow he
  have hy := interiorBlockCells_translated_row_endpoints P Q b.val
    (originalRemovedCol (hD := hD) P b k) d.val (originalRemovedCol (hD := hD) Q d (e k))
    hb hd (originalRemovedCol_block P b k) (originalRemovedCol_block Q d (e k)) v hcol he
  exact ⟨hx.1, hy.2⟩

/-- Every full removed coupling entry is preserved by matching its two whole occurrences. -/
theorem originalTranslatedBlock_removed_entry {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b a : OriginalBlocks P) (d f : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (ha : P.zeta a.val.castSucc < P.xi a.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ)
    (hf : Q.zeta f.val.castSucc < Q.xi f.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val)
    (he' : translate v (interiorBlockCells P a.val) = interiorBlockCells Q f.val)
    (i : Fin (originalRemovedSize (hD := hD) P b))
    (j : Fin (originalRemovedSize (hD := hD) P a)) :
    let e := originalTranslatedRemovedIndexEquiv (hD := hD) P Q b d hb hd v he
    let e' := originalTranslatedRemovedIndexEquiv (hD := hD) P Q a f ha hf v he'
    originalRemovedMatrix Q ⟨d, e i⟩ ⟨f, e' j⟩ = originalRemovedMatrix P ⟨b, i⟩ ⟨a, j⟩ := by
  dsimp only
  have hr := (originalTranslatedBlock_removed_endpoints P Q b d hb hd v he i).1
  have hc := (originalTranslatedBlock_removed_endpoints P Q a f ha hf v he' j).2
  change hh (originalResponseRows Q _ - originalResponseCols Q _) =
    hh (originalResponseRows P _ - originalResponseCols P _)
  rw [hr, hc, add_sub_add_right_eq_sub]

end SkewCornerDescent.Matrix.SelectedCoordinate
