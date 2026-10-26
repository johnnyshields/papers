/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureExterior

/-!
# Actual gap coordinates in the literal horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete translated
component equality identifies the original selected endpoints. Both exterior caps and every
internal gap in either copy are computed from those endpoints. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- Equality of complete translated selected components identifies their least contents. -/
theorem originalSelected_minContent_of_translated_cells {D : Diagram}
    {hD : IsConnectedSkew D} {n m : ℕ} (P : Profile n) (Q : Profile m)
    (a : OriginalSelectedBlocks (hD := hD) P) (b : OriginalSelectedBlocks (hD := hD) Q)
    (u v : ℤ × ℤ)
    (h : translate v (interiorBlockCells Q b.val.val) =
      translate u (interiorBlockCells P a.val.val)) :
    Q.zeta (interiorBlockLast Q b.val.val).castSucc + content v =
      P.zeta (interiorBlockLast P a.val.val).castSucc + content u := by
  have he := congrArg minContent h
  rw [minContent_translate (interiorBlockCells_connected Q b.val.val
      (originalBlockSelected_nonempty Q b.val b.property)).2.1,
    minContent_translate (interiorBlockCells_connected P a.val.val
      (originalBlockSelected_nonempty P a.val a.property)).2.1,
    interiorBlockCells_minContent Q b.val.val
      (originalBlockSelected_nonempty Q b.val b.property),
    interiorBlockCells_minContent P a.val.val
      (originalBlockSelected_nonempty P a.val a.property)] at he
  exact he

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The first cap of the actual closure is the first cap of its source, not a new response top. -/
theorem originalHorizontalClosure_first_cap {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) Q 0 0 =
      originalHessenbergDistance (hD := hD) P 0 0 := by
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  have he := originalHorizontalClosure_enumeration_upper_cells P Q v hQ ⟨0, hB⟩
  have hz := originalSelected_minContent_of_translated_cells P Q _ _ _ _ he
  have hv := originalHorizontalClosure_profile_endpoints P Q v hQ
  rw [originalHorizontalDisplacement_content, P.zeta_last] at hz
  change Q.zeta (interiorBlockLast Q
      (originalSelectedEnumeration (hD := hD) Q ⟨0, hBQ⟩).val.val).castSucc + content v =
    P.zeta (interiorBlockLast P
      (originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩).val.val).castSucc +
        (P.xi 0 - 0) at hz
  rw [hv.1] at hz
  rw [originalHessenbergDistance_first Q hBQ, originalHessenbergDistance_first P hB]
  unfold originalFirstCapDistance
  rw [hv.2]
  omega

/-- The last cap of the actual closure is the original last cap, with its full endpoint retained. -/
theorem originalHorizontalClosure_last_cap {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) Q (Fin.last _) (Fin.last _) =
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) := by
  obtain ⟨c⟩ := exists_selectedCoordinate hD
  let B := originalSelectedCount (hD := hD) P
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  let last : Fin B := ⟨B - 1, by dsimp [B]; omega⟩
  have he := originalHorizontalClosure_enumeration_lower_cells P Q v hQ last
  have hlast : (⟨B + last.val, by dsimp [B] at *; omega⟩ :
      Fin (originalSelectedCount (hD := hD) Q)) =
      ⟨originalSelectedCount (hD := hD) Q - 1, by omega⟩ := by
    apply Fin.ext
    dsimp [last, B]
    omega
  rw [hlast] at he
  have hz := originalSelected_minContent_of_translated_cells P Q _ _ 0 v (by
    simpa only [SkewGluing.translate_zero] using he)
  have hv := originalHorizontalClosure_profile_endpoints P Q v hQ
  have hp := c.originalSelected_endpoint_distance P (originalSelectedEnumeration P last)
  have hq := c.originalSelected_endpoint_distance Q
    (originalSelectedEnumeration Q ⟨originalSelectedCount (hD := hD) Q - 1, by omega⟩)
  rw [originalHessenbergDistance_last Q hBQ, originalHessenbergDistance_last P hB]
  unfold originalLastCapDistance
  rw [P.zeta_last, Q.zeta_last]
  dsimp only [last, B] at hp hz
  rw [hv.1] at hz
  simp only [content, Prod.fst_zero, Prod.snd_zero, add_zero, sub_self] at hz
  omega

/-- A gap between consecutive selected components inside either complete copy retains
its actual endpoint distance. -/
theorem originalHorizontalClosure_internal_distance {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (a b : Fin (originalSelectedCount (hD := hD) P)) (hab : a.val + 1 = b.val)
    (upper : Bool) :
    let offset := if upper then 0 else originalSelectedCount (hD := hD) P
    let qa : Fin (originalSelectedCount (hD := hD) Q) :=
      ⟨offset + a.val, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
        dsimp only [offset]
        split <;> omega⟩
    originalHessenbergDistance (hD := hD) Q qa.succ qa.succ =
      originalHessenbergDistance (hD := hD) P a.succ a.succ := by
  obtain ⟨c⟩ := exists_selectedCoordinate hD
  dsimp only
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  cases upper
  · simp only [Bool.false_eq_true, ite_false]
    let qa : Fin (originalSelectedCount (hD := hD) Q) :=
      ⟨originalSelectedCount (hD := hD) P + a.val, by omega⟩
    let qb : Fin (originalSelectedCount (hD := hD) Q) :=
      ⟨originalSelectedCount (hD := hD) P + b.val, by omega⟩
    have ha := originalHorizontalClosure_enumeration_lower_cells P Q v hQ a
    have hb := originalHorizontalClosure_enumeration_lower_cells P Q v hQ b
    have hza := originalSelected_minContent_of_translated_cells P Q
      (originalSelectedEnumeration P a) (originalSelectedEnumeration Q qa) 0 v (by
        simpa only [SkewGluing.translate_zero] using ha)
    have hzb := originalSelected_minContent_of_translated_cells P Q
      (originalSelectedEnumeration P b) (originalSelectedEnumeration Q qb) 0 v (by
        simpa only [SkewGluing.translate_zero] using hb)
    change originalHessenbergDistance (hD := hD) Q qa.succ qa.succ = _
    rw [c.originalHessenbergDistance_between Q qa qb (by dsimp [qa, qb]; omega),
      c.originalHessenbergDistance_between P a b hab]
    dsimp only [qa, qb] at hza hzb ⊢
    omega
  · simp only [ite_true, zero_add]
    let qa : Fin (originalSelectedCount (hD := hD) Q) := ⟨a.val, by omega⟩
    let qb : Fin (originalSelectedCount (hD := hD) Q) := ⟨b.val, by omega⟩
    have ha := originalHorizontalClosure_enumeration_upper_cells P Q v hQ a
    have hb := originalHorizontalClosure_enumeration_upper_cells P Q v hQ b
    have hza := originalSelected_minContent_of_translated_cells P Q
      (originalSelectedEnumeration P a) (originalSelectedEnumeration Q qa) (vH P.cells) v ha
    have hzb := originalSelected_minContent_of_translated_cells P Q
      (originalSelectedEnumeration P b) (originalSelectedEnumeration Q qb) (vH P.cells) v hb
    change originalHessenbergDistance (hD := hD) Q qa.succ qa.succ = _
    rw [c.originalHessenbergDistance_between Q qa qb (by dsimp [qa, qb]; omega),
      c.originalHessenbergDistance_between P a b hab]
    dsimp only [qa, qb] at hza hzb ⊢
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
