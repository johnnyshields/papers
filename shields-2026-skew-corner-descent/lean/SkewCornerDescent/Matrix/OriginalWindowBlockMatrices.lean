/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowBlockRows

/-!
# Complete original matrix transport for literal nonempty block occurrences

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
The equivalence enumerates every row of the actual block, not a representative
or a polynomial label. Both full endpoint lists and the whole matrix are retained.
Empty unit blocks require their separate source-row placement. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Whole translated block occurrences have exactly the same number of original rows. -/
theorem interiorBlockCells_translated_length {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : Fin n) (d : Fin m) (hb : P.zeta b.castSucc < P.xi b.succ)
    (hd : Q.zeta d.castSucc < Q.xi d.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b) = interiorBlockCells Q d) :
    interiorBlockLength P b = interiorBlockLength Q d := by
  have h := interiorBlockCells_translated_row_extremes P Q b d hb hd v he
  unfold interiorBlockLength
  omega

/-- The complete original row positions of two literal block occurrences are matched. -/
noncomputable def originalTranslatedBlockIndexEquiv {n m : ℕ} (P : Profile n)
    (Q : Profile m) (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val) :
    Fin (interiorBlockLength P b.val + 1) ≃ Fin (interiorBlockLength Q d.val + 1) :=
  (Fin.castOrderIso (congrArg (fun k : ℕ => k + 1)
    (interiorBlockCells_translated_length P Q b.val d.val hb hd v he))).toEquiv

/-- Every full original row and column endpoint is shifted by the actual content displacement. -/
theorem originalTranslatedBlockIndex_endpoints {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val)
    (k : Fin (interiorBlockLength P b.val + 1)) :
    let e := originalTranslatedBlockIndexEquiv P Q b d hb hd v he
    let i := originalBlockIndex P ⟨b, k⟩
    let j := originalBlockIndex Q ⟨d, e k⟩
    Q.xi j.succ = P.xi i.succ + content v ∧
      Q.zeta j.castSucc = P.zeta i.castSucc + content v := by
  let e := originalTranslatedBlockIndexEquiv P Q b d hb hd v he
  let i := originalBlockIndex P ⟨b, k⟩
  let j := originalBlockIndex Q ⟨d, e k⟩
  have hf := (interiorBlockCells_translated_row_extremes P Q b.val d.val hb hd v he).1
  have hrow : (j : ℤ) = (i : ℤ) + v.1 := by
    dsimp only [i, j, originalBlockIndex, interiorSliceIndex]
    have hk : (e k).val = k.val := rfl
    simp only [Nat.cast_add, hk]
    omega
  exact interiorBlockCells_translated_row_endpoints P Q b.val i d.val j hb hd
    (originalBlockIndex_label P ⟨b, k⟩) (originalBlockIndex_label Q ⟨d, e k⟩) v hrow he

/-- The entire actual complementary block matrix agrees under the produced occurrence map. -/
theorem originalTranslatedBlock_matrix {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val) :
    let e := originalTranslatedBlockIndexEquiv P Q b d hb hd v he
    (jtMatrix (fun j => Q.xi (originalBlockIndex Q ⟨d, j⟩).succ)
      (fun j => Q.zeta (originalBlockIndex Q ⟨d, j⟩).castSucc)).submatrix e e =
    jtMatrix (fun i => P.xi (originalBlockIndex P ⟨b, i⟩).succ)
      (fun i => P.zeta (originalBlockIndex P ⟨b, i⟩).castSucc) := by
  dsimp only
  apply Matrix.ext
  intro i j
  have hr := (originalTranslatedBlockIndex_endpoints P Q b d hb hd v he i).1
  have hc := (originalTranslatedBlockIndex_endpoints P Q b d hb hd v he j).2
  change hh (_ - _) = hh (_ - _)
  dsimp only
  rw [hr, hc, add_sub_add_right_eq_sub]

end SkewCornerDescent.Matrix
