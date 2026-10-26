/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowSourceRows

/-!
# Complete original complementary source bands in literal equal windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
The actual ordered source equivalence is produced from literal cell geometry.
It preserves all positions, both endpoint lists, and every empty interior unit pivot.
Boundary proper minors are transported by the whole-block equivalences. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Actual complementary source positions whose endpoints lie strictly inside a window. -/
abbrev OriginalWindowSourceBand {n : ℕ} (P : Profile n) (lo hi : ℤ) :=
  {i : Fin n // lo < P.zeta i.castSucc ∧ P.xi i.succ < hi}

/-- Complete equal windows produce an ordered bijection of their entire strict source bands. -/
theorem originalWindow_source_orderIso {n : ℕ} (P : Profile n) (lo hi q : ℤ)
    (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi)) :
    ∃ e : OriginalWindowSourceBand P lo hi ≃o OriginalWindowSourceBand P (lo + q) (hi + q),
      ∀ i, ((e i).val : ℤ) = (i.val : ℤ) + v.1 ∧
        P.xi (e i).val.succ = P.xi i.val.succ + q ∧
        P.zeta (e i).val.castSucc = P.zeta i.val.castSucc + q := by
  classical
  have hex (i : OriginalWindowSourceBand P lo hi) :
      ∃ j : OriginalWindowSourceBand P (lo + q) (hi + q),
        (j.val : ℤ) = (i.val : ℤ) + v.1 ∧
          P.xi j.val.succ = P.xi i.val.succ + q ∧
          P.zeta j.val.castSucc = P.zeta i.val.castSucc + q := by
    obtain ⟨j, hj, hx, hz⟩ := originalWindow_complementary_position P lo hi q v hv hwindow
      i.val i.property.1 i.property.2
    exact ⟨⟨j, by omega⟩, hj, hx, hz⟩
  let f := fun i => Classical.choose (hex i)
  have hf (i : OriginalWindowSourceBand P lo hi) :
      ((f i).val : ℤ) = (i.val : ℤ) + v.1 ∧
        P.xi (f i).val.succ = P.xi i.val.succ + q ∧
        P.zeta (f i).val.castSucc = P.zeta i.val.castSucc + q :=
    Classical.choose_spec (hex i)
  have hinj : Function.Injective f := by
    intro i j he
    have hfi := (hf i).1
    have hfj := (hf j).1
    have hev := congrArg (fun x : OriginalWindowSourceBand P (lo + q) (hi + q) => x.val) he
    rw [hev] at hfi
    apply Subtype.ext
    apply Fin.ext
    omega
  have hrev : P.cells.filter (fun x => lo ≤ content x ∧ content x < hi) =
      translate (-v) (P.cells.filter fun x => lo + q ≤ content x ∧ content x < hi + q) := by
    rw [hwindow, SkewGluing.translate_translate, neg_add_cancel, SkewGluing.translate_zero]
  have hv' : content (-v) = -q := by
    change -v.2 - -v.1 = -q
    unfold content at hv
    omega
  have hrev' : P.cells.filter
      (fun x => lo + q + -q ≤ content x ∧ content x < hi + q + -q) =
      translate (-v) (P.cells.filter fun x => lo + q ≤ content x ∧ content x < hi + q) := by
    simpa only [add_neg_cancel_right] using hrev
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hipos, hx, hz⟩ := originalWindow_complementary_position P (lo + q) (hi + q)
      (-q) (-v) hv' hrev' j.val j.property.1 j.property.2
    have hib : lo < P.zeta i.castSucc ∧ P.xi i.succ < hi := by omega
    let a : OriginalWindowSourceBand P lo hi := ⟨i, hib⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    have ha := (hf a).1
    change (i : ℤ) = (j.val : ℤ) + -v.1 at hipos
    change ((f a).val : ℤ) = (i : ℤ) + v.1 at ha
    omega
  have hmono : StrictMono f := by
    intro i j hij
    have hi := (hf i).1
    have hj := (hf j).1
    change i.val.val < j.val.val at hij
    change (f i).val.val < (f j).val.val
    omega
  refine ⟨{
    toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
    map_rel_iff' := fun {i j} => hmono.le_iff_le }, ?_⟩
  exact hf

end SkewCornerDescent.Matrix
