/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowSourceEquiv
import SkewCornerDescent.Matrix.OriginalWindowRemovedBlocks

/-!
# Literal empty blocks in complete windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). An empty interior
row is a canonical one-position block. It remains in the full removed inverse as its
actual unit pivot, and its two original endpoints translate together. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The two extreme source positions of a genuine empty block are the row itself. -/
theorem interior_empty_block_extremes {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.xi i.succ = P.zeta i.castSucc) :
    interiorBlockFirst P i = i ∧ interiorBlockLast P i = i := by
  exact ⟨interior_empty_row_isolated P i hi _
    ((mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)),
    interior_empty_row_isolated P i hi _
      ((mem_interiorBlockFiber P i _).mp (interiorBlockLast_mem P i))⟩

/-- Empty original blocks have one source position, not a discarded empty matrix. -/
theorem interior_empty_block_length {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.xi i.succ = P.zeta i.castSucc) : interiorBlockLength P i = 0 := by
  obtain ⟨hf, hl⟩ := interior_empty_block_extremes P i hi
  simp only [interiorBlockLength, hf, hl, Nat.sub_self]

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The actual selected prime never removes the empty block's unit pivot. -/
theorem originalEmptyBlock_remaining_size {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hb : P.xi b.val.succ = P.zeta b.val.castSucc) :
    originalRemovedSize (hD := hD) P b = 1 := by
  have hn : ¬ originalBlockSelected (hD := hD) P b :=
    not_dvd_originalEmptyBlock (hD := hD) P b.val hb
  simp only [originalRemovedSize, ite_eq_right hn, interior_empty_block_length P b.val hb]

/-- Every retained index of the empty block has the genuine original row and column. -/
theorem originalEmptyBlock_remaining_endpoints {n : ℕ} (P : Profile n)
    (b : OriginalBlocks P) (hb : P.xi b.val.succ = P.zeta b.val.castSucc)
    (k : Fin (originalRemovedSize (hD := hD) P b)) :
    P.xi (originalRemovedRow (hD := hD) P b k).succ = P.xi b.val.succ ∧
    P.zeta (originalRemovedCol (hD := hD) P b k).castSucc = P.zeta b.val.castSucc := by
  have hr := interior_empty_row_isolated P b.val hb _
    (originalRemovedRow_block (hD := hD) P b k)
  have hc := interior_empty_row_isolated P b.val hb _
    (originalRemovedCol_block (hD := hD) P b k)
  rw [hr, hc]
  exact ⟨rfl, rfl⟩

/-- Literal empty-block matching preserves the entire retained endpoint list. -/
theorem originalEmptyBlock_translated_endpoints {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.xi b.val.succ = P.zeta b.val.castSucc)
    (hd : Q.xi d.val.succ = Q.zeta d.val.castSucc) (q : ℤ)
    (hx : Q.xi d.val.succ = P.xi b.val.succ + q)
    (hz : Q.zeta d.val.castSucc = P.zeta b.val.castSucc + q) :
    ∃ e : Fin (originalRemovedSize (hD := hD) P b) ≃
        Fin (originalRemovedSize (hD := hD) Q d),
      ∀ k, Q.xi (originalRemovedRow (hD := hD) Q d (e k)).succ =
          P.xi (originalRemovedRow (hD := hD) P b k).succ + q ∧
        Q.zeta (originalRemovedCol (hD := hD) Q d (e k)).castSucc =
          P.zeta (originalRemovedCol (hD := hD) P b k).castSucc + q := by
  let e := (Fin.castOrderIso ((originalEmptyBlock_remaining_size (hD := hD) P b hb).trans
    (originalEmptyBlock_remaining_size (hD := hD) Q d hd).symm)).toEquiv
  refine ⟨e, fun k => ?_⟩
  obtain ⟨hr, hc⟩ := originalEmptyBlock_remaining_endpoints (hD := hD) P b hb k
  obtain ⟨hr', hc'⟩ := originalEmptyBlock_remaining_endpoints (hD := hD) Q d hd (e k)
  exact ⟨hr'.trans (hx.trans (congrArg (fun x => x + q) hr.symm)),
    hc'.trans (hz.trans (congrArg (fun x => x + q) hc.symm))⟩

end SelectedCoordinate
end SkewCornerDescent.Matrix
