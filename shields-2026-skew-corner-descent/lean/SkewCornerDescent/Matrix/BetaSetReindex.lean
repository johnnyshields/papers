/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.BlockResponseLocality
import SkewCornerDescent.Matrix.UnitVertexGeometry

/-!
# Complete original beta matrices from recovered endpoint sets

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Equal
literal row and column sets produce independent row and column bijections.
The complete boundary contraction is then identical, including every coupling
and every inverse entry. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Equal finite injective coordinate sets produce a matching index equivalence. -/
theorem equiv_of_equal_beta_sets {ν κ : Type*} [Fintype ν] [Fintype κ]
    (left : ν → ℤ) (right : κ → ℤ)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hsets : Finset.univ.image left = Finset.univ.image right) :
    ∃ e : κ ≃ ν, ∀ i, left (e i) = right i := by
  classical
  have hex (i : κ) : ∃ j, left j = right i := by
    have hi : right i ∈ Finset.univ.image right :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [← hsets] at hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj⟩
  let f : κ → ν := fun i => Classical.choose (hex i)
  have hf (i) : left (f i) = right i := Classical.choose_spec (hex i)
  have hinj : Function.Injective f := by
    intro i j he
    apply hright
    rw [← hf i, ← hf j, he]
  have hsurj : Function.Surjective f := by
    intro j
    have hj : left j ∈ Finset.univ.image left :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rw [hsets] at hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    exact ⟨i, hleft ((hf i).trans hi)⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- Equal complete original beta sets identify the same full boundary
contraction. Row and column indices are allowed to be paired differently. -/
theorem beta_contraction_eq_of_sets {ν κ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ] [CommRing F]
    (ι : Lambda →+* F) (row col : ν → ℤ) (row' col' : κ → ℤ)
    (hrow : Function.Injective row) (hcol : Function.Injective col)
    (hrow' : Function.Injective row') (hcol' : Function.Injective col')
    (hrows : Finset.univ.image row = Finset.univ.image row')
    (hcols : Finset.univ.image col = Finset.univ.image col') (x y : ℤ) :
    inverseContraction (fun i => ι (hh (x - col i))) (fun i => ι (hh (row i - y)))
        (vertexBetaMatrix ι row col) =
      inverseContraction (fun i => ι (hh (x - col' i))) (fun i => ι (hh (row' i - y)))
        (vertexBetaMatrix ι row' col') := by
  obtain ⟨er, her⟩ := equiv_of_equal_beta_sets row row' hrow hrow' hrows
  obtain ⟨ec, hec⟩ := equiv_of_equal_beta_sets col col' hcol hcol' hcols
  have hM : vertexBetaMatrix ι row' col' = (vertexBetaMatrix ι row col).submatrix er ec := by
    ext i j
    change ι (hh (row' i - col' j)) = ι (hh (row (er i) - col (ec j)))
    rw [her, hec]
  have hr : ((fun i => ι (hh (x - col i))) ∘ ec) = fun i => ι (hh (x - col' i)) := by
    funext i
    dsimp only [Function.comp_apply]
    rw [hec]
  have hc : ((fun i => ι (hh (row i - y))) ∘ er) = fun i => ι (hh (row' i - y)) := by
    funext i
    dsimp only [Function.comp_apply]
    rw [her]
  rw [hM, ← hr, ← hc, inverseContraction_equiv_rows_cols]

end SkewCornerDescent.Matrix
