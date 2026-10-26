/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowCapNormalization
import SkewCornerDescent.Matrix.OriginalClosureQuotient

/-!
# Exact original residue dependence in the monic closure coordinate

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`). The
actual closure quotient retains its produced orientation sign. Polynomial composition
absorbs that sign into the rational parameter without assuming an unsigned quotient
identity. Literal windows produce the cap and internal-product normalization.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance windowDependenceRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact dependence on the actual closure quotient gives exact dependence on its monic
central response coordinate. The fixed determinant sign is absorbed by composition. -/
theorem originalHorizontalClosure_monic_dependence {n m : ℕ}
    (P : Profile n) (H : Profile m) (h : ℤ × ℤ)
    (hH : originalHorizontalClosure P = translate h H.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (y : OtherField c.top) (p q : Polynomial ℚ) (hpq : IsCoprime p q)
    (hdep : y = Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p /
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) q) :
    let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H h hH]; omega⟩
    ∃ p' q' : Polynomial ℚ, IsCoprime p' q' ∧
      y = Polynomial.aeval (c.regularResidue (c.originalHessenbergResponse H middle middle) /
          c.originalTrueCapProduct P) p' /
        Polynomial.aeval (c.regularResidue (c.originalHessenbergResponse H middle middle) /
          c.originalTrueCapProduct P) q' := by
  dsimp only
  obtain ⟨ε, _, he⟩ := c.originalHorizontalClosure_residue_quotient P H h hH hB hmax
  let s : Polynomial ℚ := Polynomial.C (ε : ℚ) * Polynomial.X
  refine ⟨p.comp s, q.comp s, hpq.map (Polynomial.compRingHom s), ?_⟩
  rw [Polynomial.aeval_comp, Polynomial.aeval_comp]
  simpa only [s, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_intCast,
    Int.cast_id, mul_div_assoc, he] using hdep

/-- Literal source and overlap profiles, their actual closure, and the standing original
residue equation produce the normalized polynomial dependence needed by the classifier.
Neither cap correspondence nor a plane-coordinate equality is a hypothesis. -/
theorem originalWindow_residue_dependence {n k m : ℕ}
    (P : Profile n) (W : Profile k) (H : Profile m) (q : ℤ) (v z h : ℤ × ℤ)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hH : originalHorizontalClosure P = translate h H.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hQ : ∀ C ∈ edgeComponents (diagramInterior W.cells), span C ≤ (c.top : ℕ))
    (b a d : ℕ) (hd : d + a = b)
    (hcorner : (jtMatrix (fun j : Fin n => P.xi j.succ)
          (fun j => P.zeta j.castSucc)).det ^ a =
      (jtMatrix (fun j : Fin k => W.xi j.succ)
          (fun j => W.zeta j.castSucc)).det ^ b)
    (p t : Polynomial ℚ) (hpt : IsCoprime p t)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) t) :
    let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H h hH]; omega⟩
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∃ p' t' : Polynomial ℚ, IsCoprime p' t' ∧
      (ε : OtherField c.top) * (∏ i, c.originalInternalResidue P i) ^ a /
          ((∏ i, c.originalInternalResidue W i) ^ b * c.originalTrueCapProduct P ^ d) =
        Polynomial.aeval (c.regularResidue (c.originalHessenbergResponse H middle middle) /
          c.originalTrueCapProduct P) p' /
        Polynomial.aeval (c.regularResidue (c.originalHessenbergResponse H middle middle) /
          c.originalTrueCapProduct P) t' := by
  dsimp only
  obtain ⟨hB, _⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW hcutq hcutLq hC
  obtain ⟨ε, hε, hr⟩ := c.originalWindow_cap_normalized_ratio P W q v z hwindow hW
    hcutq hcutLq hC hP hQ b a d hd hcorner
  obtain ⟨p', t', hcop, he⟩ := c.originalHorizontalClosure_monic_dependence P H h hH hB hP
    _ p t hpt hdep
  exact ⟨ε, hε, p', t', hcop, hr.symm.trans he⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
