/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowActiveClasses

/-!
# Balanced true-end response aliases

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`).
The actual closure top lies strictly above both true cap tops. Consequently
all internal occurrences equal to either full true-end function have balanced
multiplicities in the complete source and overlap window. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance endClassRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both actual true-end classes have balanced internal counts, including coincident
caps and any internal aliases. No disjointness of full response functions is assumed. -/
theorem originalWindow_end_classes_balanced {n k m : ℕ}
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
    (Λ : Lambda) (b a d : ℕ) (hd : d + a = b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin k => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p t : Polynomial ℚ) (hpt : IsCoprime p t)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) t) :
    ∀ j : Fin (originalSelectedCount (hD := hD) P + 1),
      j = 0 ∨ j = Fin.last _ →
      a * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse P j j) =
            c.originalInternalResidue P i).card =
        b * (Finset.univ.filter fun i =>
          c.regularResidue (c.originalHessenbergResponse P j j) =
            c.originalInternalResidue W i).card := by
  classical
  obtain ⟨hB, _⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW hcutq hcutLq hC
  obtain ⟨_, hactive⟩ := (c.originalWindow_active_classes P W H q v z h
    hwindow hW hH hcutq hcutLq hC hP hQ Λ b a d hd hKU hKW p t hpt hdep).1
  have hcentral := c.originalHorizontalClosure_central_distance P H h hH hB
  dsimp only at hcentral
  rw [c.originalCompletedGap_last_eq_splice P hB,
    c.originalCapSpliceDistance_cap_sum, ← originalHessenbergDistance_first P hB,
    ← originalHessenbergDistance_last P hB] at hcentral
  have hf := c.originalHessenbergDistance_gt_top P hB 0 0 le_rfl
  have hl := c.originalHessenbergDistance_gt_top P hB (Fin.last _) (Fin.last _) le_rfl
  have htop := c.top.property
  intro j hj
  by_contra hne
  have he := (hactive j hne).1
  rcases hj with rfl | rfl <;> omega

end SkewCornerDescent.Matrix.SelectedCoordinate
