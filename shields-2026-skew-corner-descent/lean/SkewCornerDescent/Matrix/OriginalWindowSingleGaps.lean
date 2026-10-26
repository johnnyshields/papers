/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowActiveClasses

/-!
# Constant completed gaps in a single actual residue window

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`).
Coprimality excludes balanced internal classes when the selected prime occurs once
in the common corner base. The original dependence equation then fixes every
completed gap, including the true cap splice. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance singleGapRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At selected multiplicity one, the complete actual source gap cycle is constant.
All active-class and cap-top premises are produced from the original residue equation. -/
theorem originalWindow_single_completed_gaps {n k m : ℕ}
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
    (Λ : Lambda) (b a d : ℕ) (hd : d + a = b) (hcop : b.Coprime a)
    (hr : primeOrder (cellSchur D hD.1) Λ = 1)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin k => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p t : Polynomial ℚ) (hpt : IsCoprime p t)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) t) :
    ∃ Δ : ℤ, 0 < Δ ∧
      (∀ j, c.originalCompletedGap P j = Δ) ∧
      P.xi 0 - P.zeta (Fin.last n) = (b : ℤ) * Δ := by
  classical
  obtain ⟨hB, _⟩ := c.originalWindow_true_cap_product P W q v z hwindow hW hcutq hcutLq hC
  have hcount : originalSelectedCount (hD := hD) P = b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, mul_one]
  obtain ⟨label, hactive⟩ := (c.originalWindow_active_classes P W H q v z h
    hwindow hW hH hcutq hcutLq hC hP hQ Λ b a d hd hKU hKW p t hpt hdep).1
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  let Δ := c.originalCompletedGap P last
  have hcentral := c.originalHorizontalClosure_central_distance P H h hH hB
  dsimp only at hcentral
  have hall (j : Fin (originalSelectedCount (hD := hD) P)) :
      c.originalCompletedGap P j = Δ := by
    by_cases hj : j.val + 1 = originalSelectedCount (hD := hD) P
    · have he : j = last := by apply Fin.ext; dsimp only [last]; omega
      rw [he]
    · let i : Fin (originalSelectedCount (hD := hD) P - 1) := ⟨j.val, by omega⟩
      let U := Finset.univ.filter fun l =>
        c.regularResidue (c.originalHessenbergResponse P j.succ j.succ) =
          c.originalInternalResidue P l
      let V := Finset.univ.filter fun l =>
        c.regularResidue (c.originalHessenbergResponse P j.succ j.succ) =
          c.originalInternalResidue W l
      have hpos : 0 < U.card := by
        apply Finset.card_pos.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        rfl
      have hlt : U.card < b := by
        have hle := Finset.card_filter_le (s := (Finset.univ :
          Finset (Fin (originalSelectedCount (hD := hD) P - 1))))
          (fun l => c.regularResidue (c.originalHessenbergResponse P j.succ j.succ) =
            c.originalInternalResidue P l)
        simp only [Finset.card_univ, Fintype.card_fin] at hle
        dsimp only [U]
        omega
      have hne : a * U.card ≠ b * V.card := by
        intro he
        have hdvd : b ∣ a * U.card := by rw [he]; exact dvd_mul_right _ _
        have hz := Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_left hdvd) hlt
        omega
      have ht := (hactive j.succ hne).1
      have hgap : c.originalCompletedGap P j =
          originalHessenbergDistance (hD := hD) P j.succ j.succ - (c.top : ℤ) := by
        simp only [originalCompletedGap, hj, ite_false]
      rw [hgap]
      dsimp only [Δ, last] at ⊢
      omega
  refine ⟨Δ, c.originalCompletedGap_pos P hB last, hall, ?_⟩
  have hs := c.originalCompletedGap_sum P hB
  simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hcount] at hs
  exact hs.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
