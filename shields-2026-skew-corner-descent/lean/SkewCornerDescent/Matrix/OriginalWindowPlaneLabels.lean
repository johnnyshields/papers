/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassActiveLabels

/-!
# Rational plane labels on complete actual signed class counts

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Complete cofactor powers and literal windows turn the reduced cyclic class
labels into labels of the original signed occurrence counts. No count or
response equality is carried as an additional premise. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory

noncomputable local instance rawPlaneRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original signed active classes have produced rational plane labels
and distinct active labels, without imposing any row or column restriction. -/
theorem originalWindow_plane_labels {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (r * (b - a))]
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∃ label : c.OriginalResponseClass P → ℚ,
      (∀ X, c.originalResponseClassExponent P W a b X ≠ 0 →
        X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
          (label X : OtherField c.top) * c.originalTrueCapProduct P) ∧
      (∀ X Y, c.originalResponseClassExponent P W a b X ≠ 0 →
        c.originalResponseClassExponent P W a b Y ≠ 0 → label X = label Y → X = Y) := by
  classical
  obtain ⟨_, _, _, _, k, s, hk, hs, _, hbshape, capacity, label,
      hlabels, hinj, _, _⟩ :=
    c.originalWindow_responseClass_active_labels P W A Q q v u z w hv hwindow hW hA hQ
      hcutq hcutLq hmax Λ b a r ha hab hrpos hr hKU hKW p₀ p₁ hpq hdep
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  obtain ⟨_, hcounts, _⟩ := c.originalWindow_responseClass_defects P W q z v hv hW.symm
    hwindow hcutq hcutLq hC r (b - a) s k b a hrpos hs hk hbshape (by omega) hcountP hcountW
  have heq : c.originalResponseClassExponent P W a b =
      classDefect (c.originalResponseClassWord P (r * (b - a)) capacity) 1 (b - a) s
        (r * s - 1) 0 := by
    funext X
    exact hcounts X
  dsimp only at hlabels hinj ⊢
  refine ⟨label, ?_, ?_⟩
  · intro X hX
    exact (hlabels X (by rwa [← heq])).2
  · intro X Y hX hY hl
    exact hinj X Y (by rwa [← heq]) (by rwa [← heq]) hl

end SkewCornerDescent.Matrix.SelectedCoordinate
