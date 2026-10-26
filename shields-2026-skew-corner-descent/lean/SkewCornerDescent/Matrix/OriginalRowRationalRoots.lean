/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalActiveRationalRoots
import SkewCornerDescent.Matrix.OriginalWindowRowPencil

/-!
# Actual reduced rational roots of the full row chart

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The two produced label choices agree on each actual active class by nonzero
full cap product. The inverse-projection integer bound therefore applies to
every root of the actual coprime rational pair. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance rowRationalRootsRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full coprime rational pair on the actual all-row source has roots in
one produced signed interval of three consecutive integers, or two at equal
actual cap tops. No root/class correspondence is assumed. -/
theorem originalWindow_row_rational_roots {n m s t : ℕ}
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
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
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
    let limit := if originalHessenbergDistance (hD := hD) P 0 0 =
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) then 1 else 2
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∃ origin : ℕ, origin ≤ limit ∧
      ∀ α : ℚ, p₀.eval α = 0 ∨ p₁.eval α = 0 →
        ∃ k : ℕ, k ≤ limit ∧ α = (δ : ℚ) * ((k : ℚ) - (origin : ℚ)) := by
  classical
  obtain ⟨bounded, origin, horigin, hbounded, _⟩ := c.originalWindow_row_plane_labels
    P W A Q q v u z w hv hwindow hW hA hQ hcutq hcutLq hmax hrows Λ b a r ha hab hrpos hr
      hKU hKW p₀ p₁ hpq hdep
  obtain ⟨δ, hδ, label, hlabels, _, _, hroots⟩ := c.originalWindow_active_rational_roots
    P W A Q q v u z w hv hwindow hW hA hQ hcutq hcutLq hmax Λ b a r ha hab hrpos hr
      hKU hKW p₀ p₁ hpq hdep
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
    exact Nat.mul_pos hrpos (by omega)
  dsimp only at hbounded horigin hlabels hroots ⊢
  refine ⟨δ, hδ, origin, horigin, ?_⟩
  intro α hα
  obtain ⟨X, hX, hαX⟩ := hroots α hα
  obtain ⟨⟨k, hk, hval⟩, hboundedX⟩ := hbounded X hX
  have he := c.original_plane_labels_eq P Q _ hB hmax X (label X) (bounded X)
    (hlabels X hX) hboundedX
  refine ⟨k, hk, ?_⟩
  rw [hαX, he, hval]

end SkewCornerDescent.Matrix.SelectedCoordinate
