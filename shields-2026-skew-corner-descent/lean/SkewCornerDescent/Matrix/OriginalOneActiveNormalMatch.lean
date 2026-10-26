/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOneActiveRationalSeries
import SkewCornerDescent.Matrix.OriginalWindowGeometricResidue
import SkewCornerDescent.Matrix.NormalRationalResidueMatch

/-!
# Produced ordinary normalization of the supplied rational series

Supports `shields-2026-skew-corner-descent.tex` (`eq:residue-match`,
`eq:original-defect`, `lem:original-transfer`). The literal common core and
exact supplied rational representation give the normalization used by the
actual ordinary comparison logarithm. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance oneActiveNormalMatchRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual shared-core cross identity produces the ordinary residue
normalization for the supplied rational series; no defect match is assumed. -/
theorem originalOneActive_normal_match {n m s t on : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t) (O : Profile on)
    (q : ℤ) (v u z w zO : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hO : originalHorizontalClosure P = translate zO O.cells ∨
      originalVerticalClosure P = translate zO O.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a : ℕ) (hab : a < b)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : c.OriginalResponseClass P)
    (hother : ∀ X, X ≠ active → c.originalResponseClassExponent P W a b X = 0)
    (hactive : let center : Fin (originalSelectedCount (hD := hD) O - 1) :=
        ⟨originalSelectedCount (hD := hD) P - 1, by
          rw [originalOrdinaryClosure_selected_count P O zO hO]
          have := NeZero.pos (originalSelectedCount (hD := hD) P)
          omega⟩
      c.originalInternalResidue O center = active.val) :
    ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
      c.originalRationalFunctionSeries P H p₀ p₁ =
        PowerSeries.C (κ : OtherField c.top) *
          (c.normalPolynomialSeries O.schur * (c.normalPolynomialSeries P.schur)⁻¹^2)^(b-a) ∧
      (PowerSeries.constantCoeff (c.normalPolynomialSeries A.schur))^b =
        (κ : OtherField c.top) *
          (PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur))^a *
          (PowerSeries.constantCoeff (c.normalPolynomialSeries O.schur))^(b-a) ∧
      PowerSeries.constantCoeff (c.originalRationalFunctionSeries P H p₀ p₁) ≠ 0 := by
  classical
  obtain ⟨κ, hκ, hseries, hpower, hρ⟩ := c.originalOneActive_supplied_series_power
    P W A H O q v u z w zO hv hwindow hW hA hH hO hcutq hcutLq hC hmax Λ b a hab
    hKU hKW p₀ p₁ hpq hdep active hother hactive
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hf := c.originalSchur_residue_ne_zero P hB hmax
  have hqtop : q < P.xi 0 := by
    let x := ((s : ℤ), W.zeta (Fin.last s) + s)
    have hx : x ∈ W.cells := W.row_left_mem_cells (Fin.last s)
    have hy : x + z ∈ P.cells.filter
        (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
      rw [← hW]
      apply mem_translate.mpr
      simpa only [add_sub_cancel_right] using hx
    have hb := (Finset.mem_filter.mp hy).2
    omega
  have hcross := c.originalWindow_residue_cross_identity P W A q v u z hq hqtop hv
    hwindow hW hA hC
  have hw : c.residueMap W.schur ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcross
    exact pow_ne_zero 2 hf hcross.symm
  have hdegree : (∑ i ∈ ({()} : Finset Unit), (fun _ : Unit => ((b-a : ℕ) : ℤ)) i) =
      (b : ℤ) - a := by simp only [Finset.sum_singleton]; omega
  have hprod : c.residueMap P.schur^a / c.residueMap W.schur^b =
      (κ : OtherField c.top) * ∏ i ∈ ({()} : Finset Unit),
        (c.residueMap O.schur / c.residueMap P.schur^2 -
          (fun _ : Unit => (0 : OtherField c.top)) i)^((b-a : ℕ) : ℤ) := by
    simpa only [Finset.prod_singleton, sub_zero, zpow_natCast] using hpower
  have hm := rationalDefect_residue_match (c.residueMap P.schur) (c.residueMap A.schur)
    (c.residueMap W.schur) (c.residueMap O.schur) (κ : OtherField c.top)
    ({()} : Finset Unit) (fun _ => 0) (fun _ => ((b-a : ℕ) : ℤ)) a b hf hw hcross hdegree hprod
  refine ⟨κ, hκ, hseries, ?_, hρ⟩
  simpa only [Finset.prod_singleton, zero_mul, sub_zero, zpow_natCast,
    c.normalPolynomialSeries_constant] using hm

end SkewCornerDescent.Matrix.SelectedCoordinate
