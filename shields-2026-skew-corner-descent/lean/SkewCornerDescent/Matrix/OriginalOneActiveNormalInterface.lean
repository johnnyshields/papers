/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOneActiveDefectDetection
import SkewCornerDescent.Matrix.OriginalClosureLiteralRoot

/-!
# Complete actual one-active normal interface

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
Complete supplied rational matching, genuine ordinary closures and the
actual response/gap nullspace give bounded original-defect detection or
a proper literal empty row/column root of the whole parent. The full
phase energy and root suppliers are invoked; overlap selected positivity
and the two-state bound are derived from the original corner powers
and standing outer-count regime. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance oneActiveNormalInterfaceRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The whole actual one-active chart has a bounded positive original
defect coefficient or a proper literal empty b-copy line-outer root. -/
theorem originalOneActive_normal_interface {n m s t on : ℕ}
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
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b)
    (hrpos : 0 < r) (hr : primeOrder (cellSchur D hD.1) Λ = r)
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
      c.originalInternalResidue O center = active.val)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active.val)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hcoprime : Nat.Coprime a b) (hb : 3 ≤ b)
    (δ : ℤ) (hspan : P.xi 0 = (b : ℤ) * δ) :
    (∃ j : ℕ, 0 < j ∧ j ≤ (b-a)*r ∧ j < originalSelectedCount (hD := hD) P ∧
      PowerSeries.coeff j (c.originalDeterminantDefect P A H a b p₀ p₁) ≠ 0) ∨
    (∃ E : Diagram, IsConnectedSkew E ∧ span E = δ.toNat ∧
      (emptyMarkH E).IsLegal ∧ 2 ≤ E.card ∧
      (∃ x ∈ E, ∃ y ∈ E, x.1 ≠ y.1 ∧ x.2 ≠ y.2) ∧
      2 ≤ (horizontalRow b).card ∧ 2 ≤ (verticalColumn b).card ∧
      (P.cells = (emptyMarkH E).compose (horizontalRow b) ∨
        P.cells = (emptyMarkH E).compose (verticalColumn b))) := by
  classical
  let : NeZero b := ⟨by omega⟩
  let : NeZero r := ⟨ne_of_gt hrpos⟩
  have hcountW : originalSelectedCount (hD := hD) W = a*r := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos ha hrpos
  have hab' : a < b := by omega
  have hd : 2 ≤ b-a := by omega
  have hn : 2 ≤ (b-a)*r := by
    have hm := Nat.mul_le_mul_right r hd
    omega
  obtain ⟨hcountP, hCQ, hshort, hdata⟩ := c.originalOneActive_normal_defect_detection
    P W A H O q v u z w zO hq hv hwindow hW hA hH hO hcutq hcutLq hC hmax Λ b a r
    ha hab' hrpos hr hKU hKW p₀ p₁ hpq hdep active hother hactive hresponse hgap hn
  rcases hdata with hp | ⟨j, hj, hjn, hjD⟩
  · apply Or.inr
    have hc : Nat.Coprime (b-a) b := (Nat.coprime_self_sub_left hab'.le).mpr hcoprime
    obtain ⟨_, hroot⟩ := c.originalClosure_no_discrepancy_literal_root P O zO hO active.val
      b r (b-a) hc hb hcountP hresponse hgap hmax δ hspan
    exact hroot hactive hp
  · exact Or.inl ⟨j, hj, hjn, hjn.trans_lt hshort, hjD⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
