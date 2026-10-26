/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOneActiveDefectDetection
import SkewCornerDescent.Matrix.OriginalClosurePhaseLiteral

/-!
# Original defect detection or complete interval copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual supplied defect is detected by the normal bound, or coprime
occurrence phases give full paired original interval copies. The latter
retains every original row and column, not only a scalar response.
Whole-parent cell tiling is not asserted here. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance oneActiveIntervalAlternativeRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact supplied matching gives bounded original-defect detection or
complete literal paired intervals in every occurrence phase. -/
theorem originalOneActive_literal_interval_or_defect {n m s t on : ℕ}
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
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a < b)
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
    (hn : 2 ≤ (b-a)*r) (hcoprime : Nat.Coprime a b) :
    ∃ hcountP : originalSelectedCount (hD := hD) P = b*r,
    ∃ hCQ : originalSelectedCount (hD := hD) O = 2 * originalSelectedCount (hD := hD) P,
    letI : NeZero b := ⟨by omega⟩
    letI : NeZero r := ⟨ne_of_gt hrpos⟩
    (b-a)*r < originalSelectedCount (hD := hD) P ∧
      ((∀ (i : Fin r) (k l : ZMod b), originalInternalLiteralCopy O
        (originalClosurePhaseStateIndex P O b r hcountP hCQ i k)
        (originalClosurePhaseStateIndex P O b r hcountP hCQ i l)) ∨
        ∃ j : ℕ, 0 < j ∧ j ≤ (b-a)*r ∧
          PowerSeries.coeff j (c.originalDeterminantDefect P A H a b p₀ p₁) ≠ 0) := by
  classical
  let : NeZero b := ⟨by omega⟩
  let : NeZero r := ⟨ne_of_gt hrpos⟩
  obtain ⟨hcountP, hCQ, hshort, hdata⟩ := c.originalOneActive_normal_defect_detection
    P W A H O q v u z w zO hq hv hwindow hW hA hH hO hcutq hcutLq hC hmax Λ b a r
    ha hab hrpos hr hKU hKW p₀ p₁ hpq hdep active hother hactive hresponse hgap hn
  refine ⟨hcountP, hCQ, hshort, ?_⟩
  rcases hdata with hperiod | hdetect
  · apply Or.inl
    have hc : Nat.Coprime (b-a) b := (Nat.coprime_self_sub_left hab.le).mpr hcoprime
    obtain ⟨hCQ', hcopy⟩ := c.originalClosure_phase_literal_intervals P O zO hO active.val
      b r (b-a) hc hcountP hresponse hgap hmax
    exact hcopy hactive hperiod
  · exact Or.inr hdetect

end SkewCornerDescent.Matrix.SelectedCoordinate
