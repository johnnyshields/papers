/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOneActiveNormalMatch
import SkewCornerDescent.Matrix.OriginalNormalLogDetection
import SkewCornerDescent.Matrix.OrdinaryMonomialFactorization
import SkewCornerDescent.Matrix.OriginalTransfer

/-!
# Bounded detection of the supplied original one-active defect

Formalizes the detection branch of `shields-2026-skew-corner-descent.tex`,
`prop:normal-interface`. The supplied rational series and its ordinary
normalization are produced from actual geometry. The complete original defect
is detected at a positive order no larger than the normal bound unless every
shifted incoming profile agrees. Whole cell-root construction is separate.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance oneActiveDefectDetectionRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual phase energy detects the complete supplied original defect,
with no monomial representation or normalized matching premise. -/
theorem originalOneActive_normal_defect_detection {n m s t on : ℕ}
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
    (hn : 2 ≤ (b-a)*r) :
    ∃ hcountP : originalSelectedCount (hD := hD) P = b*r,
    ∃ hCQ : originalSelectedCount (hD := hD) O = 2 * originalSelectedCount (hD := hD) P,
    letI : NeZero b := ⟨by omega⟩
    letI : NeZero r := ⟨ne_of_gt hrpos⟩
    let C := finiteWordCycle (c.originalInternalEndpointProfiles O)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) O - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    let incoming := fun (i : Fin r) (k : ZMod b) =>
      (C (ZMod.ringEquivCongr hcountP.symm (phaseCycleEquiv b r (i,k)))).1
    (b-a)*r < originalSelectedCount (hD := hD) P ∧
      ((∀ i k, incoming i k = incoming i (k + ((b-a : ℕ) : ZMod b))) ∨
        ∃ j : ℕ, 0 < j ∧ j ≤ (b-a)*r ∧
          PowerSeries.coeff j (c.originalDeterminantDefect P A H a b p₀ p₁) ≠ 0) := by
  classical
  obtain ⟨κ, hκ, hseries, hmatch, hρ⟩ := c.originalOneActive_normal_match
    P W A H O q v u z w zO hq hv hwindow hW hA hH hO hcutq hcutLq hC hmax Λ b a hab
    hKU hKW p₀ p₁ hpq hdep active hother hactive
  obtain ⟨hcountP, hCQ, hdata⟩ := c.originalCompleted_normal_log_detection P W A O
    q z v u zO hq hv hW.symm hwindow hA hO hcutq hcutLq Λ b a r ha hab hrpos hr
    hKU hKW active.val hresponse hgap hmax hn (κ : OtherField c.top)
      (by simpa only [mul_assoc] using hmatch)
  have hd := hdata hactive
  refine ⟨hcountP, hCQ, ?_⟩
  dsimp only at hd ⊢
  refine ⟨hd.1, ?_⟩
  rcases hd.2 with hperiod | ⟨j, hj, hjn, hjlog⟩
  · exact Or.inl hperiod
  · apply Or.inr
    have hf : PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur) ≠ 0 := by
      simpa only [c.normalPolynomialSeries_constant] using
        c.originalSchur_residue_ne_zero P (NeZero.pos _) hmax
    have hmaxO : ∀ X ∈ edgeComponents (diagramInterior O.cells), span X ≤ (c.top : ℕ) := by
      rcases hO with hhor | hver
      · exact c.originalHorizontalClosure_profile_component_span P O zO hhor hmax
      · exact c.originalVerticalClosure_profile_component_span P O zO hver hmax
    have hOunit : PowerSeries.constantCoeff (c.normalPolynomialSeries O.schur) ≠ 0 := by
      simp only [c.normalPolynomialSeries_constant]
      apply c.originalSchur_residue_ne_zero O
      · rw [hCQ]
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega
      · exact hmaxO
    have hκne : (κ : OtherField c.top) ≠ 0 := by rcases hκ with rfl | rfl <;> norm_num
    let : Algebra ℚ (OtherField c.top) := DivisionRing.toRatAlgebra
    obtain ⟨l, hl, hlj, hlD⟩ := ordinaryMonomialDefect_detection
      (c.normalPolynomialSeries A.schur) (c.normalPolynomialSeries P.schur)
      (c.normalPolynomialSeries O.schur) (κ : OtherField c.top) a b j hab.le hf hOunit
      hκne hmatch hjlog
    refine ⟨l, hl, hlj.trans hjn, ?_⟩
    simpa only [originalDeterminantDefect, hseries] using hlD

end SkewCornerDescent.Matrix.SelectedCoordinate
