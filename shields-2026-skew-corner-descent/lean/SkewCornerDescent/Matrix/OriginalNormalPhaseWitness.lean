/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalPhaseCoefficient
import SkewCornerDescent.Matrix.OriginalClosurePhaseDiscrepancy

/-!
# Original ordinary normal coefficient with produced phase data

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`,
`eq:normal-interface`.  Actual completed closure geometry produces all first
discrepancy choices, their positive maximal margin and the protected generator.
The complete ordinary affine coefficient identity then follows for the whole
original Schur ratio, including its full first-normal correction and the
two-state boundary.  The alternative is equality of all shifted full incoming
profiles; detection and literal-root reconstruction are separate conclusions.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual original normal comparison either has identical shifted full
incoming profiles, or produces its first-discrepancy choices, positive maximal
resolving margin, protected generator and complete ordinary coefficient
identity.  No phase choice, half-height bound or resolving margin is assumed. -/
theorem originalCompleted_normal_phase_energy_witness {n m an qn : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an) (Q : Profile qn)
    (q : ℤ) (u v w z : ℤ × ℤ) (hq0 : 0 ≤ q) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate w A.cells)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hn : 2 ≤ (b - a) * r)
    (κ : OtherField c.top)
    (hmatch : (PowerSeries.constantCoeff (c.normalPolynomialSeries A.schur)) ^ b =
      κ * ((PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur)) ^ a *
        (PowerSeries.constantCoeff (c.normalPolynomialSeries Q.schur)) ^ (b - a))) :
    ∃ hcountP : originalSelectedCount (hD := hD) P = b * r,
    ∃ hshort : (b - a) * r < originalSelectedCount (hD := hD) P,
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    letI : NeZero b := ⟨by omega⟩
    letI : NeZero r := ⟨ne_of_gt hrpos⟩
    let d := b - a
    let n := d * r
    let C := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    let incoming := fun (i : Fin r) (k : ZMod b) =>
      (C (ZMod.ringEquivCongr hcountP.symm (phaseCycleEquiv b r (i,k)))).1
    let K := fun i : Fin r => ((c.top : ℤ) + c.originalCompletedGap P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
    let ZP := ∏ i : Fin n, (c.originalInternalResidue P
      ⟨i.val, by have hi : i.val < (b - a) * r := i.isLt; omega⟩)⁻¹
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    (∀ i k, incoming i k = incoming i (k + (d : ZMod b))) ∨
    ∃ choices : Fin r → Option ℕ, ∃ J H : ℕ+,
    ∃ hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ),
    let protectedIndex := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    (∀ i, match choices i with
      | none => ∀ k, incoming i k = incoming i (k + (d : ZMod b))
      | some w => 0 < w ∧ 2 * w < K i ∧
          (∀ k l, l < w → (incoming i k).coeff l =
            (incoming i (k + (d : ZMod b))).coeff l) ∧
          (K i : ℤ) - 2 * (w : ℤ) ≤ (J : ℤ)) ∧
    (∃ i w, choices i = some w ∧ (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) ∧
      ∃ k, (incoming i k).coeff w - (incoming i (k + (d : ZMod b))).coeff w ≠ 0) ∧
    ∃ p : Polynomial (residueGeneratorCoefficientField c.top
      ⟨protectedIndex.val, ne_of_gt protectedIndex.property⟩), p.natDegree ≤ 1 ∧
      Polynomial.aeval
        (residueGenerator c.top ⟨protectedIndex.val, ne_of_gt protectedIndex.property⟩) p =
          PowerSeries.coeff n logDefect ∧
      ((p.coeff 1 : residueGeneratorCoefficientField c.top
        ⟨protectedIndex.val, ne_of_gt protectedIndex.property⟩) : OtherField c.top) =
        (-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^n * ZP *
          (d • (∑ i : Fin r, match choices i with
            | none => 0
            | some w => if (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
                ((1/2 : OtherField c.top) * ∑ k : ZMod b,
                  ((incoming i k).coeff w -
                    (incoming i (k + (d : ZMod b))).coeff w)^2) *
                  (completeResponseCycle (c.originalInternalResidue P) active
                    (i.val : ZMod (originalSelectedCount (hD := hD) P)))⁻¹
              else 0) -
            ((n + 1 : ℕ) : OtherField c.top) *
              c.residueMap (pderiv J (cellSchur D hD.1)) * PowerSeries.coeff 1 logDefect) := by
  classical
  let : NeZero b := ⟨by omega⟩
  let : NeZero r := ⟨ne_of_gt hrpos⟩
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hshort : (b - a) * r < originalSelectedCount (hD := hD) P := by
    rw [hcountP]
    exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (by omega) ha) hrpos
  obtain ⟨hCQ, hdata⟩ := c.originalClosure_phase_first_discrepancies P Q z hQ active
    b r (b - a) hcountP hresponse hgap hmax
  refine ⟨hcountP, hshort, hCQ, ?_⟩
  intro hactive
  have hwitness := hdata hactive
  dsimp only at hwitness ⊢
  generalize hCycle : finiteWordCycle (c.originalInternalEndpointProfiles Q)
    (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega) = Cycle at hwitness ⊢
  rcases hwitness with hperiod | ⟨choices, J, hchoices, hattain⟩
  · exact Or.inl hperiod
  · let δ := windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0
    have hδ : 0 ≤ δ := by
      unfold δ windowSum
      apply Finset.sum_nonneg
      intro i _
      have hg := c.originalCompletedGap_gt_top P
        ((ZMod.finEquiv _).symm (0 + i • (1 : ZMod (originalSelectedCount (hD := hD) P))))
      have hN : 0 < (c.top : ℤ) := by exact_mod_cast c.top.pos
      change 0 ≤ c.originalCompletedGap P
        ((ZMod.finEquiv _).symm (0 + i • (1 : ZMod (originalSelectedCount (hD := hD) P))))
      omega
    have hδd : 0 ≤ (b - a) • δ := nsmul_nonneg hδ _
    have hJ : 0 < (J : ℤ) := by exact_mod_cast J.pos
    have hHpos : 0 < (b - a) • δ + (J : ℤ) := by omega
    let H : ℕ+ := ⟨((b - a) • δ + (J : ℤ)).toNat, by omega⟩
    have hH : (H : ℤ) = (b - a) • windowSum
        (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ) :=
      Int.toNat_of_nonneg hHpos.le
    obtain ⟨_, _, _, _, hcoef⟩ := c.originalCompleted_normal_phase_energy_coefficient
      P W A Q q u v w z hq0 hv hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr
        hKU hKW active hresponse hgap hmax hn J H hH κ hmatch
    obtain ⟨p, hdegree, heval, _, hcoeff⟩ := hcoef hactive
    dsimp only at hcoeff
    rw [hCycle] at hcoeff
    right
    refine ⟨choices, J, H, hH, hchoices, hattain, p, hdegree, heval, ?_⟩
    exact hcoeff choices hchoices

end SkewCornerDescent.Matrix.SelectedCoordinate
