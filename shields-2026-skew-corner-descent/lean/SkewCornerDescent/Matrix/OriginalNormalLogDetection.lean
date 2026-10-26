/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalPhaseWitness
import SkewCornerDescent.Matrix.OriginalClosureEnergyNonzero
import SkewCornerDescent.Matrix.OriginalInternalInverseJets

/-!
# Bounded detection of the actual original comparison logarithm

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
Actual source phase choices produce nonzero filtered energy and the protected
ordinary coefficient.  The full first-normal correction is retained: a
nonzero first jet detects immediately, otherwise transcendence of the produced
generator detects by the complete normal bound.  The alternative is equality
of all shifted full incoming profiles; the bound is strictly below the full
source count.  Original-defect transfer and whole cell-root reconstruction
are separate assembly steps.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The whole actual original comparison logarithm is detected by the full
normal bound unless every shifted complete incoming profile agrees.  Phase
data, a nonzero energy and the original protected coefficient are all produced;
the first-normal correction is retained and handled by the actual first jet. -/
theorem originalCompleted_normal_log_detection {n m an qn : ℕ}
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
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    letI : NeZero b := ⟨by omega⟩
    letI : NeZero r := ⟨ne_of_gt hrpos⟩
    let d := b - a
    let states := d * r
    let C := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    let incoming := fun (i : Fin r) (k : ZMod b) =>
      (C (ZMod.ringEquivCongr hcountP.symm (phaseCycleEquiv b r (i,k)))).1
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    states < originalSelectedCount (hD := hD) P ∧
      ((∀ i k, incoming i k = incoming i (k + (d : ZMod b))) ∨
        ∃ j : ℕ, 0 < j ∧ j ≤ states ∧ PowerSeries.coeff j logDefect ≠ 0) := by
  classical
  let : NeZero b := ⟨by omega⟩
  let : NeZero r := ⟨ne_of_gt hrpos⟩
  obtain ⟨hcountP, hshort, hCQ, hwitness⟩ := c.originalCompleted_normal_phase_energy_witness
    P W A Q q u v w z hq0 hv hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr
      hKU hKW active hresponse hgap hmax hn κ hmatch
  obtain ⟨_, henergy⟩ := c.originalClosure_filtered_phase_energy_ne_zero P Q z hQ active
    b r (b - a) hcountP hmax
  refine ⟨hcountP, hCQ, ?_⟩
  intro hactive
  have hdata := hwitness hactive
  have hE := henergy hactive
  dsimp only at hdata hE ⊢
  refine ⟨hshort, ?_⟩
  generalize hCycle : finiteWordCycle (c.originalInternalEndpointProfiles Q)
    (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega) = Cycle at hdata hE ⊢
  let Dlog := PowerSeries.logOf
    (PowerSeries.C κ⁻¹ * (c.normalPolynomialSeries A.schur ^ b *
      (c.normalPolynomialSeries P.schur ^ a * c.normalPolynomialSeries Q.schur ^ (b-a))⁻¹))
  by_cases hfirst : PowerSeries.coeff 1 Dlog = 0
  · rcases hdata with hperiod | ⟨choices, J, H, hH, hchoices, hattain, p, hdegree, heval, hcoeff⟩
    · exact Or.inl hperiod
    · have hEne := hE choices J hattain
      have hZP : (∏ i : Fin ((b-a)*r), (c.originalInternalResidue P
          ⟨i.val, by have := i.isLt; omega⟩)⁻¹) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        apply inv_ne_zero
        exact c.originalHessenberg_residue_ne_zero P
          (NeZero.pos (originalSelectedCount (hD := hD) P)) hmax
          ⟨i.val+1, by have := i.isLt; omega⟩
      have hslope : ((p.coeff 1 : residueGeneratorCoefficientField c.top
          ⟨(c.originalInternalPeriodHigherIndex P r (b-a) hn hgap J H hH).val,
            ne_of_gt (c.originalInternalPeriodHigherIndex P r (b-a) hn hgap J H hH).property⟩) :
            OtherField c.top) ≠ 0 := by
        rw [hcoeff]
        change _ * ((b-a) • _ - _ * PowerSeries.coeff 1 Dlog) ≠ 0
        rw [hfirst, mul_zero, sub_zero]
        apply mul_ne_zero
        · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
            (pow_ne_zero _ (inv_ne_zero c.normalCoefficient_ne_zero))) hZP
        · rw [nsmul_eq_mul]
          apply mul_ne_zero (show ((b-a : ℕ) : OtherField c.top) ≠ 0 by
            exact_mod_cast (by omega : b-a ≠ 0))
          exact hEne
      have hpcoef : p.coeff 1 ≠ 0 := by
        intro hz
        apply hslope
        rw [hz]
        rfl
      have hp : p ≠ 0 := by
        intro hz
        apply hpcoef
        rw [hz]
        rfl
      have hevalne : Polynomial.aeval
          (residueGenerator c.top
            ⟨(c.originalInternalPeriodHigherIndex P r (b-a) hn hgap J H hH).val,
              ne_of_gt
                (c.originalInternalPeriodHigherIndex P r (b-a) hn hgap J H hH).property⟩)
          p ≠ 0 := by
        intro hz
        apply hp
        exact (transcendental_iff_injective.mp
          (residueGeneratorCoefficientField_transcendental c.top _))
            (by simpa only [map_zero] using hz)
      right
      refine ⟨(b-a)*r, by omega, le_rfl, ?_⟩
      intro hz
      exact hevalne (heval.trans hz)
  · exact Or.inr ⟨1, by omega, by omega, hfirst⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
