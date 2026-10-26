/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalCrossSelfIdentity
import SkewCornerDescent.Matrix.OriginalFirstLogAllHighZero
import SkewCornerDescent.Matrix.OriginalProfileChargeSupport
import SkewCornerDescent.PolynomialPartialSupport

/-!
# Affinity obstruction for the complete original normal coefficient

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
For every eligible period, all full profile charges, residue weights, selected
gradients, and the whole first logarithm omit the protected generator. Their
actual composition proves the second partial derivative zero, including the
two-state cancellation. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At every eligible period, the original normal coefficient has
zero second protected partial derivative. Every full charge-support and whole
first-logarithm independence premise is produced from the actual source.

**Differs from the paper's route.** The manuscript cancels the two-state
quadratic cluster contributions directly. This proof differentiates the
complete raw cross-minus-self identity: exact first-log pair balance and
full profile support make its right side independent of the protected
generator, without a separate enumeration of quadratic clusters. -/
theorem originalCompleted_normal_second_high_zero {n m an qn : ℕ}
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
    (hn : 2 ≤ (b - a) * r) (J H : ℕ+)
    (hH : (H : ℤ) = (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ))
    (κ : OtherField c.top)
    (hmatch : (PowerSeries.constantCoeff (c.normalPolynomialSeries A.schur)) ^ b =
      κ * ((PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur)) ^ a *
        (PowerSeries.constantCoeff (c.normalPolynomialSeries Q.schur)) ^ (b - a))) :
    let d := b - a
    let n := d * r
    let K := c.originalInternalPeriodHigherIndex P r d
      (show 2 ≤ d * r by dsimp only [d]; omega) hgap J H hH
    let δ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ = active) → δ (δ (PowerSeries.coeff n logDefect)) = 0 := by
  let d := b - a
  let n := d * r
  have hn2 : 2 ≤ n := hn
  let K := c.originalInternalPeriodHigherIndex P r d hn2 hgap J H hH
  let δ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let S := residueLowerField c.top K.val
  have hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K.val : ℤ) := by
    change (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ)
    rw [hH]
    have hj := J.pos
    omega
  obtain ⟨hshort, hcountA, hcountQ, hcross⟩ := c.originalCompleted_normal_cross_self_identity
    P W A Q q u v w z hq0 hv hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr
    hKU hKW active hresponse hgap hmax hn2 J H hH κ hmatch
  have hshort' : n < originalSelectedCount (hD := hD) P := hshort
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by
    have := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega⟩
  have hpQ : Function.Periodic
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) Q)) := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_period P Q z hQ r hgap
    · exact c.originalVerticalClosure_completed_gap_period P Q z hQ r hgap
  have hsumQ : windowSum
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x)) 1 r 0 =
      windowSum (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 := by
    rcases hQ with hQ | hQ
    · exact c.originalHorizontalClosure_completed_gap_window P Q z hQ r
    · exact c.originalVerticalClosure_completed_gap_window P Q z hQ r
  have hheightQ : d • windowSum
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x)) 1 r 0 < (K.val : ℤ) := by
    rw [hsumQ]
    exact hheight
  obtain ⟨_, hfirstAll⟩ := c.originalCompleted_first_log_all_high_zero
    P W A Q q u v w z hq0 hv hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr
    hKU hKW active hresponse hgap hmax hn J H hH κ hmatch
  have hC := c.originalCrossPrefixCharge_mem_lower Q r d hn2 hpQ K.val K.property hheightQ
    n J (originalSelectedCount (hD := hD) P) (by omega)
  have hS := c.originalSelfPrefixCharge_mem_lower Q r d hn2 hpQ K.val K.property hheightQ
    J (originalSelectedCount (hD := hD) P) (by omega)
  have hCd : δ (c.originalCrossPrefixCharge Q n J
      (originalSelectedCount (hD := hD) P) (by omega)) = 0 :=
    residueGeneratorDeriv_lower _ _ hC
  have hSd : δ (c.originalSelfPrefixCharge Q J
      (originalSelectedCount (hD := hD) P) (by omega)) = 0 :=
    residueGeneratorDeriv_lower _ _ hS
  have hα : c.normalCoefficient⁻¹ ∈ S := S.inv_mem
    (residueLowerField_mono K.property.le c.normalCoordinate_mem_lower.1)
  let ZP := ∏ i : Fin n,
    (c.originalInternalResidue P ⟨i.val, by have := i.isLt; omega⟩)⁻¹
  have hZ : ZP ∈ S := by
    apply S.prod_mem
    intro i _
    exact S.inv_mem (c.originalInternal_residue_mem_lower P r d hn2 hgap K.val K.property
      hheight _)
  have hpref : (-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^n * ZP ∈ S :=
    S.mul_mem (S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) (S.pow_mem hα _)) hZ
  have hprefd : δ ((-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^n * ZP) = 0 :=
    residueGeneratorDeriv_lower _ _ hpref
  have hγ : ((n + 1 : ℕ) : OtherField c.top) *
      c.residueMap (pderiv J (cellSchur D hD.1)) ∈ S :=
    S.mul_mem (natCast_mem S _) (c.selected_gradient_mem_lower K.val K.property J)
  have hγd : δ (((n + 1 : ℕ) : OtherField c.top) *
      c.residueMap (pderiv J (cellSchur D hD.1))) = 0 :=
    residueGeneratorDeriv_lower _ _ hγ
  refine ⟨hcountQ, ?_⟩
  intro hactive
  have hfirst := hfirstAll hactive
  have he := congrArg δ (hcross hactive)
  dsimp only at hfirst he ⊢
  change δ (δ _) = 0
  rw [δ.leibniz, hprefd, smul_zero, add_zero, map_sub, map_nsmul, map_sub,
    hCd, hSd, sub_self, nsmul_zero, δ.leibniz, hγd, hfirst, smul_zero, smul_zero,
    add_zero, sub_self, smul_zero] at he
  exact he

end SkewCornerDescent.Matrix.SelectedCoordinate
