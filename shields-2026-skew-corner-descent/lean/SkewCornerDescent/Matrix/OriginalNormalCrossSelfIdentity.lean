/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalLongChargeIdentity
import SkewCornerDescent.Matrix.OriginalAmalgamationSelfCharge
import SkewCornerDescent.Matrix.OriginalLongProfileCharge
import SkewCornerDescent.Matrix.OriginalBalancedSelfCharge
import SkewCornerDescent.Matrix.OriginalVerticalGapPeriod

/-!
# Complete original cross-minus-self logarithmic derivative

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Original determinant comparison, full prefix charges, actual residue phases,
complete endpoint gradients, and the raw/chart self correction compose into
one directed cross-minus-self identity. The whole first-normal logarithmic
coefficient and exact n+1 pair multiplicity remain. This is a derivative
identity; phase-filtered energy, high-variable affine extraction, and literal
recovery are not asserted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original higher logarithmic derivative is the full weighted
directed cross-minus-self profile charge and the whole first-normal correction.
No profile energy, high affine extraction, or literal-state conclusion is assumed. -/
theorem originalCompleted_normal_cross_self_identity {n m an qn : ℕ}
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
    let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    let δ₀ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    ∃ hshort : n < originalSelectedCount (hD := hD) P,
    ∃ hcountA : originalSelectedCount (hD := hD) A = originalSelectedCount (hD := hD) P + n,
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have hn' : 2 ≤ n := hn
      omega⟩ = active) →
    let ZP := ∏ i : Fin n, (c.originalInternalResidue P
      ⟨i.val, by have := i.isLt; omega⟩)⁻¹
    δ₀ (PowerSeries.coeff n logDefect) =
      (-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^n * ZP *
        (d • (c.originalCrossPrefixCharge Q n J (originalSelectedCount (hD := hD) P)
            (by omega) -
          c.originalSelfPrefixCharge Q J (originalSelectedCount (hD := hD) P)
            (by have hn' : 2 ≤ n := hn; omega)) -
          ((n + 1 : ℕ) : OtherField c.top) *
            c.residueMap (pderiv J (cellSchur D hD.1)) * PowerSeries.coeff 1 logDefect) := by
  let d := b - a
  let n := d * r
  have hn2 : 2 ≤ n := hn
  have hd : 0 < d := by dsimp only [d]; omega
  let : NeZero r := ⟨ne_of_gt hrpos⟩
  let : NeZero n := ⟨by omega⟩
  let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  obtain ⟨hshort, hcountA, hcountQ, hlong⟩ :=
    c.originalCompleted_normal_long_charge_identity P W A Q q u v w z hq0 hv
      hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr hKU hKW active hresponse
      hgap hmax hn J H hH κ hmatch
  have hshort' : n < originalSelectedCount (hD := hD) P := hshort
  have hcountA' : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + n := hcountA
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hrn : r ≤ n := by dsimp only [n]; nlinarith
  have hrP : r ≤ originalSelectedCount (hD := hD) P - 1 := by omega
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
  have hHQ : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap Q ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ) := by
    rw [hsumQ]
    exact hH
  obtain ⟨_, _, hLA⟩ := c.originalCompleted_amalgamation_self_charge
    P W A q u v w hq0 hv hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW
    active hresponse hgap hn J H hH
  obtain ⟨_, hself⟩ := c.originalClosure_balanced_self_charge P Q z hQ active b d r
    hcountP hshort hresponse J
  obtain ⟨_, hcycleQ⟩ := c.originalClosure_normal_residue_cycle P Q z hQ active
  refine ⟨hshort, hcountA, hcountQ, ?_⟩
  intro hactive
  have hlong' := hlong hactive
  have hself' := hself hactive
  have hcQ := hcycleQ hactive
  have hSiQ (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
      c.originalInternalResidue Q i = completeResponseCycle (c.originalInternalResidue P) active
        (i.val : ZMod (originalSelectedCount (hD := hD) P)) := by
    have he := hcQ i
    rw [c.originalInternal_normal_constant Q] at he
    exact he
  have hresQ (i j : Fin (originalSelectedCount (hD := hD) Q - 1))
      (hij : j.val = i.val + r) :
      c.originalInternalResidue Q i = c.originalInternalResidue Q j := by
    rw [hSiQ, hSiQ, hij, Nat.cast_add, hresponse]
  have hLQ := c.originalInternal_long_charge_profiles Q r d hn hpQ
    (originalSelectedCount (hD := hD) P) (by omega) hresQ J H hHQ
  have hpInv (i j : Fin (originalSelectedCount (hD := hD) P - 1))
      (hij : j.val = i.val + r) : (c.originalInternalResidue P i)⁻¹ =
        (c.originalInternalResidue P j)⁻¹ := by
    rw [← completeResponseCycle_prefix (c.originalInternalResidue P) active i,
      ← completeResponseCycle_prefix (c.originalInternalResidue P) active j, hij, Nat.cast_add,
      hresponse]
  let ZP := ∏ i : Fin n, (c.originalInternalResidue P ⟨i.val, by have := i.isLt; omega⟩)⁻¹
  have hZP : ZP = (∏ i : Fin r,
      (c.originalInternalResidue P ⟨i.val, i.isLt.trans_le hrP⟩)⁻¹)^d := by
    simpa only [ZP, n, zero_add] using finite_periodic_window_product
      (fun i => (c.originalInternalResidue P i)⁻¹) hrP hpInv d 0 (by omega)
  have hZQ : (∏ i : Fin r,
      (c.originalInternalResidue Q ⟨i.val, by have := i.isLt; omega⟩)⁻¹)^d = ZP := by
    rw [hZP]
    apply congrArg (fun x : OtherField c.top => x^d)
    apply Finset.prod_congr rfl
    intro i _
    rw [hSiQ, completeResponseCycle_prefix (c.originalInternalResidue P) active
      ⟨i.val, i.isLt.trans_le hrP⟩]
  dsimp only at hLQ
  rw [hZQ] at hLQ
  have hidx : c.originalInternalPeriodHigherIndex Q r d hn hpQ J H hHQ =
      c.originalInternalPeriodHigherIndex P r d hn hgap J H hH := Subtype.ext rfl
  simp only [hidx] at hLQ
  obtain ⟨_, hupperA⟩ := c.originalAmalgamation_upper_internal_matrix P A q v w hq0 hv
    hwindow hA (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx)
  have hVA : normalOnsitePrefixCharge ((c.originalInternalResponseMatrix A).map c.normalSeries)
      n (by omega) =
      normalOnsitePrefixCharge ((c.originalInternalResponseMatrix P).map c.normalSeries)
        n (by omega) := by
    unfold normalOnsitePrefixCharge
    apply Finset.sum_congr rfl
    intro s _
    have he := hupperA ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩
    exact congrArg (fun p => PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹) he
  dsimp only at hLA hlong'
  rw [hLA, hLQ, hVA] at hlong'
  dsimp only
  have hpow : c.normalCoefficient⁻¹^n =
      c.normalCoefficient⁻¹^(n - 1) * c.normalCoefficient⁻¹ := by
    calc
      _ = c.normalCoefficient⁻¹^((n - 1) + 1) :=
        congrArg (fun m : ℕ => c.normalCoefficient⁻¹^m) (by omega)
      _ = _ := pow_succ _ _
  rw [hpow]
  simp only [nsmul_eq_mul] at hself' hlong' ⊢
  linear_combination hlong' -
    ((-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^(n - 1) *
      c.normalCoefficient⁻¹ * ZP) * hself'

end SkewCornerDescent.Matrix.SelectedCoordinate
