/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalComparisonPrefixes
import SkewCornerDescent.Matrix.OriginalAmalgamationResidueCycle
import SkewCornerDescent.Matrix.NormalPrefixChargeFactorization

/-!
# Original normal comparison reduced to its long and onsite charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal source geometry produces every full-normal word period. The actual
identified closure and completed residue phase produce all window products.
The original logarithmic derivative is reduced to long and onsite charges
with the full first logarithmic coefficient and exact n+1 pair multiplicity.
This is a derivative identity; no high-variable affine coefficient extraction
or endpoint-energy or literal-root conclusion is asserted here. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original higher resolving derivative has only its full long charge,
complete onsite charge, and complete first logarithmic coefficient left.
Every cyclic vertex and both exterior pair occurrences are counted. -/
theorem originalCompleted_normal_long_charge_identity {n m an qn : ℕ}
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
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
    let full := fun {k : ℕ} (X : Profile k) => c.normalPolynomialSeries X.schur
    let logDefect := PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (full A ^ b * (full P ^ a * full Q ^ d)⁻¹))
    ∃ hshort : n < originalSelectedCount (hD := hD) P,
    ∃ hcountA : originalSelectedCount (hD := hD) A = originalSelectedCount (hD := hD) P + n,
    ∃ hcountQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have hn' : 2 ≤ n := hn
      omega⟩ = active) →
    let MA := (c.originalInternalResponseMatrix A).map c.normalSeries
    let MQ := (c.originalInternalResponseMatrix Q).map c.normalSeries
    let ZP := ∏ i : Fin n, (c.originalInternalResidue P
      ⟨i.val, by have := i.isLt; omega⟩)⁻¹
    let L := b • normalLongPrefixCharge MA δ (n - 1) n (by omega) -
      d • normalLongPrefixCharge MQ δ (n - 1)
        (originalSelectedCount (hD := hD) P) (by have hn' : 2 ≤ n := hn; omega)
    let V := b • normalOnsitePrefixCharge MA n (by omega) -
      d • normalOnsitePrefixCharge MQ (originalSelectedCount (hD := hD) P)
        (by have hn' : 2 ≤ n := hn; omega)
    δ₀ (PowerSeries.coeff n logDefect) =
      (-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^(n - 1) *
        (-c.normalCoefficient⁻¹ * L + γ * ZP * V -
          γ * ((n + 1 : ℕ) : OtherField c.top) * ZP * PowerSeries.coeff 1 logDefect) := by
  let d := b - a
  let n := d * r
  have hn2 : 2 ≤ n := hn
  have hd : 0 < d := by dsimp only [d]; omega
  let : NeZero r := ⟨ne_of_gt hrpos⟩
  let : NeZero n := ⟨by omega⟩
  let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
  obtain ⟨hshort, hcountA, hcountQ, hfirst, hhigher⟩ :=
    c.originalCompleted_normal_comparison_prefixes P W A Q q u v w z hq0 hv
      hW hwindow hA hQ hq hLq Λ b a r ha hab hrpos hr hKU hKW
      active hresponse hgap hmax hn J H hH κ hmatch
  have hshort' : n < originalSelectedCount (hD := hD) P := hshort
  have hcountA' : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + n := hcountA
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  have hproper : originalSelectedCount (hD := hD) W < originalSelectedCount (hD := hD) P := by
    rw [hcountW, hcountP]
    exact Nat.mul_lt_mul_of_pos_left hab hrpos
  have hstep : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = d * r := by
    rw [hcountP, hcountW, ← Nat.mul_sub_left_distrib, Nat.mul_comm]
  have hshift : originalSelectedCount (hD := hD) A -
      originalSelectedCount (hD := hD) P = n := by omega
  have hrn : r ≤ n := by dsimp only [n]; nlinarith
  have hrP : r ≤ originalSelectedCount (hD := hD) P - 1 := by omega
  let MA := (c.originalInternalResponseMatrix A).map c.normalSeries
  let MQ := (c.originalInternalResponseMatrix Q).map c.normalSeries
  let ZP := ∏ i : Fin n, (c.originalInternalResidue P ⟨i.val, by have := i.isLt; omega⟩)⁻¹
  have hcycleA := c.originalAmalgamation_normal_residue_cycle P W A q v w u hq0 hv
    hwindow hW.symm hA (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx) hC hproper r d hrpos hd
    hstep active hresponse
  obtain ⟨_, hcycleQ⟩ := c.originalClosure_normal_residue_cycle P Q z hQ active
  refine ⟨hshort, hcountA, hcountQ, ?_⟩
  intro hactive
  have hcycleQ' := hcycleQ hactive
  have hpSource (i j : Fin (originalSelectedCount (hD := hD) P - 1))
      (hij : j.val = i.val + r) :
      c.originalInternalResidue P i = c.originalInternalResidue P j := by
    rw [← completeResponseCycle_prefix (c.originalInternalResidue P) active i,
      ← completeResponseCycle_prefix (c.originalInternalResidue P) active j, hij, Nat.cast_add]
    exact (hresponse _).symm
  have hpInv (i j : Fin (originalSelectedCount (hD := hD) P - 1))
      (hij : j.val = i.val + r) : (c.originalInternalResidue P i)⁻¹ =
        (c.originalInternalResidue P j)⁻¹ := congrArg Inv.inv (hpSource i j hij)
  have hZP : ZP = (∏ i : Fin r,
      (c.originalInternalResidue P ⟨i.val, i.isLt.trans_le hrP⟩)⁻¹)^d := by
    simpa only [ZP, n, zero_add] using finite_periodic_window_product
      (fun i => (c.originalInternalResidue P i)⁻¹) hrP hpInv d 0 (by omega)
  have hresA (i j : Fin (originalSelectedCount (hD := hD) A - 1))
      (hij : j.val = i.val + r) : PowerSeries.constantCoeff (MA i i) =
        PowerSeries.constantCoeff (MA j j) := by
    rw [hcycleA i, hcycleA j, hij, Nat.cast_add]
    exact (hresponse _).symm
  have hresQ (i j : Fin (originalSelectedCount (hD := hD) Q - 1))
      (hij : j.val = i.val + r) : PowerSeries.constantCoeff (MQ i i) =
        PowerSeries.constantCoeff (MQ j j) := by
    rw [hcycleQ' i, hcycleQ' j, hij, Nat.cast_add]
    exact (hresponse _).symm
  obtain ⟨_, _, hwordA⟩ := c.originalAmalgamation_internal_word_periods P W A
    q v w u hq0 hv hwindow hW.symm hA
    (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx)
  obtain ⟨_, hwordQ⟩ := c.originalClosure_internal_word_periods P Q z hQ
  dsimp only at hwordA hwordQ
  rw [hshift] at hwordA
  have hfacA := normalOpenPrefixCharge_factor MA δ c.normalCoefficient⁻¹ γ (n - 1) d
    hd (by dsimp only [n]; omega)
    (show n ≤ originalSelectedCount (hD := hD) A - 1 - (n - 1 + 1) by omega)
    hwordA.1 hwordA.2 hresA
  have hfacQ := normalOpenPrefixCharge_factor MQ δ c.normalCoefficient⁻¹ γ (n - 1) d
    hd (by dsimp only [n]; omega)
    (show originalSelectedCount (hD := hD) P ≤
      originalSelectedCount (hD := hD) Q - 1 - (n - 1 + 1) by omega)
    hwordQ.1 hwordQ.2 hresQ
  obtain ⟨_, hupperA⟩ := c.originalAmalgamation_upper_internal_matrix
    P A q v w hq0 hv hwindow hA
    (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx)
  obtain ⟨_, hupperQ⟩ := c.originalClosure_upper_internal_matrix P Q z hQ
  have hZA : (∏ i : Fin r, (PowerSeries.constantCoeff
      (MA ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val, by have := i.isLt; omega⟩))⁻¹)^d = ZP := by
    rw [hZP]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    have he := congrArg PowerSeries.constantCoeff
      (hupperA ⟨i.val, i.isLt.trans_le hrP⟩ ⟨i.val, i.isLt.trans_le hrP⟩)
    rw [c.originalInternal_normal_constant P] at he
    exact congrArg Inv.inv he
  have hZQ : (∏ i : Fin r, (PowerSeries.constantCoeff
      (MQ ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val, by have := i.isLt; omega⟩))⁻¹)^d = ZP := by
    rw [hZP]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    have he := congrArg PowerSeries.constantCoeff
      (hupperQ ⟨i.val, i.isLt.trans_le hrP⟩ ⟨i.val, i.isLt.trans_le hrP⟩)
    rw [c.originalInternal_normal_constant P] at he
    exact congrArg Inv.inv he
  dsimp only at hfacA hfacQ
  rw [hZA] at hfacA
  rw [hZQ] at hfacQ
  change normalOpenOverlapPrefixCharge MA δ c.normalCoefficient⁻¹ γ (n - 1) n (by omega) =
    (-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^(n - 1) *
      (-c.normalCoefficient⁻¹ * normalLongPrefixCharge MA δ (n - 1) n (by omega) +
        γ * ZP * normalOnsitePrefixCharge MA n (by omega) -
        γ * ((n - 1 + 2 : ℕ) : OtherField c.top) * ZP *
          normalFirstPrefixCharge MA c.normalCoefficient⁻¹ n (by omega)) at hfacA
  change normalOpenOverlapPrefixCharge MQ δ c.normalCoefficient⁻¹ γ (n - 1)
      (originalSelectedCount (hD := hD) P) (by omega) =
    (-1 : OtherField c.top)^(n - 1) * c.normalCoefficient⁻¹^(n - 1) *
      (-c.normalCoefficient⁻¹ * normalLongPrefixCharge MQ δ (n - 1)
          (originalSelectedCount (hD := hD) P) (by omega) +
        γ * ZP * normalOnsitePrefixCharge MQ (originalSelectedCount (hD := hD) P) (by omega) -
        γ * ((n - 1 + 2 : ℕ) : OtherField c.top) * ZP *
          normalFirstPrefixCharge MQ c.normalCoefficient⁻¹
            (originalSelectedCount (hD := hD) P) (by omega)) at hfacQ
  rw [hfacA, hfacQ] at hhigher
  simp only [show n - 1 + 2 = n + 1 by omega] at hhigher
  dsimp only
  rw [hfirst]
  simp only [nsmul_eq_mul] at hhigher ⊢
  linear_combination hhigher

end SkewCornerDescent.Matrix.SelectedCoordinate
