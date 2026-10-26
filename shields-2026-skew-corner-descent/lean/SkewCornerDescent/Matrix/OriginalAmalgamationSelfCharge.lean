/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCompletedAmalgamationSelfGradient
import SkewCornerDescent.Matrix.OriginalAmalgamationResidueCycle
import SkewCornerDescent.Matrix.OriginalSelfPrefixCharge
import SkewCornerDescent.Matrix.NormalLongPrefixWeights

/-!
# Actual amalgamation long charge from complete source self profiles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Original corner powers produce the prefix size. Literal copies, actual
residue phases, full long-entry gradients, and complete inverse products
identify the whole long prefix with its full source self-profile charge.
No profile-gradient or coefficient identity is an extra premise. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual amalgamation long prefix is its complete original source
self-profile charge times the full source inverse period product. -/
theorem originalCompleted_amalgamation_self_charge {n m an : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile an)
    (q : ℤ) (u v w : ℤ × ℤ) (hq0 : 0 ≤ q) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate w A.cells)
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
    (hn : 2 ≤ (b - a) * r) (J H : ℕ+)
    (hH : (H : ℤ) = (b - a) • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let d := b - a
    let n := d * r
    let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    ∃ hshort : n < originalSelectedCount (hD := hD) P,
    ∃ hcountA : originalSelectedCount (hD := hD) A = originalSelectedCount (hD := hD) P + n,
    let ZP := ∏ i : Fin n, (c.originalInternalResidue P
      ⟨i.val, by have := i.isLt; omega⟩)⁻¹
    normalLongPrefixCharge ((c.originalInternalResponseMatrix A).map c.normalSeries)
      δ (n - 1) n (by have hn' : 2 ≤ n := hn; omega) =
      ZP * c.originalSelfPrefixCharge P J n (by omega) := by
  let d := b - a
  let n := d * r
  have hn2 : 2 ≤ n := hn
  have hd : 0 < d := by dsimp only [d]; omega
  let : NeZero r := ⟨ne_of_gt hrpos⟩
  let : NeZero n := ⟨by omega⟩
  let K := c.originalInternalPeriodHigherIndex P r d hn hgap J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
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
  have hshort : n < originalSelectedCount (hD := hD) P := by omega
  have hinv := originalAmalgamation_selected_inventory (hD := hD)
    P W A q v w u hv hwindow hW.symm hA
  have hcountA : originalSelectedCount (hD := hD) A =
      originalSelectedCount (hD := hD) P + n := by omega
  obtain ⟨_, hupperA⟩ := c.originalAmalgamation_upper_internal_matrix
    P A q v w hq0 hv hwindow hA
    (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx)
  have hrn : r ≤ n := by dsimp only [n]; nlinarith
  have hrP : r ≤ originalSelectedCount (hD := hD) P - 1 := by omega
  let MA := (c.originalInternalResponseMatrix A).map c.normalSeries
  let ZP := ∏ i : Fin n, (c.originalInternalResidue P ⟨i.val, by have := i.isLt; omega⟩)⁻¹
  have hcycleA := c.originalAmalgamation_normal_residue_cycle P W A q v w u hq0 hv
    hwindow hW.symm hA (fun x hx => privateDiagonal_avoids_interior hq hx)
    (fun x hx => privateDiagonal_avoids_interior hLq hx) hC hproper r d hrpos hd
    hstep active hresponse
  have hresA (i j : Fin (originalSelectedCount (hD := hD) A - 1))
      (hij : j.val = i.val + r) : PowerSeries.constantCoeff (MA i i) =
        PowerSeries.constantCoeff (MA j j) := by
    rw [hcycleA i, hcycleA j, hij, Nat.cast_add]
    exact (hresponse _).symm
  have hpInv (i j : Fin (originalSelectedCount (hD := hD) P - 1))
      (hij : j.val = i.val + r) : (c.originalInternalResidue P i)⁻¹ =
        (c.originalInternalResidue P j)⁻¹ := by
    rw [← completeResponseCycle_prefix (c.originalInternalResidue P) active i,
      ← completeResponseCycle_prefix (c.originalInternalResidue P) active j, hij, Nat.cast_add,
      hresponse]
  have hZP : ZP = (∏ i : Fin r,
      (c.originalInternalResidue P ⟨i.val, i.isLt.trans_le hrP⟩)⁻¹)^d := by
    simpa only [ZP, n, zero_add] using finite_periodic_window_product
      (fun i => (c.originalInternalResidue P i)⁻¹) hrP hpInv d 0 (by omega)
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
  have hRSi (s : Fin n) : PowerSeries.constantCoeff
      (MA ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩) =
        c.originalInternalResidue P ⟨s.val, by have := s.isLt; omega⟩ := by
    have he := congrArg PowerSeries.constantCoeff
      (hupperA ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩)
    rw [c.originalInternal_normal_constant P] at he
    exact he
  have hfac := normalLongPrefixCharge_residue_factor MA δ (n - 1) d hd
    (by dsimp only [n]; omega)
    (show n ≤ originalSelectedCount (hD := hD) A - 1 - (n - 1 + 1) by omega) hresA
  dsimp only at hfac
  rw [hZA] at hfac
  simp only [Nat.add_assoc, Nat.sub_add_cancel (show 1 ≤ n by omega)] at hfac
  have hsum : (∑ s : Fin n, PowerSeries.constantCoeff (δ
      (MA ⟨s.val, by have := s.isLt; omega⟩
        ⟨s.val + n, by have := s.isLt; omega⟩)) *
      (PowerSeries.constantCoeff
        (MA ⟨s.val, by have := s.isLt; omega⟩ ⟨s.val, by have := s.isLt; omega⟩))⁻¹) =
        c.originalSelfPrefixCharge P J n (by omega) := by
    unfold originalSelfPrefixCharge
    dsimp only
    apply Finset.sum_congr rfl
    intro s _
    rw [hRSi]
    obtain ⟨_, _, _, hgrad⟩ := c.originalCompleted_amalgamation_prefix_self_gradient
      P W A q u v w hq0 hv hW hwindow hA hq hLq Λ b a r ha hab hrpos hr hKU hKW
      hgap hn s J H hH
    dsimp only at hgrad
    have hidx :
        (⟨s.val, by have := s.isLt; omega⟩ :
          Fin (originalSelectedCount (hD := hD) P)).succ =
        originalInternalStateIndex P ⟨s.val, by have := s.isLt; omega⟩ := Fin.ext rfl
    simp only [hidx] at hgrad
    have hc : PowerSeries.constantCoeff (δ
        (MA ⟨s.val, by have := s.isLt; omega⟩
          ⟨s.val + n, by have := s.isLt; omega⟩)) =
        residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
          (c.regularResidue (c.originalInternalResponseMatrix A
            ⟨s.val, by have := s.isLt; omega⟩
            ⟨s.val + n, by have := s.isLt; omega⟩)) := by
      change PowerSeries.constantCoeff (δ (c.normalSeries
        (c.originalInternalResponseMatrix A ⟨s.val, by have := s.isLt; omega⟩
          ⟨s.val + n, by have := s.isLt; omega⟩))) = _
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, residueSeriesGeneratorDeriv_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, c.normalSeries_constant_apply]
    rw [hc]
    simpa only [originalInternalEndpointProfiles] using
      congrArg (fun x => x * (c.originalInternalResidue P
        ⟨s.val, by have := s.isLt; omega⟩)⁻¹) hgrad
  rw [hsum] at hfac
  exact ⟨hshort, hcountA, hfac⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
