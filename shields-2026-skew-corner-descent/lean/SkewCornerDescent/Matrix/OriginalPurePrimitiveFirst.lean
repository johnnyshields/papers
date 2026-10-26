/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrimitiveConstantPin
import SkewCornerDescent.Matrix.OriginalPureCycleAlternative
import SkewCornerDescent.Matrix.OriginalOneActiveNormalMatch
import SkewCornerDescent.Matrix.OriginalFirstLogCyclic
import SkewCornerDescent.Matrix.OriginalClosureLiteralRoot
import SkewCornerDescent.Matrix.OrdinaryMonomialFactorization
import SkewCornerDescent.Matrix.OriginalTransfer

/-!
# Original pure primitive first-normal detection or a proper literal root

Formalizes `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The actual pure corner powers supply all counts and maximal component bounds.
The primitive ordinary pin supplies the real closure, full proper-core word
and omitted phase. Complete actual binary profiles give nonzero first charge
unless all connectors agree. Full original logarithm and rational-series
suppliers transfer that charge to the complete supplied defect; the other
branch reconstructs the entire parent as a proper literal empty composition.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
noncomputable local instance purePrimitiveFirstRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

set_option maxHeartbeats 2400000 in
-- The proof composes both complete original normal words and the dependent literal root interface.
/-- A constant pure primitive original response word has a nonzero supplied
first-normal defect coefficient or a proper literal empty b-copy root.
No phase, profile, binary, coefficient, normal match or closure pin is assumed. -/
theorem originalPurePrimitive_first_or_literal_root {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevq : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hprevLq : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (b a : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hcop : Nat.Coprime b a)
    (hKP : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ) (fun j => W.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    (hconstant : ∀ i j, c.originalInternalResidue P i = c.originalInternalResidue P j)
    (lo prevlo hi prevhi : ℤ × ℤ)
    (hlo : lo ∈ P.cells) (hprevlo : prevlo ∈ P.cells)
    (hhi : hi ∈ P.cells) (hprevhi : prevhi ∈ P.cells)
    (hclo : content lo = P.xi 0 - q) (hcprevlo : content prevlo = P.xi 0 - q - 1)
    (hchi : content hi = q) (hcprevhi : content prevhi = q - 1)
    (hdir : lo.2 = prevlo.2 ↔ hi.2 = prevhi.2)
    (δ : ℤ) (hspan : P.xi 0 = (b : ℤ) * δ) :
    PowerSeries.coeff 1 (c.originalDeterminantDefect P A H a b p₀ p₁) ≠ 0 ∨
      ∃ E : Diagram, IsConnectedSkew E ∧ span E = δ.toNat ∧
        (emptyMarkH E).IsLegal ∧ 2 ≤ E.card ∧
        (∃ x ∈ E, ∃ y ∈ E, x.1 ≠ y.1 ∧ x.2 ≠ y.2) ∧
        2 ≤ (horizontalRow b).card ∧ 2 ≤ (verticalColumn b).card ∧
        (P.cells = (emptyMarkH E).compose (horizontalRow b) ∨
          P.cells = (emptyMarkH E).compose (verticalColumn b)) := by
  classical
  have hr : primeOrder (cellSchur D hD.1) (cellSchur D hD.1) = 1 :=
    primeOrder_self (irreducible_cellSchur hD).prime
  have hcountP : originalSelectedCount (hD := hD) P = b := by
    rw [originalSelectedCount_eq_primeOrder, hKP,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, mul_one]
  have hcountW : originalSelectedCount (hD := hD) W = a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, mul_one]
  let : NeZero (originalSelectedCount (hD := hD) P) := ⟨by omega⟩
  let : NeZero b := ⟨by omega⟩
  let : NeZero (b-a) := ⟨by omega⟩
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hC : 0 < originalSelectedCount (hD := hD) W := by rw [hcountW]; exact ha
  have hmax := c.originalPure_component_span P b hKP
  obtain ⟨active, he, hother, hgapPeriod, hcore, on, O, zO, hO, hcenter⟩ :=
    c.originalPrimitive_constant_ordinary_pin P W A H q v u z w hv hwindow hW hA hH
      hcutq hcutLq hprevq hprevLq hmax (cellSchur D hD.1) b a ha hab hcop hr hKP hKW
      p₀ p₁ hpq hdep hconstant lo prevlo hi prevhi hlo hprevlo hhi hprevhi
      hclo hcprevlo hchi hcprevhi hdir
  have hsource := c.originalPrimitive_internal_eq_unique_active P W a b hcop hcountP active hother
  obtain ⟨_, hgap, _⟩ := c.originalPrimitive_closure_heights P W A H q v u z w hv hwindow hW
    hA hH hcutq hcutLq hmax (cellSchur D hD.1) a b ha (by omega) hcop hcountP hcountW
    hKP hKW p₀ p₁ hpq hdep
  let KZ := originalHessenbergDistance (hD := hD) P 0 0 +
    originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _)
  have hKnonneg : 0 ≤ KZ := by
    have hl := c.originalHessenbergDistance_gt_top P hB 0 0 le_rfl
    have hh := c.originalHessenbergDistance_gt_top P hB (Fin.last _) (Fin.last _) le_rfl
    have ht := c.top.pos
    dsimp only [KZ]
    omega
  let K := KZ.toNat
  have hKcoe : (K : ℤ) = KZ := Int.toNat_of_nonneg hKnonneg
  have hgapK (i) : c.originalCompletedGap P i = (K : ℤ)-(c.top : ℤ) := by
    rw [hKcoe]
    exact hgap i
  obtain ⟨hTA, hTO, halternative⟩ := c.originalPure_constant_cycle_alternative
    P W A O q v u z zO hq hv hwindow hW hA hO hcutq hcutLq b a ha hab hcop
    hKP hKW active.val K hsource hgapK hcore hcenter
  rcases halternative with hnone | hcharge
  · apply Or.inr
    have hcopShift : Nat.Coprime (b-a) b :=
      (Nat.coprime_self_sub_left (by omega)).mpr hcop.symm
    have hBroot : originalSelectedCount (hD := hD) P = b*1 := by simpa only [mul_one] using hcountP
    have hcomplete (x : ZMod (originalSelectedCount (hD := hD) P)) :
        completeResponseCycle (c.originalInternalResidue P) active.val x = active.val := by
      unfold completeResponseCycle
      split_ifs
      · exact hsource _
      · rfl
    have hresponse : Function.Periodic
        (completeResponseCycle (c.originalInternalResidue P) active.val)
        ((1 : ℕ) : ZMod (originalSelectedCount (hD := hD) P)) :=
      fun x => (hcomplete _).trans (hcomplete _).symm
    obtain ⟨hCO, hroot⟩ := c.originalClosure_no_discrepancy_literal_root P O zO hO active.val
      b 1 (b-a) hcopShift (by omega) hBroot hresponse
      (by simpa only [Nat.cast_one] using hgapPeriod) hmax δ hspan
    apply hroot hcenter
    let hlen : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) O - 1 := by
      omega
    let cycle := finiteWordCycle (c.originalInternalEndpointProfiles O) hlen
    let hlenB : b ≤ originalSelectedCount (hD := hD) O - 1 := by omega
    have hphase (i : Fin 1) (k : ZMod b) :
        ZMod.ringEquivCongr hBroot.symm (phaseCycleEquiv b 1 (i,k)) =
          (k.val : ZMod (originalSelectedCount (hD := hD) P)) := by
      rw [phaseCycleEquiv_apply, map_add, map_mul, map_natCast, map_natCast]
      have hi : i.val = 0 := by have := i.isLt; omega
      simp only [hi, Nat.cast_zero, Nat.cast_one, zero_add, one_mul, map_natCast]
    have hcycle (k : ZMod b) : cycle (k.val : ZMod (originalSelectedCount (hD := hD) P)) =
        c.originalInternalEndpointCycle O hlenB k := by
      apply congrArg (c.originalInternalEndpointProfiles O)
      apply Fin.ext
      change (k.val : ZMod (originalSelectedCount (hD := hD) P)).val = k.val
      rw [ZMod.val_natCast, hcountP, Nat.mod_eq_of_lt (ZMod.val_lt k)]
    intro i k
    change (cycle _).1 = (cycle _).1
    rw [hphase, hphase, hcycle, hcycle]
    exact hnone k
  · apply Or.inl
    obtain ⟨κ, hκ, hseries, hmatch, hρ⟩ := c.originalOneActive_normal_match
      P W A H O q v u z w zO hq hv hwindow hW hA hH hO hcutq hcutLq hC hmax
      (cellSchur D hD.1) b a (by omega) hKP hKW p₀ p₁ hpq hdep active hother hcenter
    obtain ⟨_, _, _, hlog⟩ := c.originalCompleted_first_log_cyclic P W A O q z v u zO
      hq hv hW.symm hwindow hA hO hcutq hcutLq (cellSchur D hD.1) b a 1 ha (by omega)
      (by omega) hr hKP hKW hmax (by omega) (κ : OtherField c.top)
      (by simpa only [mul_assoc] using hmatch)
    dsimp only at hlog
    let : Algebra ℚ (OtherField c.top) := DivisionRing.toRatAlgebra
    let : NeZero ((b-a)*1) := ⟨by omega⟩
    have hAeq := normalCyclicFirstCharge_matrix_length_congr
      (T := (b-a)*1) (U := b-a)
      ((c.originalInternalResponseMatrix A).map c.normalSeries) c.normalCoefficient⁻¹
      (by omega) hTA (Nat.mul_one (b-a))
    have hOeq := normalCyclicFirstCharge_matrix_length_congr
      (T := originalSelectedCount (hD := hD) P) (U := b)
      ((c.originalInternalResponseMatrix O).map c.normalSeries) c.normalCoefficient⁻¹
      (by omega) hTO hcountP
    have hlogne : PowerSeries.coeff 1 (PowerSeries.logOf
        (PowerSeries.C (κ : OtherField c.top)⁻¹ *
          (c.normalPolynomialSeries A.schur ^ b *
            (c.normalPolynomialSeries P.schur ^ a *
              c.normalPolynomialSeries O.schur ^ (b-a))⁻¹))) ≠ 0 := by
      rw [hlog, hAeq, hOeq]
      exact hcharge
    have hf : PowerSeries.constantCoeff (c.normalPolynomialSeries P.schur) ≠ 0 := by
      simpa only [c.normalPolynomialSeries_constant] using c.originalSchur_residue_ne_zero P hB hmax
    have hmaxO : ∀ C ∈ edgeComponents (diagramInterior O.cells), span C ≤ (c.top : ℕ) := by
      rcases hO with hH | hV
      · exact c.originalHorizontalClosure_profile_component_span P O zO hH hmax
      · exact c.originalVerticalClosure_profile_component_span P O zO hV hmax
    have hOunit : PowerSeries.constantCoeff (c.normalPolynomialSeries O.schur) ≠ 0 := by
      simp only [c.normalPolynomialSeries_constant]
      apply c.originalSchur_residue_ne_zero O
      · rw [originalOrdinaryClosure_selected_count P O zO hO]
        omega
      · exact hmaxO
    have hκne : (κ : OtherField c.top) ≠ 0 := by rcases hκ with rfl | rfl <;> norm_num
    obtain ⟨l, hl, hlone, hlD⟩ := ordinaryMonomialDefect_detection
      (c.normalPolynomialSeries A.schur) (c.normalPolynomialSeries P.schur)
      (c.normalPolynomialSeries O.schur) (κ : OtherField c.top) a b 1 (by omega)
      hf hOunit hκne hmatch hlogne
    have hle : l = 1 := by omega
    rw [hle] at hlD
    simpa only [originalDeterminantDefect, hseries] using hlD

end SkewCornerDescent.Matrix.SelectedCoordinate
