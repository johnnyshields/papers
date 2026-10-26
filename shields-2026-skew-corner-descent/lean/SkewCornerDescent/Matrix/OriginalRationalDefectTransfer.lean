/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalComparisonLogTransfer
import SkewCornerDescent.Matrix.OriginalRationalPrefactor
import SkewCornerDescent.Matrix.NormalRationalCoefficientTransfer
import SkewCornerDescent.Matrix.NormalRationalResidueMatch
import SkewCornerDescent.Matrix.OriginalWindowGeometricResidue

/-!
# Literal original rational defect coefficient from exact residue matching

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The source, overlap, amalgamation and closure are literal profiles. Their coefficient
producers, rational virtual units and signed prefactor are composed without replacing
full inverses by residues. The paper's standing signed rational residue match remains
an input; its geometric conversion to the raw defect equation is proved here. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Given exact original residue matching, the full actual rational defect has its
prefactor-weighted signed cyclic coefficient. All virtual units and every factor's
lower resolving-generator independence are produced from the literal geometry. -/
theorem originalRationalDefect_coefficient_of_residue_match {n m s t : ℕ} {ι : Type*}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (hab : a < b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)]
    (k h : ℕ) (hh : 0 < h) (hhB : h < originalSelectedCount (hD := hD) P)
    (hlen : h + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0)
    (classes : Finset ι) (α : ι → ℚ) (e : ι → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hdegree : (∑ i ∈ classes, e i) = ((b - a : ℕ) : ℤ))
    (hresidue : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      (ε : OtherField c.top) * ∏ i ∈ classes,
        (c.residueMap Q.schur / c.residueMap P.schur ^ 2 - (α i : OtherField c.top)) ^ e i) :
    let f := c.normalPolynomialSeries P.schur
    let E := c.normalPolynomialSeries A.schur
    let ρ := c.originalRationalPrefactor P Q classes α e ε
    let cycle := finiteWordCycle (n := originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W) (c.originalInternalResidue P) (by omega)
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    (∀ l, l < h → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ)) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff h (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ)) =
      PowerSeries.constantCoeff ρ *
        (((-1 : OtherField c.top) ^ h * (c.normalCoefficient)⁻¹ ^ h) *
          ((b : OtherField c.top) * inverseWindowSum cycle (h + 1) -
            ∑ i ∈ classes, (e i : OtherField c.top) * inverseWindowSum
              (completeResponseCycle (c.originalInternalResidue P)
                (c.originalVirtualCentralResponse P Q middle (α i))) (h + 1))) ∧
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ) h := by
  classical
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have hba : a + (b - a) = b := by omega
  have hbalance : (∑ i ∈ classes, e i) = (b : ℤ) - (a : ℤ) := by
    rw [hdegree]
    omega
  have htE := c.originalAmalgamation_normalized_log_from_source P W A q v u z hq hv
    hwindow hW hA hcutq hcutLq hC hmax Λ b a r hab hrpos hr hKU hKW
    k h hh hhB hlen hp K hK hKeq
  have htf := c.originalSchur_normalized_log_linear_periodic P hB hmax
    r k h hh hhB hlen hp K hK hKeq
  have htT (i : ι) := c.originalVirtualClosure_normalized_log_cycle P Q w hQ hB hmax
    r k h hh hhB hlen hp K hK hKeq (α i)
  have hlog := c.originalComparison_normalized_log_from_source P W A Q q v u z w hq hv
    hwindow hW hA hQ hcutq hcutLq hC hmax Λ b a r hab hrpos hr hKU hKW
    k h hh hhB hlen hp K hK hKeq classes α e a hbalance
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hcountW : originalSelectedCount (hD := hD) W = a * r := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hproper : originalSelectedCount (hD := hD) W < originalSelectedCount (hD := hD) P := by
    rw [hcountP, hcountW]
    exact Nat.mul_lt_mul_of_pos_right hab hrpos
  have hinv := originalAmalgamation_selected_inventory (hD := hD) P W A q v u z
    hv hwindow hW hA
  have hmaxA := originalAmalgamation_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  have hE0 := c.originalSchur_residue_ne_zero A (by omega) hmaxA
  have hf0 := c.originalSchur_residue_ne_zero P hB hmax
  have hqtop : q < P.xi 0 := by
    let x := ((s : ℤ), W.zeta (Fin.last s) + s)
    have hx : x ∈ W.cells := W.row_left_mem_cells (Fin.last s)
    have hy : x + z ∈ P.cells.filter
        (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
      rw [← hW]
      apply mem_translate.mpr
      simpa only [add_sub_cancel_right] using hx
    have hb := (Finset.mem_filter.mp hy).2
    omega
  have hcross := c.originalWindow_residue_cross_identity P W A q v u z hq hqtop hv
    hwindow hW hA hC
  have hW0 : c.residueMap W.schur ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcross
    exact (pow_ne_zero 2 hf0) hcross.symm
  have hmatch := rationalDefect_residue_match (c.residueMap P.schur) (c.residueMap A.schur)
    (c.residueMap W.schur) (c.residueMap Q.schur) (ε : OtherField c.top)
    classes (fun i => (α i : OtherField c.top)) e a b hf0 hW0 hcross hbalance hresidue
  let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  let f := c.normalPolynomialSeries P.schur
  let E := c.normalPolynomialSeries A.schur
  let β := c.normalPolynomialSeries Q.schur
  let T := fun i => β - PowerSeries.C (α i : OtherField c.top) * f ^ 2
  have hTc : ∀ i ∈ classes, PowerSeries.constantCoeff (T i) ≠ 0 := by
    intro i _
    simpa only [T, β, f, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C,
      c.normalPolynomialSeries_constant] using
      c.originalVirtualClosure_residue_ne_zero P Q w hQ hB hmax (α i)
  have hε0 : (ε : OtherField c.top) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hDε : δ (ε : OtherField c.top) = 0 := by
    apply residueGeneratorDeriv_lower
    exact (residueLowerField c.top K).intCast_mem ε
  have he := coeff_deriv_full_rational_defect δ classes E f β
    (fun i => (α i : OtherField c.top)) e (ε : OtherField c.top) a (b - a) h hh
    (by simpa only [f, c.normalPolynomialSeries_constant] using hf0)
    (by simpa only [E, c.normalPolynomialSeries_constant] using hE0) hε0 hDε hTc hdegree
    (by simpa only [E, f, β, hba, c.normalPolynomialSeries_constant, map_sub, map_mul,
      map_pow, PowerSeries.constantCoeff_C] using hmatch)
    htE.1 htf.1 (fun i _ => (htT i).1)
  rw [hba] at he
  have hlogs := coeff_deriv_normal_comparison_log_first δ classes E f T e b a h hh
    (by simpa only [E, c.normalPolynomialSeries_constant] using hE0)
    (by simpa only [f, c.normalPolynomialSeries_constant] using hf0) hTc
    htE.1 htf.1 (fun i _ => (htT i).1)
  dsimp only [δ, E, f, β, T] at he hlogs
  dsimp only at hlog ⊢
  rw [← hlogs, hlog.2] at he
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    have hz := coeff_deriv_full_rational_defect_zero δ classes E f β
      (fun i => (α i : OtherField c.top)) e (ε : OtherField c.top) a (b - a) l
      (by simpa only [f, c.normalPolynomialSeries_constant] using hf0)
      hDε hTc hdegree
      (fun j hj => htE.1 j (hj.trans_lt hl))
      (fun j hj => htf.1 j (hj.trans_lt hl))
      (fun i _ j hj => (htT i).1 j (hj.trans_lt hl))
    rw [hba] at hz
    simpa only [δ, E, f, β, originalRationalPrefactor] using hz
  · simpa only [originalRationalPrefactor] using he
  · have hfAffine := c.originalSchur_jets_affine_periodic P hB hmax
      r k h hh hhB hlen hp K hK hKeq
    have hβAffine := (c.originalVirtualClosure_normalized_log_from_source P Q w hQ hB hmax
      r k h hh hhB hlen hp K hK hKeq 0).2.2
    have hAffine := fullRationalDefect_jets_affine
      (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      classes (fun i => (α i : OtherField c.top)) e (ε : OtherField c.top)
      f E β a b h hh ((residueLowerField c.top K).intCast_mem ε)
      (fun i _ => SubfieldClass.ratCast_mem (residueLowerField c.top K) (α i))
      hfAffine htE.2.2 hβAffine
    simpa only [f, E, β, originalRationalPrefactor] using hAffine

end SkewCornerDescent.Matrix.SelectedCoordinate
