/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalStrictComparison
import SkewCornerDescent.Matrix.OriginalRationalDefectTransfer

/-!
# Strict-bin detection in the full original rational defect

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). The complete
original comparison detector transfers through the nonzero actual prefactor to
the original rational defect. Literal common-core geometry supplies its constant
matching equation; no raw matching or periodic gap hypothesis is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Exact standing residue dependence and the literal geometry supply a nonzero
first-fresh coefficient of the full original rational defect in a strict bin. -/
theorem originalRationalDefect_strict_bin_ne_zero {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (hj : 2 ≤ j)
    (hjlen : j = originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)
    (M : ℤ) (hstrict : q < M)
    (hbound : ∀ x : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a)) 1 j x ≤ M)
    (hretain : ∃ x : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun a => c.originalCompletedGap P ((ZMod.finEquiv _).symm a)) 1 j x = M)
    (K : ℕ+) (hK : c.top < K) (hKeq : (K : ℤ) = (c.top : ℤ) + M)
    (classes : Finset ℚ) (e : ℚ → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (b a : ℕ) (hab : a < b)
    (hdegree : (∑ α ∈ classes, e α) = ((b - a : ℕ) : ℤ))
    (hresidue : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      (ε : OtherField c.top) * ∏ α ∈ classes,
        (c.residueMap Q.schur / c.residueMap P.schur ^ 2 - (α : OtherField c.top)) ^ e α) :
    let f := c.normalPolynomialSeries P.schur
    let E := c.normalPolynomialSeries A.schur
    let ρ := c.originalRationalPrefactor P Q classes id e ε
    (∀ l, l < j - 1 → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ)) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1) (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ)) ≠ 0 ∧
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      (f ^ a * (E * f⁻¹ ^ 2) ^ b - ρ) (j - 1) := by
  classical
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have hjB : j ≤ originalSelectedCount (hD := hD) P := by omega
  have hba : a + (b - a) = b := by omega
  have hbalance : (∑ α ∈ classes, e α) = (b : ℤ) - (a : ℤ) := by rw [hdegree]; omega
  have hcutq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  have hcutLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcutLq hx
  have htE := c.originalAmalgamation_strict_normalized_log_zero P W A q v u z hq hv
    hwindow hW hA hcutq' hcutLq' hC hmax j hj hjlen M hstrict hbound K hK hKeq
  have htf := c.originalSchur_normalized_log_from_gap_bound P hB hmax j hj hjB
    M hbound K hK hKeq
  have htT (α : ℚ) := c.originalVirtualClosure_normalized_log_from_gap_bound P Q w hQ
    hB hmax j hj hjB M hbound K hK hKeq α
  have hlog := c.originalComparison_strict_bin_ne_zero P W A Q q v u z w hq hv hwindow
    hW hA hQ hcutq' hcutLq' hC hmax j hj hjlen M hstrict hbound hretain K hK hKeq
    classes e (by rw [hdegree]; omega) b a
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
    classes (fun α => (α : OtherField c.top)) e a b hf0 hW0 hcross hbalance hresidue
  let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  let f := c.normalPolynomialSeries P.schur
  let E := c.normalPolynomialSeries A.schur
  let β := c.normalPolynomialSeries Q.schur
  let T := fun α : ℚ => β - PowerSeries.C (α : OtherField c.top) * f ^ 2
  have hTc : ∀ α ∈ classes, PowerSeries.constantCoeff (T α) ≠ 0 := by
    intro α _
    simpa only [T, β, f, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C,
      c.normalPolynomialSeries_constant] using
      c.originalVirtualClosure_residue_ne_zero P Q w hQ hB hmax α
  have hε0 : (ε : OtherField c.top) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hDε : δ (ε : OtherField c.top) = 0 := by
    apply residueGeneratorDeriv_lower
    exact (residueLowerField c.top K).intCast_mem ε
  have he := coeff_deriv_full_rational_defect δ classes E f β
    (fun α => (α : OtherField c.top)) e (ε : OtherField c.top) a (b - a) (j - 1) (by omega)
    (by simpa only [f, c.normalPolynomialSeries_constant] using hf0)
    (by simpa only [E, c.normalPolynomialSeries_constant] using hE0) hε0 hDε hTc hdegree
    (by simpa only [E, f, β, hba, c.normalPolynomialSeries_constant, map_sub, map_mul,
      map_pow, PowerSeries.constantCoeff_C] using hmatch)
    htE.1 htf.1 (fun α _ => (htT α).1)
  rw [hba] at he
  have hlogs := coeff_deriv_normal_comparison_log_first δ classes E f T e b a
    (j - 1) (by omega)
    (by simpa only [E, c.normalPolynomialSeries_constant] using hE0)
    (by simpa only [f, c.normalPolynomialSeries_constant] using hf0) hTc
    htE.1 htf.1 (fun α _ => (htT α).1)
  dsimp only [δ, E, f, β, T] at he hlogs
  dsimp only at hlog ⊢
  rw [← hlogs] at he
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    have hz := coeff_deriv_full_rational_defect_zero δ classes E f β
      (fun α => (α : OtherField c.top)) e (ε : OtherField c.top) a (b - a) l
      (by simpa only [f, c.normalPolynomialSeries_constant] using hf0)
      hDε hTc hdegree
      (fun k hk => htE.1 k (hk.trans_lt hl))
      (fun k hk => htf.1 k (hk.trans_lt hl))
      (fun α _ k hk => (htT α).1 k (hk.trans_lt hl))
    rw [hba] at hz
    simpa only [δ, E, f, β, originalRationalPrefactor, id_eq] using hz
  · have hρ := c.originalRationalPrefactor_constant_ne_zero P Q w hQ hB hmax classes id e ε hε
    have hn := mul_ne_zero hρ hlog.2
    simpa only [originalRationalPrefactor, id_eq, ← he] using hn
  · have hβAffine := (htT 0).2.2
    simp only [Rat.cast_zero, map_zero, zero_mul, sub_zero] at hβAffine
    have haff := fullRationalDefect_jets_affine
      (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩)
      classes (fun α => (α : OtherField c.top)) e (ε : OtherField c.top)
      f E β a b (j - 1) (by omega) ((residueLowerField c.top K).intCast_mem ε)
      (fun α _ => SubfieldClass.ratCast_mem (residueLowerField c.top K) α)
      htf.2.2 htE.2.2 hβAffine
    simpa only [f, E, β, originalRationalPrefactor, id_eq] using haff

end SkewCornerDescent.Matrix.SelectedCoordinate
