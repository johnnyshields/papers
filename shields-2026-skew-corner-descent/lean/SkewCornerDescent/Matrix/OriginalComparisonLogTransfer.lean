/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalAmalgamationNormalTransfer
import SkewCornerDescent.Matrix.OriginalVirtualCycleTransfer
import SkewCornerDescent.Matrix.NormalComparisonCoefficient

/-!
# Signed original determinant logarithm from literal diagram geometry

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Every source, amalgamation and virtual determinant coefficient is supplied by its
actual diagram assembly. Signed class balance cancels the linear inventory without
discarding earlier intrinsic coefficients. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Signed balance cancels the common source inventory for arbitrary class multiplicities. -/
theorem signed_linear_inventory_cancel {F : Type*} [Field F] {ι : Type*}
    (s : Finset ι) (e : ι → ℤ) (b v : ℕ) (L P : F) (Q : ι → F)
    (hbalance : (∑ i ∈ s, e i) = (b : ℤ) - (v : ℤ)) :
    (b : F) * (L + P) - (v : F) * L - ∑ i ∈ s, (e i : F) * (L + Q i) =
      (b : F) * P - ∑ i ∈ s, (e i : F) * Q i := by
  have hc : (∑ i ∈ s, (e i : F)) = (b : F) - (v : F) := by
    have he := congrArg (fun x : ℤ => (x : F)) hbalance
    simpa only [Int.cast_sum, Int.cast_sub, Int.cast_natCast] using he
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hc]
  ring

/-- A common contraction coefficient respects the same signed inventory cancellation. -/
theorem scaled_signed_linear_inventory_cancel {F : Type*} [Field F] {ι : Type*}
    (s : Finset ι) (e : ι → ℤ) (b v : ℕ) (η L P : F) (Q : ι → F)
    (hbalance : (∑ i ∈ s, e i) = (b : ℤ) - (v : ℤ)) :
    (b : F) * (η * (L + P)) - (v : F) * (η * L) -
        ∑ i ∈ s, (e i : F) * (η * (L + Q i)) =
      η * ((b : F) * P - ∑ i ∈ s, (e i : F) * Q i) := by
  simp_rw [mul_left_comm (e _ : F)]
  rw [← Finset.mul_sum]
  calc
    _ = η * ((b : F) * (L + P) - (v : F) * L -
        ∑ i ∈ s, (e i : F) * (L + Q i)) := by ring
    _ = _ := by rw [signed_linear_inventory_cancel s e b v L P Q hbalance]

namespace SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full original comparison logarithm has the actual signed cyclic inventory.
Only the paper's literal geometry, corner powers, standing periodicity and signed
balance are inputs; the fresh coefficient and all earlier independence are derived. -/
theorem originalComparison_normalized_log_from_source {n m s t : ℕ} {ι : Type*}
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
    (k d : ℕ) (hd : 0 < d) (hdB : d < originalSelectedCount (hD := hD) P)
    (hlen : d + 1 = k * r)
    (hp : Function.Periodic
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hKeq : (K : ℤ) = (c.top : ℤ) + k • windowSum
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0)
    (classes : Finset ι) (α : ι → ℚ) (e : ι → ℤ) (vexp : ℕ)
    (hbalance : (∑ i ∈ classes, e i) = (b : ℤ) - (vexp : ℤ)) :
    let f := c.normalPolynomialSeries P.schur
    let E := c.normalPolynomialSeries A.schur
    let T := fun i => c.normalPolynomialSeries Q.schur -
      PowerSeries.C (α i : OtherField c.top) * f ^ 2
    let R := normalComparisonSeries classes E f T e b vexp
    let cycle := finiteWordCycle (n := originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W) (c.originalInternalResidue P) (by omega)
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    (∀ l, l < d → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l R) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff d
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff R)⁻¹ * R))) =
      ((-1 : OtherField c.top) ^ d * (c.normalCoefficient)⁻¹ ^ d) *
        ((b : OtherField c.top) * inverseWindowSum cycle (d + 1) -
          ∑ i ∈ classes, (e i : OtherField c.top) * inverseWindowSum
            (completeResponseCycle (c.originalInternalResidue P)
              (c.originalVirtualCentralResponse P Q middle (α i))) (d + 1)) := by
  classical
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have htE := c.originalAmalgamation_normalized_log_from_source P W A q v u z hq hv
    hwindow hW hA hcutq hcutLq hC hmax Λ b a r hab hrpos hr hKU hKW
    k d hd hdB hlen hp K hK hKeq
  have htf := c.originalSchur_normalized_log_linear_periodic P hB hmax
    r k d hd hdB hlen hp K hK hKeq
  have htT (i : ι) :=
    c.originalVirtualClosure_normalized_log_cycle P Q w hQ hB hmax
      r k d hd hdB hlen hp K hK hKeq (α i)
  have hinv := originalAmalgamation_selected_inventory (hD := hD) P W A q v u z
    hv hwindow hW hA
  have hmaxA := originalAmalgamation_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  have hcountP : originalSelectedCount (hD := hD) P = b * r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hcountW : originalSelectedCount (hD := hD) W = a * r := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr]
  have hproper : originalSelectedCount (hD := hD) W <
      originalSelectedCount (hD := hD) P := by
    rw [hcountP, hcountW]
    exact Nat.mul_lt_mul_of_pos_right hab hrpos
  have hE0 := c.originalSchur_residue_ne_zero A (by omega) hmaxA
  have hf0 := c.originalSchur_residue_ne_zero P hB hmax
  let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  let f := c.normalPolynomialSeries P.schur
  let E := c.normalPolynomialSeries A.schur
  let T := fun i => c.normalPolynomialSeries Q.schur -
    PowerSeries.C (α i : OtherField c.top) * f ^ 2
  have hTc : ∀ i ∈ classes, PowerSeries.constantCoeff (T i) ≠ 0 := by
    intro i _
    simpa only [T, f, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C,
      c.normalPolynomialSeries_constant] using
      c.originalVirtualClosure_residue_ne_zero P Q w hQ hB hmax (α i)
  dsimp only at htE htf ⊢
  constructor
  · intro l hl
    exact coeff_deriv_normal_comparison_zero δ classes E f T e b vexp l
      (by simpa only [f, c.normalPolynomialSeries_constant] using hf0) hTc
      (fun j hj => htE.1 j (hj.trans_lt hl))
      (fun j hj => htf.1 j (hj.trans_lt hl))
      (fun i _ j hj => (htT i).1 j (hj.trans_lt hl))
  · have he := coeff_deriv_normal_comparison_log_first δ classes E f T e b vexp d hd
      (by simpa only [E, c.normalPolynomialSeries_constant] using hE0)
      (by simpa only [f, c.normalPolynomialSeries_constant] using hf0) hTc
      htE.1 htf.1 (fun i _ => (htT i).1)
    dsimp only [δ, E, f, T] at he
    rw [he, htE.2.1, htf.2]
    have hs := Finset.sum_congr (s₁ := classes) (s₂ := classes) rfl (fun i _ =>
      congrArg (fun x => (e i : OtherField c.top) * x) (htT i).2)
    rw [hs]
    exact scaled_signed_linear_inventory_cancel classes e b vexp _ _ _ _ hbalance

end SelectedCoordinate

end SkewCornerDescent.Matrix
