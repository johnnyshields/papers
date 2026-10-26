/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalAmalgamationSpan
import SkewCornerDescent.Matrix.OriginalAmalgamationGapPeriod
import SkewCornerDescent.Matrix.OriginalAmalgamationCyclicInventory
import SkewCornerDescent.Matrix.OriginalSchurAffine
import SkewCornerDescent.CyclicWordProjection

/-!
# The fresh coefficient of the full actual amalgamation Schur polynomial

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). Literal overlap,
private cuts, and the original corner powers produce the union count, component span
bound, completed-gap period, and extra cyclic inventory. No union period or normal-jet
independence is supplied as a hypothesis. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original amalgamation coefficient is the source linear inventory plus its full
extra cyclic inventory. Corner multiplicities and literal windows supply every union premise. -/
theorem originalAmalgamation_normalized_log_from_source {n m s : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
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
      (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) 1 r 0) :
    let E := c.normalPolynomialSeries A.schur
    let cycle := finiteWordCycle (n := originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W) (c.originalInternalResidue P) (by omega)
    (∀ l, l < d → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff l E) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff d
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff E)⁻¹ * E))) =
      ((-1 : OtherField c.top) ^ d * (c.normalCoefficient)⁻¹ ^ d) *
        (linearInverseWindowSum (c.originalInternalResidue P) (d + 1) +
          inverseWindowSum cycle (d + 1)) ∧
    jetsAffineOver (residueLowerField c.top K) (residueGenerator c.top ⟨K, ne_of_gt hK⟩) E d := by
  classical
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
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  let : NeZero r := ⟨by omega⟩
  have hrB : r ∣ originalSelectedCount (hD := hD) P := by
    rw [hcountP]; exact dvd_mul_left _ _
  have hrC : r ∣ originalSelectedCount (hD := hD) W := by
    rw [hcountW]; exact dvd_mul_left _ _
  have hrle := Nat.le_of_dvd hB hrB
  have hcutq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  have hcutLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcutLq hx
  have hinv := originalAmalgamation_selected_inventory (hD := hD) P W A q v u z
    hv hwindow hW hA
  have hBA : 0 < originalSelectedCount (hD := hD) A := by omega
  let : NeZero (originalSelectedCount (hD := hD) A) := ⟨by omega⟩
  have hrA : r ∣ originalSelectedCount (hD := hD) A := by
    have hdvd : r ∣ 2 * originalSelectedCount (hD := hD) P := hrB.mul_left 2
    rw [← hinv] at hdvd
    simpa only [Nat.add_sub_cancel] using Nat.dvd_sub hdvd hrC
  let cycleR := finiteWordCycle (c.originalCompletedGap P) hrle
  have hwP := c.originalCompletedGap_period_cycle P r hrle hp
  have hwA := c.originalAmalgamation_completed_gap_cycle P W A q v u z hq hv
    hwindow hW hA hcutq' hcutLq' hC r hrle hrB hrC hp
  have hpA := cyclicWord_period_of_projection (c.originalCompletedGap A) cycleR hrA hwA
  have hsumA := cyclicWord_windowSum_projection (c.originalCompletedGap A) cycleR hrA hwA r
  have hsumP := cyclicWord_windowSum_projection (c.originalCompletedGap P) cycleR hrB hwP r
  have hKA : (K : ℤ) = (c.top : ℤ) + k • windowSum
      (fun z => c.originalCompletedGap A ((ZMod.finEquiv _).symm z)) 1 r 0 := by
    rw [hsumA, ← hsumP]
    exact hKeq
  have hmaxA := originalAmalgamation_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  have he := c.originalSchur_normalized_log_linear_periodic A hBA hmaxA
    r k d hd (by omega) hlen hpA K hK hKA
  dsimp only at he ⊢
  refine ⟨he.1, ?_, c.originalSchur_jets_affine_periodic A hBA hmaxA
    r k d hd (by omega) hlen hpA K hK hKA⟩
  rw [he.2, c.originalAmalgamation_linear_inventory P W A q v u z hq hv
    hwindow hW hA hcutq hcutLq hC hproper (d + 1) (by omega)]

end SkewCornerDescent.Matrix.SelectedCoordinate
