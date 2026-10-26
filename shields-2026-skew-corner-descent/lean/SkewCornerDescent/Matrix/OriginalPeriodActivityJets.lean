/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalPeriodGradient
import SkewCornerDescent.Matrix.OriginalInternalInverseJets
import SkewCornerDescent.Matrix.NormalIntervalActivityJets

/-!
# Actual high period-activity contribution of complete denominator jets

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full source produces its high numerator gradient, every diagonal's high
independence and every unit residue. The first inverse-product jet therefore
retains all original slopes, with no gradient or inverse-jet premise supplied.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual period response's high first denominator jet is its raw normalized
selected gradient times the complete negative diagonal slope sum. Every supplier
is called on the unchanged original source. -/
theorem original_period_activity_high_inverse_jet {n m : ℕ} (P : Profile n) (W : Profile m)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hn : 2 ≤ d * r)
    (hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = r * d)
    (hresponse : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      j.val = i.val + r → c.originalInternalResidue P i = c.originalInternalResidue P j)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + d * r)
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ))
    (s : Finset (Fin (originalSelectedCount (hD := hD) P - 1))) :
    let p := fun k => c.normalSeries (c.originalInternalResponseMatrix P k k)
    let response := c.normalSeries (c.originalLocalResponse P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t)))
    let γ := c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))
    residueGeneratorDeriv c.top
      ⟨H, by
        have h := c.originalInternal_period_total_gt_top P r d hr hd hp
        have hpos := J.pos
        have hlt : (c.top : ℤ) < (H : ℤ) := by omega
        exact ne_of_gt (show c.top < H by exact_mod_cast hlt)⟩
      (PowerSeries.coeff 1 (response * ∏ k ∈ s, (p k)⁻¹)) =
      -γ * (∏ k ∈ s, (PowerSeries.constantCoeff (p k))⁻¹) *
        ∑ k ∈ s, PowerSeries.coeff 1 (p k) * (PowerSeries.constantCoeff (p k))⁻¹ := by
  dsimp only
  have htotal := c.originalInternal_period_total_gt_top P r d hr hd hp
  have hHH : c.top < H := by
    have hpos := J.pos
    have hlt : (c.top : ℤ) < (H : ℤ) := by omega
    exact_mod_cast hlt
  have hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ) := by
    have hpos := J.pos
    omega
  rw [← residueSeriesGeneratorDeriv_coeff]
  apply normal_activity_amplitude_gradient_coeff_one
  · intro k _
    exact c.originalInternal_normal_diagonal_ne_zero P (NeZero.pos _) hmax k
  · intro k _
    exact c.originalInternal_normal_diagonal_high_zero P hmax r d hn hp H hHH hheight k
  · exact c.original_period_response_normal_gradient P W q u v hv hW hwindow hq hLq hC
      r d hr hd hdiff hresponse hp i t ht J H hH

end SkewCornerDescent.Matrix.SelectedCoordinate
