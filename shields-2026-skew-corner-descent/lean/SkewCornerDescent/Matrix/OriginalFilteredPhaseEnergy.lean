/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseSquareEnergy

/-!
# Nonzero filtered phase energy over original response classes

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
The attained maximal-margin discrepancy survives the complete finite sum of
squares, with every wrapped occurrence and actual response-class weight.
A produced common positive regular specialization proves nonvanishing; no
positivity of derived response coordinates is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The maximal-margin phase energy is nonzero when an actual discrepancy
attains that margin.  All scalar weights are genuine original response
classes, and every wrapped occurrence remains in the finite square sum. -/
theorem originalResponseClasses_filtered_phase_energy_ne_zero {n r b : ℕ} [NeZero b]
    (P : Profile n) (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (incoming : Fin r → ZMod b → Polynomial (OtherField c.top))
    (weight : Fin r → c.OriginalResponseClass P) (d : ℕ) (K : Fin r → ℕ)
    (choices : Fin r → Option ℕ) (J : ℕ+)
    (hattain : ∃ i w, choices i = some w ∧ (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) ∧
      ∃ k, (incoming i k).coeff w - (incoming i (k + (d : ZMod b))).coeff w ≠ 0) :
    (∑ i : Fin r, match choices i with
      | none => 0
      | some w => if (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
          ((1/2 : OtherField c.top) * ∑ k : ZMod b,
            ((incoming i k).coeff w - (incoming i (k + (d : ZMod b))).coeff w)^2) *
              (weight i).val⁻¹
        else 0) ≠ 0 := by
  classical
  let η := fun (i : Fin r) (k : ZMod b) => match choices i with
    | none => 0
    | some w => if (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
        (incoming i k).coeff w - (incoming i (k + (d : ZMod b))).coeff w
      else 0
  have hη : ∃ p : Fin r × ZMod b, η p.1 p.2 ≠ 0 := by
    obtain ⟨i, w, hi, hmargin, k, hk⟩ := hattain
    refine ⟨(i,k), ?_⟩
    simpa only [η, hi, ite_eq_left hmargin] using hk
  have hs := c.originalResponseClasses_square_energy_ne_zero P hB hmax
    (fun p : Fin r × ZMod b => weight p.1) (fun p => η p.1 p.2) hη
  have heq : (∑ i : Fin r, match choices i with
        | none => 0
        | some w => if (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
            ((1/2 : OtherField c.top) * ∑ k : ZMod b,
              ((incoming i k).coeff w - (incoming i (k + (d : ZMod b))).coeff w)^2) *
                (weight i).val⁻¹
          else 0) =
      (1/2 : OtherField c.top) * (∑ p : Fin r × ZMod b, (η p.1 p.2)^2 / (weight p.1).val) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases hi : choices i with
    | none => simp [η, hi]
    | some w =>
      by_cases hm : (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ)
      · simp only [hi, ite_eq_left hm, η]
        simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      · simp [η, hi, hm]
  rw [heq]
  exact mul_ne_zero (by norm_num) hs

end SkewCornerDescent.Matrix.SelectedCoordinate
