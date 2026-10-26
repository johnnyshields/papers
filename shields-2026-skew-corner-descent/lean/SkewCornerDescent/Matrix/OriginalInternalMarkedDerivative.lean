/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalInverseJets
import SkewCornerDescent.Matrix.OriginalInternalPeriodHeight
import SkewCornerDescent.Matrix.HessenbergMarkedActivityDerivative

/-!
# Actual source normalization for complete marked determinant differentiation

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original period height produces the chosen higher index. Genuine full
source units then supply chosen-generator independence of all normalization
weights, without freezing any normal-dependent inverse jet.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual period-height identity produces the higher-generator index.
Its value is the specified original generator; only its order proof is constructed. -/
def originalInternalPeriodHigherIndex {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    {K : ℕ+ // c.top < K} :=
  ⟨H, by
    have hpos : 0 < d ∧ 0 < r := by
      constructor
      · by_contra hz
        have he : d = 0 := by omega
        simp [he] at hn
      · by_contra hz
        have he : r = 0 := by omega
        simp [he] at hn
    have htotal := c.originalInternal_period_total_gt_top P r d hpos.2 hpos.1 hp
    have hJ := J.pos
    have hlt : (c.top : ℤ) < (H : ℤ) := by omega
    exact_mod_cast hlt⟩

/-- Actual source geometry supplies independence of both the exact selected
subdiagonal and every complete inverse-diagonal weight; no independence is assumed. -/
theorem originalInternal_marked_derivative_inputs {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    δ (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹) = 0 ∧
      ∀ i : Fin (originalSelectedCount (hD := hD) P - 1),
        δ ((c.normalSeries (c.originalInternalResponseMatrix P i i))⁻¹) = 0 := by
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  have htop : c.top < H := K.property
  have hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ) := by
    have hJ := J.pos
    omega
  let δ := residueSeriesGeneratorDeriv c.top ⟨H, ne_of_gt htop⟩
  have hX : δ PowerSeries.X = 0 := by
    unfold δ residueSeriesGeneratorDeriv
    exact powerSeriesCoefficientDerivation_X _ _ _ _
  have ha : residueGeneratorDeriv c.top ⟨H, ne_of_gt htop⟩ c.normalCoefficient⁻¹ = 0 := by
    apply residueGeneratorDeriv_lower
    exact Subfield.inv_mem _ (residueLowerField_mono htop.le c.normalCoordinate_mem_lower.1)
  have hC : δ (PowerSeries.C c.normalCoefficient⁻¹) = 0 := by
    dsimp only [δ]
    rw [residueSeriesGeneratorDeriv_C, ha, map_zero]
  constructor
  · change δ (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹) = 0
    have hprod := @Derivation.leibniz' ℚ
      (PowerSeries (OtherField c.top)) (PowerSeries (OtherField c.top)) _ _ _ _ _
      (inferInstance : Algebra ℚ (PowerSeries (OtherField c.top))).toModule
      δ PowerSeries.X (PowerSeries.C c.normalCoefficient⁻¹)
    change δ (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹) =
      PowerSeries.X * δ (PowerSeries.C c.normalCoefficient⁻¹) +
        PowerSeries.C c.normalCoefficient⁻¹ * δ PowerSeries.X at hprod
    simp only [hX, hC, mul_zero, add_zero] at hprod
    exact hprod
  · intro i
    change δ ((c.normalSeries (c.originalInternalResponseMatrix P i i))⁻¹) = 0
    have hi := c.originalInternal_normal_diagonal_high_zero P hmax r d hn hp H htop hheight i
    have hunit := c.originalInternal_normal_diagonal_ne_zero P (NeZero.pos _) hmax i
    rw [normal_series_deriv_inverse δ _ hunit, hi, mul_zero]

/-- The complete actual internal normalized determinant differentiates into
all marked original permutation activities. Source geometry supplies the higher
index and every normalization independence law; none is an assembly hypothesis. -/
theorem originalInternal_det_marked_derivative {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let w := fun j => (A j j)⁻¹
    δ (A.det * ∏ j, w j) =
      ∑ σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)),
        if (∀ j, j.val ≤ (σ j).val + 1) then
          let upper := Finset.univ.filter (fun j => j.val ≤ (σ j).val)
          let cost := (Finset.univ.filter (fun j => (σ j).val < j.val)).card
          let activity := fun j => A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
          (-1 : PowerSeries (OtherField c.top)) ^ cost *
            (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹) ^ cost *
            ∑ i ∈ upper, (δ (A i (σ i)) * ∏ l ∈ Finset.Icc i (σ i), w l) *
              ∏ j ∈ upper.erase i, activity j
        else 0 := by
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  let w := fun j => (A j j)⁻¹
  obtain ⟨ht, hw⟩ := c.originalInternal_marked_derivative_inputs P hmax r d hn hp J H hH
  exact hessenberg_det_marked_activity_derivative δ A (c.originalInternal_normal_shape P)
    (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹)
    (c.originalInternal_normal_subdiagonal P) ht w hw

/-- The full original normalized determinant has exactly its two complete
marked cost frontiers. Earlier independence and diagonal normalization are
produced from the actual source rather than supplied as coefficient assumptions.

**Differs from the paper's route.** The full marked permutation expansion
isolates the two selected costs before the logarithmic correction, rather than
enumerating connected activity clusters. -/
theorem originalInternal_marked_two_costs {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let w := fun j => (A j j)⁻¹
    let marked := fun σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)) =>
      let upper := Finset.univ.filter (fun j => j.val ≤ (σ j).val)
      let activity := fun j => A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
      ∑ i ∈ upper, (δ (A i (σ i)) * ∏ l ∈ Finset.Icc i (σ i), w l) *
        ∏ j ∈ upper.erase i, activity j
    let m := d * r
    residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      (PowerSeries.coeff m (A.det * ∏ j, w j)) =
      ∑ σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)),
        if (∀ j, j.val ≤ (σ j).val + 1) then
          let cost := (Finset.univ.filter (fun j => (σ j).val < j.val)).card
          if cost = m then
            (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m *
              PowerSeries.constantCoeff (marked σ)
          else if cost + 1 = m then
            (-1 : OtherField c.top) ^ (m - 1) * c.normalCoefficient⁻¹ ^ (m - 1) *
              PowerSeries.coeff 1 (marked σ)
          else 0
        else 0 := by
  classical
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  let w := fun j => (A j j)⁻¹
  let marked := fun σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)) =>
    let upper := Finset.univ.filter (fun j => j.val ≤ (σ j).val)
    let activity := fun j => A j (σ j) * ∏ l ∈ Finset.Icc j (σ j), w l
    ∑ i ∈ upper, (δ (A i (σ i)) * ∏ l ∈ Finset.Icc i (σ i), w l) *
      ∏ j ∈ upper.erase i, activity j
  let m := d * r
  have hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K.val : ℤ) := by
    change d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ)
    have hJ := J.pos
    omega
  have hshort (σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)))
      (hσ : ∀ j, j.val ≤ (σ j).val + 1)
      (hcost : (Finset.univ.filter (fun j => (σ j).val < j.val)).card + 1 < m) :
      marked σ = 0 := by
    dsimp only [marked]
    apply Finset.sum_eq_zero
    intro i hi
    have hiup : i.val ≤ (σ i).val := (Finset.mem_filter.mp hi).2
    have hb := hessenberg_permutation_interval_cost σ hσ i hiup
    have hlen : (σ i).val - i.val + 1 < d * r := by
      change (σ i).val - i.val + 1 < m
      omega
    have hz : δ (A i (σ i)) = 0 :=
      c.originalInternal_normal_entry_short P hmax r d hp K.val K.property hheight
        i (σ i) hiup hlen
    rw [hz, zero_mul, zero_mul]
  have hexp := c.originalInternal_det_marked_derivative P hmax r d hn hp J H hH
  dsimp only
  rw [← residueSeriesGeneratorDeriv_coeff]
  change PowerSeries.coeff m (δ (A.det * ∏ j, w j)) = _
  rw [hexp, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : ∀ j, j.val ≤ (σ j).val + 1
  · simp only [ite_eq_left hσ]
    let cost := (Finset.univ.filter (fun j => (σ j).val < j.val)).card
    change PowerSeries.coeff m ((-1 : PowerSeries (OtherField c.top)) ^ cost *
      (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹) ^ cost * marked σ) = _
    rw [normal_cost_prefactor_coeff]
    by_cases hle : cost ≤ m
    · rw [ite_eq_left hle]
      by_cases hcm : cost = m
      · rw [ite_eq_left hcm, hcm, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      · rw [ite_eq_right hcm]
        by_cases hnext : cost + 1 = m
        · rw [ite_eq_left hnext]
          have he : cost = m - 1 := by omega
          have hs : m - cost = 1 := by omega
          rw [hs, he]
        · rw [ite_eq_right hnext]
          have hzero := hshort σ hσ (by change cost + 1 < m; omega)
          rw [hzero, map_zero, mul_zero]
    · have hcm : cost ≠ m := by omega
      have hnext : cost + 1 ≠ m := by omega
      rw [ite_eq_right hle, ite_eq_right hcm, ite_eq_right hnext]
  · simp only [ite_eq_right hσ, map_zero]

end SkewCornerDescent.Matrix.SelectedCoordinate
