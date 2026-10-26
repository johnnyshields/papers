/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalHessenberg

/-!
# Original selected endpoint geometry

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:component-elimination`). Actual selected
endpoints have the selected top distance. The two exterior caps and distinct selected gaps
strictly exceed that top. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- A genuine original block break strictly separates the lower source endpoints. -/
theorem interior_block_endpoint_separation {n : ℕ} (P : Profile n) (i j : Fin n)
    (hlt : interiorBlock P j < interiorBlock P i) : P.xi i.succ < P.zeta j.castSucc := by
  obtain ⟨k, hk, hjk, hki⟩ := exists_interiorCut_of_block_lt P i j hlt
  have hb := (Finset.mem_filter.mp hk).2.2
  have hr := P.xi_strictAnti.antitone (show k.succ ≤ i.succ by
    change k.val + 1 ≤ i.val + 1
    have h := Fin.le_def.mp hki
    omega)
  have hc := P.zeta_strictAnti.antitone
    (show j.castSucc ≤ (previousIndex k).castSucc by
      change j.val ≤ k.val - 1
      have h := Fin.lt_def.mp hjk
      omega)
  omega

namespace SelectedCoordinate

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual selection supplies the literal endpoint distance of the selected prime. -/
theorem originalSelected_endpoint_distance {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    P.xi b.val.val.succ - P.zeta (interiorBlockLast P b.val.val).castSucc = (c.top : ℤ) := by
  let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  have hx := congrFun (interiorSliceProfile_beta P _ _ _ (interiorBlock_slice_same P b.val.val)
    (interiorBlock_first_nonempty P b.val.val
      (originalBlockSelected_nonempty P b.val b.property))).1 0
  change Q.xi 0 = P.xi (interiorSliceIndex _ _ _ 0).succ -
    P.zeta (interiorSliceIndex _ _ _ (Fin.last _)).castSucc at hx
  have hf := (originalBlockInterval_first P b.val.val).trans b.val.property
  rw [hf, originalBlockInterval_last] at hx
  have ht := Q.topVar_coe
  rw [originalSelectedProfile_top P b c] at ht
  exact hx.symm.trans ht.symm

/-- True first-cap distance, from the exterior top row to a selected literal last column. -/
def originalFirstCapDistance {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) : ℤ :=
  P.xi 0 - P.zeta (interiorBlockLast P b.val.val).castSucc

/-- True last-cap distance, from a selected literal first row to the exterior last column. -/
def originalLastCapDistance {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) : ℤ :=
  P.xi b.val.val.succ - P.zeta (Fin.last n)

/-- The true first cap has a protected top strictly above the selected generator. -/
theorem originalFirstCapDistance_gt_top {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) : (c.top : ℤ) < originalFirstCapDistance P b := by
  have ht := c.originalSelected_endpoint_distance P b
  have hx := P.xi_strictAnti (show (0 : Fin (n + 1)) < b.val.val.succ by
    change 0 < b.val.val.val + 1
    omega)
  unfold originalFirstCapDistance
  omega

/-- The true last cap has a protected top strictly above the selected generator. -/
theorem originalLastCapDistance_gt_top {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) : (c.top : ℤ) < originalLastCapDistance P b := by
  have ht := c.originalSelected_endpoint_distance P b
  have hz := P.zeta_strictAnti (Fin.castSucc_lt_last (interiorBlockLast P b.val.val))
  unfold originalLastCapDistance
  omega

/-- Actual distinct selected component gaps exceed the selected top, including tied primes. -/
theorem originalSelected_gap_gt_top {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hlt : interiorBlock P b.val.val < interiorBlock P d.val.val) :
    (c.top : ℤ) < P.zeta (interiorBlockLast P b.val.val).castSucc -
      P.zeta (interiorBlockLast P d.val.val).castSucc := by
  have ht := c.originalSelected_endpoint_distance P d
  have he := interior_block_endpoint_separation P d.val.val (interiorBlockLast P b.val.val)
    (by rw [interiorBlockLast_label]; exact hlt)
  omega

end SelectedCoordinate
end SkewCornerDescent.Matrix
