/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.RealResponseChart
import SkewCornerDescent.Matrix.OriginalHessenbergTops
import SkewCornerDescent.Matrix.OriginalBoundedSchurFrontier
import SkewCornerDescent.PositiveReciprocalInventories

/-!
# Nonvanishing positive inventories of actual retained responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Every
complete original diagonal response acquires its faithful rational representative
from elimination. One simultaneous monic-positive assignment then witnesses that
an inhabited inverse-product context cannot vanish. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every inhabited finite inverse-product inventory of complete original diagonal
responses is nonzero. The common positive assignment is constructed, not assumed. -/
theorem originalHessenberg_inverse_inventory_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    {ι σ : Type*} (s : Finset ι) (hs : s.Nonempty) (positions : ι → Finset σ)
    (letter : ι → σ → Fin (originalSelectedCount (hD := hD) P + 1)) :
    (∑ i ∈ s, ∏ j ∈ positions i,
      (c.regularResidue (c.originalHessenbergResponse P (letter i j) (letter i j)))⁻¹) ≠ 0 := by
  classical
  let K := fun i : Fin (originalSelectedCount (hD := hD) P + 1) =>
    c.originalHessenbergTop P hB i i le_rfl
  have hNK : ∀ i, c.top < K i := by
    intro i
    have hg := c.originalHessenbergDistance_gt_top P hB i i le_rfl
    have he := c.originalHessenbergTop_coe P hB i i le_rfl
    exact_mod_cast (show (c.top : ℤ) < (K i : ℤ) by dsimp only [K]; omega)
  have hindex : ∀ i,
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (originalHessenbergRows P i))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (originalHessenbergCols P i))) =
        (K i : ℤ) := fun i => (c.originalHessenbergTop_coe P hB i i le_rfl).symm
  obtain ⟨p, q, hp, hq, hq0, hqreal, he⟩ := c.originalResponses_real_representatives
    (fun _ => n) (fun _ => P) (originalHessenbergRows P) (originalHessenbergCols P)
    K hNK hindex (fun _ => hmax)
  obtain ⟨x, hx, hsigned⟩ := exists_signed_rational_triangular_family
    (fun i => (K i : ℕ)) (fun i => realResiduePolynomial c.top (p i))
    (fun i => realResiduePolynomial c.top (q i)) (c.top : ℕ)
    (fun i => (hNK i).le) hp hq hqreal true
  let ιR := algebraMap (OtherPolynomial c.top) (OtherField c.top)
  let φ : OtherPolynomial c.top →+* ℝ :=
    (MvPolynomial.eval x).comp (realResiduePolynomial c.top)
  let num := fun i => MvPolynomial.X ⟨K i, ne_of_gt (hNK i)⟩ * q i + p i
  have hden : ∀ i, ιR (q i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hq0 i)
  have hresponse : ∀ i, c.regularResidue (c.originalHessenbergResponse P i i) =
      ιR (num i) / ιR (q i) := by
    intro i
    change c.regularResidue (c.originalLocalResponse P (originalHessenbergRows P i)
      (originalHessenbergCols P i)) = _
    rw [he i]
    change residueGenerator c.top ⟨K i, ne_of_gt (hNK i)⟩ + ιR (p i) / ιR (q i) = _
    simp only [num, map_add, map_mul]
    change residueGenerator c.top ⟨K i, ne_of_gt (hNK i)⟩ + ιR (p i) / ιR (q i) =
      (residueGenerator c.top ⟨K i, ne_of_gt (hNK i)⟩ * ιR (q i) + ιR (p i)) / ιR (q i)
    field_simp [hden i]
  have hnF : ∀ i, ιR (num i) ≠ 0 := by
    intro i hz
    have hunit := c.originalHessenberg_residue_ne_zero P hB hmax i
    rw [hresponse i, hz, zero_div] at hunit
    exact hunit rfl
  have hpositive : ∀ i, 0 < φ (num i) / φ (q i) := by
    intro i
    have hxi := hx i
    have hsign := hsigned i
    change 0 < rationalTriangularResponse (K i : ℕ)
      (realResiduePolynomial c.top (p i)) (realResiduePolynomial c.top (q i)) x at hsign
    have hv : φ (num i) / φ (q i) = rationalTriangularResponse (K i : ℕ)
        (realResiduePolynomial c.top (p i)) (realResiduePolynomial c.top (q i)) x := by
      simp only [num, map_add, map_mul, φ, RingHom.comp_apply]
      have hX : MvPolynomial.eval x
          (realResiduePolynomial c.top (MvPolynomial.X ⟨K i, ne_of_gt (hNK i)⟩)) = x (K i) := by
        simp [realResiduePolynomial]
      rw [hX]
      unfold rationalTriangularResponse
      field_simp [hxi]
    rw [hv]
    exact hsign
  have hnonzero := sum_prod_inv_ne_zero_of_positive_specialization ιR φ
    (IsFractionRing.injective _ _) num q hnF hpositive s hs positions letter
  simpa only [← hresponse] using hnonzero

/-- An actual interval attaining the protected distance makes the complete
filtered inventory nonzero on the constructed common positive chamber. -/
theorem originalFilteredIntervalInventory_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (K : ℕ+)
    (hretain : ∃ i k : Fin (originalSelectedCount (hD := hD) P + 1),
      i.val ≤ k.val ∧ k.val - i.val = j - 1 ∧
        originalHessenbergDistance (hD := hD) P i k = (K : ℤ)) :
    c.originalFilteredIntervalInventory P j K ≠ 0 := by
  classical
  let starts := Finset.univ.filter
    (fun p : Fin (originalSelectedCount (hD := hD) P + 1) ×
        Fin (originalSelectedCount (hD := hD) P + 1) =>
      p.1.val ≤ p.2.val ∧ p.2.val - p.1.val = j - 1 ∧
        originalHessenbergDistance (hD := hD) P p.1 p.2 = (K : ℤ))
  have hs : starts.Nonempty := by
    obtain ⟨i, k, h⟩ := hretain
    exact ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have hn := c.originalHessenberg_inverse_inventory_ne_zero P hB hmax starts hs
    (fun p => Finset.Icc p.1 p.2) (fun _ l => l)
  simpa only [starts, Finset.sum_filter, Fintype.sum_prod_type,
    originalFilteredIntervalInventory] using hn

end SkewCornerDescent.Matrix.SelectedCoordinate
