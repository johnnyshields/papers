/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalMultiplicity
import SkewCornerDescent.Matrix.OriginalWindowUnitBlocks
import SkewGluing.ComponentOrders

/-!
# Exact original unit geometry of a pure corner inventory

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
A nonempty actual component factor divides the complete original cofactor.
In a pure selected-prime power it is associated to that prime and hence
selected. Every other original block is therefore a single actual
gap-zero unit vertex, never a discarded empty matrix. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every positive actual block is selected when the complete original
corner inventory is a pure power of the selected prime. -/
theorem originalPure_positive_block_selected {n : ℕ} (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k) (u : OriginalBlocks P)
    (hu : P.zeta u.val.castSucc < P.xi u.val.succ) :
    originalBlockSelected (hD := hD) P u := by
  classical
  have hf : Irreducible (originalBlockPolynomial P u) := by
    rw [originalBlockPolynomial, interior_block_det_eq_profile P u.val hu]
    exact irreducible_schur _ (interiorBlockProfile P u.val hu)
  have hd : originalBlockPolynomial P u ∣ cellSchur D hD.1 ^ k := by
    rw [← hK, interior_det_eq_original_product]
    exact Finset.dvd_prod_of_mem (originalBlockPolynomial P) (Finset.mem_univ u)
  have hψ : originalBlockPolynomial P u ∣ cellSchur D hD.1 := hf.prime.dvd_of_dvd_pow hd
  change cellSchur D hD.1 ∣ originalBlockPolynomial P u
  exact (hf.associated_of_dvd (irreducible_cellSchur hD) hψ).symm.dvd

/-- No positive nonselected component remains in a pure original corner inventory. -/
theorem originalPure_nonselected_empty {n : ℕ} (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k) (u : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u) :
    P.xi u.val.succ = P.zeta u.val.castSucc := by
  have hle := P.zeta_le_xi_succ u.val
  by_contra hn
  exact hu (originalPure_positive_block_selected P k hK u (by omega))

/-- Every nonselected original block in the pure inventory is exactly
one genuine gap-zero unit pivot. -/
theorem originalPure_nonselected_single_vertex {n : ℕ} (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k) (u : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u) :
    P.xi u.val.succ = P.zeta u.val.castSucc ∧ originalRemovedSize (hD := hD) P u = 1 := by
  have he := originalPure_nonselected_empty P k hK u hu
  refine ⟨he, ?_⟩
  simp only [originalRemovedSize, ite_eq_right hu, interior_empty_block_length P u.val he, zero_add]

/-- The complete pure original cofactor supplies the maximal component-span
bound; no separate maximal-component hypothesis is needed in the pure domain. -/
theorem originalPure_component_span (c : SelectedCoordinate D hD) {n : ℕ}
    (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k) :
    ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ) := by
  have he : cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior =
      cellSchur D hD.1 ^ k := by
    rw [← P.minorDet_eq_interiorSchur]
    exact hK
  intro C hC
  have hd := component_cellSchur_dvd P.isConnectedSkew_cells.1.interior hC
  rw [he] at hd
  have hb := polynomialSpan_le_of_dvd (pow_ne_zero k (cellSchur_ne_zero D hD.1)) hd
  rw [polynomialSpan_cellSchur (isConnectedSkew_component P.isConnectedSkew_cells.1.interior hC)]
    at hb
  have ht : polynomialSpan (cellSchur D hD.1) = (c.top : ℕ) :=
    (polynomialSpan_cellSchur hD).trans c.span_eq.symm
  exact hb.trans ((polynomialSpan_pow_le _ k).trans ht.le)

end SkewCornerDescent.Matrix.SelectedCoordinate
