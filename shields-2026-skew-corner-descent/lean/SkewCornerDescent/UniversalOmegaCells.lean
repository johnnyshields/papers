/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.UniversalOmegaSchur
import SkewGluing.CellTableauBridge

/-!
# Universal omega on actual connected cell diagrams

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The full polynomial involution sends the actual connected cell-diagram Schur
function to the actual transposed diagram's function. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- Profile cells are the integer realization of the complete tableau shape. -/
theorem profile_cells_eq_skewDiagram {n : ℕ} (P : Profile n) :
    P.cells = skewDiagram P.lam P.mu := by
  ext c
  constructor
  · intro hc
    rcases c with ⟨r, s⟩
    have hi := P.row_of_mem_cells hc
    have hj := P.nonneg_col_of_mem_cells hc
    change 0 ≤ r at hi
    change 0 ≤ s at hj
    obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    exact (mem_skewDiagram_nat i j).mpr ((P.mem_cells_nat i j).mp hc)
  · intro hc
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram hc
    exact (P.mem_cells_nat i j).mpr ((mem_skewDiagram_nat i j).mp hc)

/-- Transposition of the actual integer cells agrees with transposition of the
complete Young shapes, retaining every cell. -/
theorem transpose_skewDiagram (lam mu : YoungDiagram) :
    transpose (skewDiagram lam mu) = skewDiagram lam.transpose mu.transpose := by
  ext c
  constructor
  · intro hc
    have hc' := mem_transpose.mp hc
    obtain ⟨i, j, hij⟩ := nat_cell_of_mem_skewDiagram hc'
    have he : c = ((j : ℤ), (i : ℤ)) := by
      have h := congrArg Prod.swap hij
      simpa only [Prod.swap_swap, Prod.swap_prod_mk] using h
    subst c
    simp only [Prod.swap_prod_mk] at hc'
    rw [mem_skewDiagram_nat] at hc' ⊢
    simpa only [Shields.mem_skewCells, YoungDiagram.mem_transpose,
      Prod.swap_prod_mk] using hc'
  · intro hc
    obtain ⟨i, j, rfl⟩ := nat_cell_of_mem_skewDiagram hc
    rw [mem_transpose]
    simp only [Prod.swap_prod_mk]
    rw [mem_skewDiagram_nat]
    rw [mem_skewDiagram_nat] at hc
    simpa only [Shields.mem_skewCells, YoungDiagram.mem_transpose,
      Prod.swap_prod_mk] using hc

/-- Swapping coordinates commutes with translating the complete actual diagram. -/
theorem transpose_translate (v : ℤ × ℤ) (D : Diagram) :
    transpose (translate v D) = translate v.swap (transpose D) := by
  ext c
  rw [mem_transpose, mem_translate, mem_translate, mem_transpose]
  rfl

/-- Universal omega transports the actual normalized profile Schur function
to the full transposed cell diagram. -/
theorem schurInvolution_profile_cells {n : ℕ} (P : Profile n) :
    schurInvolution P.schur =
      cellSchur (transpose P.cells) (isSkew_transpose P.isSkew_cells) := by
  apply eq_of_evalComplete_eq
  intro a
  rw [evalComplete_schurInvolution_profile]
  have hc := isConnectedSkew_transpose P.isConnectedSkew_cells
  have he : transpose P.cells = skewDiagram P.lam.transpose P.mu.transpose := by
    rw [profile_cells_eq_skewDiagram, transpose_skewDiagram]
  have hd : IsConnectedSkew (skewDiagram P.lam.transpose P.mu.transpose) := he ▸ hc
  rw [cellSchur_congr he _ hd.1]
  exact (aeval_cellSchur_skewDiagram
    (YoungDiagram.transpose_mono P.mu_le_lam) hd a (varAlphabet a)).symm

/-- The original universal polynomial involution transports every actual
connected skew diagram, independently of its chosen profile and translation. -/
theorem schurInvolution_cellSchur {D : Diagram} (hD : IsConnectedSkew D) :
    schurInvolution (cellSchur D hD.1) =
      cellSchur (transpose D) (isSkew_transpose hD.1) := by
  obtain ⟨n, P, v, hv⟩ := hD.exists_profile_cells
  rw [cellSchur_eq_profile hD P v hv, schurInvolution_profile_cells]
  have ht : transpose D = translate v.swap (transpose P.cells) := by
    rw [hv, transpose_translate]
  rw [cellSchur_congr ht _ (isSkew_translate _ (isSkew_transpose P.isSkew_cells)),
    cellSchur_translate]

end SkewCornerDescent
