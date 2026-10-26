/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.RowBands
import SkewGluing.CofactorAssembly

/-!
# Schur factorization of actual row interiors

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:row-cofactor`).  The factors are obtained from the actual
separated cell union, not assumed as normalization data.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- Translation invariance evaluates every actual row factor. -/
theorem IsLegal.rowPiece_schur_product (h : ω.IsLegal) (hW : ω.W.Nonempty) (m : ℕ) :
    (∏ i : RowPieceIndex m, cellSchur (ω.rowPiece m i) (h.isSkew_rowPiece hW m i)) =
      ω.capTheta h hW * ω.middleCofactor h hW ^ m * ω.hatMarkB h hW ^ (m - 1) := by
  classical
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_bool]
  simp only [rowPiece]
  simp_rw [cellSchur_translate ω.upperCap (h.isSkew_upperCap hW),
    cellSchur_translate (diagramInterior ω.middle) (h.middle_connected hW).1.interior,
    cellSchur_translate ω.hatMarkWindow (h.isSkew_hatMarkWindow hW)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  dsimp only [capTheta, middleCofactor, hatMarkB]
  ring

/-- The actual interior function of an arbitrary nonempty marked row has its cap product. -/
theorem IsLegal.interiorSchur_rowCopies (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) :
    cellSchur (diagramInterior (ω.rowCopies m))
        (h.isConnectedSkew_rowCopies hW m hm).1.interior =
      ω.capTheta h hW * ω.middleCofactor h hW ^ m * ω.hatMarkB h hW ^ (m - 1) := by
  classical
  have hp := cellSchur_biUnion Finset.univ (ω.rowPiece m)
    (h.isSkew_rowPiece hW m) (h.isSkew_rowPiece_union hW hm)
    (fun i _ j _ hij => h.rowPiece_disjoint hW hm hij)
    (fun i _ j _ hij x hx y hy => h.rowPiece_noAdj hW hm hij hx hy)
  rw [cellSchur_congr (h.rowPiece_union_eq_interior hW hm) _
    (h.isConnectedSkew_rowCopies hW m hm).1.interior] at hp
  exact hp.trans (h.rowPiece_schur_product hW m)

/-- The cap product is the actual cofactor of the actual horizontal-row composition. -/
theorem IsLegal.interiorSchur_compose_horizontalRow (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) :
    cellSchur (diagramInterior (ω.compose (horizontalRow m)))
        (h.isConnectedSkew_compose_horizontalRow hW hm).1.interior =
      ω.capTheta h hW * ω.middleCofactor h hW ^ m * ω.hatMarkB h hW ^ (m - 1) := by
  simpa only [ω.compose_horizontalRow hm] using h.interiorSchur_rowCopies hW hm

/-- The largest-generator coefficient of the actual row is the proved cap product. -/
theorem IsLegal.rowSchur_corner (h : ω.IsLegal) (hW : ω.W.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ L : ℕ+, (L : ℕ) = span (ω.rowCopies m) ∧
      ∃ R ∈ MvPolynomial.supported ℤ {k : ℕ+ | k < L},
        cellSchur (ω.rowCopies m) (h.isConnectedSkew_rowCopies hW m hm).1 =
          (-1) ^ (((ω.rowCopies m).image Prod.fst).card - 1) * MvPolynomial.X L *
            (ω.capTheta h hW * ω.middleCofactor h hW ^ m *
              ω.hatMarkB h hW ^ (m - 1)) + MvPolynomial.map (Int.castRingHom ℚ) R := by
  obtain ⟨L, hL, _, R, hR, he⟩ := cellSchur_corner (h.isConnectedSkew_rowCopies hW m hm)
  rw [h.interiorSchur_rowCopies hW hm] at he
  exact ⟨L, hL, R, hR, he⟩

end SkewGluing.MarkedInner
