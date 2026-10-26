/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap
import SkewCoframeRigidity.UnitRestoration.ZeroFree
import SkewCoframeRigidity.Stationary.BCell

/-!
# Equal cores from the first cap

Formalizes the passage in the unit case of `sc:positive-power` of
`shields-2026-skew-coframe-rigidity.tex` that shortens the top beta of the two zero-free cores
from `M` to `M - 1`, observes that the shortened cores have equal whole function, and adjoins the
same literal cell on top: the nonlinear fixed-cap result `sc:fixed-cap` identifies the cores.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe

section Helpers

variable {b : ℕ}

/-- The diagram with its top row beta decreased by one, given room below it. -/
def dropTop (B : BetaDiagram (b + 1)) (hr : ∀ i : Fin b, B.row i.succ < B.row 0 - 1)
    (hc : B.col 0 < B.row 0 - 1) : BetaDiagram (b + 1) where
  row i := if i = 0 then B.row 0 - 1 else B.row i
  col := B.col
  row_strictAnti := by
    intro i j hij
    have hj : j ≠ 0 := by
      intro h
      subst h
      exact absurd hij (Fin.not_lt_zero _)
    by_cases hi : i = 0
    · subst hi
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      simpa using hr j'
    · simpa [hi, hj] using B.row_strictAnti hij
  col_strictAnti := B.col_strictAnti
  row_nonempty i := by
    by_cases hi : i = 0
    · subst hi
      simpa using hc
    · simpa [hi] using B.row_nonempty i

variable (B : BetaDiagram (b + 1)) (hr : ∀ i : Fin b, B.row i.succ < B.row 0 - 1)
  (hc : B.col 0 < B.row 0 - 1)

theorem dropTop_isNorm (hB : IsNorm B) : IsNorm (dropTop B hr hc) := hB

theorem dropTop_connected (hBc : B.Connected) : (dropTop B hr hc).Connected := by
  refine ⟨Nat.succ_pos _, fun i hi => ?_⟩
  have h := hBc.2 i hi
  have hne : (⟨i.val + 1, hi⟩ : Fin (b + 1)) ≠ 0 := by
    intro h0
    have := congrArg Fin.val h0
    simp at this
  simp only [dropTop]
  rw [if_neg hne]
  exact h

theorem properMatrixOf_dropTop {L : Type*} [Zero L] (h : ℕ → L) :
    properMatrixOf h (dropTop B hr hc) = properMatrixOf h B := by
  ext i j
  simp [properMatrixOf, dropTop, Fin.succ_ne_zero]

theorem topVecOf_dropTop {L : Type*} [Zero L] (h : ℕ → L) :
    topVecOf h (dropTop B hr hc) = topVecOf h B := by
  ext i
  simp [topVecOf, dropTop, Fin.succ_ne_zero]

theorem coframe_dropTop : coframe (dropTop B hr hc) = coframe B := by
  unfold coframe coframeOf coframeVecOf
  rw [properMatrixOf_dropTop, topVecOf_dropTop]
  rfl

theorem cohCorner_dropTop : cohCorner (dropTop B hr hc) = cohCorner B := by
  unfold cohCorner cornerOf
  rw [properMatrixOf_dropTop]

theorem span_dropTop : span (dropTop B hr hc) = span B - 1 := by
  unfold span BetaDiagram.largestLabel
  change (((if (0 : Fin (b + 1)) = 0 then B.row 0 - 1 else B.row 0) -
    B.col (Fin.last b)).toNat) = _
  rw [if_pos rfl]
  omega

/-- The whole function of the shortened diagram is the signed corner times the degree `M - 1`
coefficient of `H G`. -/
theorem algebraMap_cohSchur_dropTop (hBc : B.Connected) :
    algebraMap CohRing CohField (cohSchur (dropTop B hr hc)) =
      algebraMap CohRing CohField (cohCorner B) *
        PowerSeries.coeff (span B - 1) (letterSeries * (coframe B : PowerSeries CohField)) := by
  rw [schur_eq_corner_mul_topQuotient (dropTop_connected B hr hc hBc), cohCorner_dropTop]
  congr 1
  unfold topQuotient topQuotientOf
  rw [span_dropTop]
  change PowerSeries.coeff _ (letterSeries * (coframe (dropTop B hr hc) : PowerSeries CohField)) = _
  rw [coframe_dropTop]

/-- Equal whole functions from equal board determinants under a reindexing of the index set. -/
theorem schur_eq_of_reindex {m n : ℕ} (D : BetaDiagram m) (E : BetaDiagram n) (e : Fin m ≃ Fin n)
    (hrow : ∀ i, D.row i = E.row (e i)) (hcol : ∀ i, D.col i = E.col (e i)) :
    D.schur = E.schur := by
  unfold BetaDiagram.schur
  rw [← Matrix.det_submatrix_equiv_self e E.matrix]
  congr 1
  ext i j
  simp [BetaDiagram.matrix, hrow, hcol]

/-- The same-cell splice of the shortened diagram has the whole function of the original. -/
theorem schur_splice_dropTop (hB : IsNorm B) :
    (splice cellCap (dropTop B hr hc) cellCap_isNorm (dropTop_isNorm B hr hc hB)).schur =
      B.schur := by
  obtain ⟨e, hv⟩ : ∃ e : Fin (0 + b + 1) ≃ Fin (b + 1), ∀ i, (e i).val = i.val :=
    ⟨finCongr (by omega), fun _ => rfl⟩
  refine schur_eq_of_reindex _ _ e (fun i => ?_) (fun i => ?_)
  · change spliceRow cellCap (dropTop B hr hc) i = _
    by_cases h : i.val < 1
    · have h0 : e i = 0 := by ext; rw [hv, Fin.val_zero]; omega
      rw [spliceRow_top cellCap _ i (by omega), h0]
      have : i = 0 := by ext; rw [Fin.val_zero]; omega
      subst this
      simp [cellCap, dropTop]
    · have h0 : e i ≠ 0 := by
        intro hh
        have := congrArg Fin.val hh
        rw [hv, Fin.val_zero] at this
        omega
      rw [spliceRow_bot cellCap _ i (by omega)]
      have : (⟨i.val - 0, by omega⟩ : Fin (b + 1)) = e i := by ext; simp [hv]
      simp only [dropTop]
      rw [this, if_neg h0]
  · change spliceCol cellCap (dropTop B hr hc) i = _
    rw [spliceCol_bot cellCap _ i (by omega)]
    change B.col _ = _
    congr 1
    ext
    simp [hv]

/-- Room below the top row beta: no proper row at `M - 1` and no column at `M - 1`. -/
theorem gap_facts {D : BetaDiagram (b + 1)} (hD : IsNorm D) (hDc : D.Connected)
    (hgap : ∀ i : Fin b, rowPos D i ≠ span D - 1) (hcol : (coframe D).coeff (span D - 1) = 0) :
    (∀ i : Fin b, D.row i.succ < D.row 0 - 1) ∧ D.col 0 < D.row 0 - 1 := by
  have hl : D.col (Fin.last b) = 0 := hD
  have hsp := span_cast D
  have hsp1 := span_pos D
  unfold BetaDiagram.largestLabel at hsp
  have hr : ∀ i : Fin b, D.row i.succ < D.row 0 - 1 := by
    intro i
    have h1 := rowPos_cast D i
    have h2 := rowPos_lt_span D i
    have h3 := hgap i
    omega
  refine ⟨hr, ?_⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have h0 : D.col 0 = 0 := hl
    have : span D - 1 ≠ 0 := by
      intro h
      rw [coframe_of_zero, h] at hcol
      simp at hcol
    omega
  · have h1 := hDc.2 ⟨0, by omega⟩ (by simp; omega)
    have h2 := hr ⟨0, hb⟩
    exact lt_of_le_of_lt h1 h2

end Helpers

theorem core_eq_of_first_cap (hcap : FixedCap.CapVanishing cellCap) {b : ℕ}
    (B B' : BetaDiagram (b + 1)) (hB : IsNorm B) (hB' : IsNorm B') (hBc : B.Connected)
    (hB'c : B'.Connected) (hs : B.schur = B'.schur)
    (hgap : ∀ i : Fin b, rowPos B i ≠ span B - 1) (hgap' : ∀ i : Fin b, rowPos B' i ≠ span B' - 1)
    (hcol : (coframe B).coeff (span B - 1) = 0) (hcol' : (coframe B').coeff (span B' - 1) = 0)
    (hU : PowerSeries.coeff (span B - 1) (unitFreeSeries * (coframe B : PowerSeries CohField)) =
      PowerSeries.coeff (span B' - 1) (unitFreeSeries * (coframe B' : PowerSeries CohField))) :
    B = B' := by
  have hspan : span B = span B' := (coequal_data hBc hs).2.2.1
  have hcorner : cohCorner B = cohCorner B' := (coequal_data hBc hs).2.1
  obtain ⟨hr, hc⟩ := gap_facts hB hBc hgap hcol
  obtain ⟨hr', hc'⟩ := gap_facts hB' hB'c hgap' hcol'
  set sB := dropTop B hr hc with hsB
  set sB' := dropTop B' hr' hc' with hsB'
  have hsBc : sB.Connected := dropTop_connected B hr hc hBc
  have hsB'c : sB'.Connected := dropTop_connected B' hr' hc' hB'c
  have hq : ∀ {D : BetaDiagram (b + 1)}, (coframe D).coeff (span D - 1) = 0 →
      PowerSeries.coeff (span D - 1) (letterSeries * (coframe D : PowerSeries CohField)) =
        PowerSeries.coeff (span D - 1) (unitFreeSeries * (coframe D : PowerSeries CohField)) :=
    fun {D} h => by
      rw [coeff_unitFree_mul, h, mul_zero, sub_zero]
  have hcs : cohSchur sB = cohSchur sB' := by
    apply IsFractionRing.injective CohRing CohField
    rw [algebraMap_cohSchur_dropTop B hr hc hBc, algebraMap_cohSchur_dropTop B' hr' hc' hB'c,
      hq hcol, hq hcol', hU, hcorner]
  have hss : sB.schur = sB'.schur := by
    apply physInclude_injective
    rw [← physSpec_schurOf, ← physSpec_schurOf]
    exact congrArg physSpec hcs
  have h2 : (splice cellCap sB cellCap_isNorm (dropTop_isNorm B hr hc hB)).schur =
      (splice cellCap sB' cellCap_isNorm (dropTop_isNorm B' hr' hc' hB')).schur := by
    rw [schur_splice_dropTop B hr hc hB, schur_splice_dropTop B' hr' hc' hB', hs]
  have hEq : sB = sB' :=
    eq_of_heq (FixedCap.fixed_cap_rigidity cellCap cellCap_isNorm cellCap_connected hcap sB sB'
      (dropTop_isNorm B hr hc hB) (dropTop_isNorm B' hr' hc' hB') hsBc hsB'c hss h2).2
  have hrow : ∀ i, sB.row i = sB'.row i := fun i => by rw [hEq]
  have hcl : B.col = B'.col := by
    have := congrArg BetaDiagram.col hEq
    exact this
  have hr0 : B.row 0 = B'.row 0 := by
    have := hrow 0
    simp [hsB, hsB', dropTop] at this
    exact this
  have hrw : B.row = B'.row := by
    funext i
    by_cases hi : i = 0
    · subst hi; exact hr0
    · have := hrow i
      simpa [hsB, hsB', dropTop, hi] using this
  cases B
  cases B'
  simp only at hrw hcl
  subst hrw hcl
  rfl

end SkewCoframeRigidity.UnitCase
