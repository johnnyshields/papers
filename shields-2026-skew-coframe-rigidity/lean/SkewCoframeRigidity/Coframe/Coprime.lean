/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Irreducible
import SkewCoframeRigidity.Coframe.Atlas

/-!
# Irreducibility and coprimality of coframes

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:coprime`.  A nonconstant complete
coframe is irreducible over the raw field; two distinct coframes are coprime; equal coframes of
normalized connected diagrams of the same span identify the diagrams literally; and the defect of
two distinct coframes, the first nonconstant, is nonzero.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n m : ℕ}

theorem coframe_irreducible {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n) :
    Irreducible (coframe D) :=
  coframe_irreducible_aux D (properDet_cohLetters_ne_zero hD) hn

theorem coframe_not_dvd_numerator {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n) :
    ¬ coframe D ∣ numerator D :=
  coframe_not_dvd_numerator_aux D (properDet_cohLetters_ne_zero hD) hn

theorem coframe_coeff_zero (D : BetaDiagram (n + 1)) : (coframe D).coeff 0 = 1 :=
  uniPoly_coeff_zero_of_pos _ _ (colPos_pos D)

theorem coframe_of_zero (D : BetaDiagram (0 + 1)) : coframe D = 1 := by
  simp [coframe, coframeOf]

theorem coframe_dvd_eq {D : BetaDiagram (n + 1)} {E : BetaDiagram (m + 1)}
    (hD : D.Connected) (hE : E.Connected) (hn : 0 < n)
    (h : coframe D ∣ coframe E) : coframe D = coframe E := by
  have hG := coframe_irreducible hD hn
  obtain ⟨w, hw⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exfalso
    rw [coframe_of_zero] at hw
    exact hG.not_isUnit (isUnit_iff_exists_inv.2 ⟨w, hw.symm⟩)
  · have hC := coframe_irreducible hE hm
    rcases hC.isUnit_or_isUnit hw with h1 | h1
    · exact absurd h1 hG.not_isUnit
    · obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp h1
      have h0 := congrArg (fun p => p.coeff 0) hw
      simp only [coframe_coeff_zero, Polynomial.coeff_mul_C] at h0
      have : r = 1 := by simpa using h0.symm
      rw [hw, this]
      simp

theorem coframe_isCoprime {D : BetaDiagram (n + 1)} {E : BetaDiagram (m + 1)}
    (hD : D.Connected) (hE : E.Connected) (hne : coframe D ≠ coframe E) :
    IsCoprime (coframe D) (coframe E) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coframe_of_zero]
    exact isCoprime_one_left
  · exact (coframe_irreducible hD hn).coprime_iff_not_dvd.2 fun h => hne (coframe_dvd_eq hD hE hn h)

theorem defect_eq {D : BetaDiagram (n + 1)} {E : BetaDiagram (m + 1)} (hs : span D = span E) :
    defect D E = coframe D * numerator E - coframe E * numerator D := by
  unfold defect clippedOp numerator numeratorOf
  rw [hs]
  rfl

theorem defect_ne_zero {D : BetaDiagram (n + 1)} {E : BetaDiagram (m + 1)}
    (hD : D.Connected) (hE : E.Connected) (hn : 0 < n) (hs : span D = span E)
    (hne : coframe D ≠ coframe E) : defect D E ≠ 0 := by
  intro h0
  rw [defect_eq hs, sub_eq_zero] at h0
  have hG := coframe_irreducible hD hn
  have hdiv : coframe D ∣ coframe E * numerator D := ⟨numerator E, h0.symm⟩
  rcases hG.prime.dvd_or_dvd hdiv with h | h
  · exact hne (coframe_dvd_eq hD hE hn h)
  · exact coframe_not_dvd_numerator hD hn h

theorem strictAnti_eq_of_range_eq {k : ℕ} {f g : Fin k → ℤ} (hf : StrictAnti f)
    (hg : StrictAnti g) (h : Set.range f = Set.range g) : f = g := by
  have hf' : StrictMono (f ∘ Fin.rev) := fun a b hab => hf (Fin.rev_strictAnti hab)
  have hg' : StrictMono (g ∘ Fin.rev) := fun a b hab => hg (Fin.rev_strictAnti hab)
  have hr : Set.range (f ∘ Fin.rev) = Set.range (g ∘ Fin.rev) := by
    rw [Function.Surjective.range_comp Fin.rev_involutive.surjective,
      Function.Surjective.range_comp Fin.rev_involutive.surjective, h]
  have := (hf'.range_inj_of_wellFoundedLT hg').1 hr
  funext i
  simpa using congrFun this i.rev

section Normalized

variable (D : BetaDiagram (n + 1)) (hDn : D.col (Fin.last n) = 0)
include hDn

theorem row_zero_eq : D.row 0 = (span D : ℤ) := by
  have := span_cast D
  unfold BetaDiagram.largestLabel at this
  omega

theorem row_succ_eq (i : Fin n) : D.row i.succ = (rowPos D i : ℤ) := by
  have := rowPos_cast D i
  omega

theorem col_castSucc_eq (j : Fin n) : D.col j.castSucc = (colPos D j : ℤ) := by
  have := colPos_cast D j
  omega

theorem mem_range_row (z : ℤ) :
    z ∈ Set.range D.row ↔ z = (span D : ℤ) ∨ ∃ i ∈ rowSet D, z = (i : ℤ) := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k using Fin.cases with
    | zero => exact Or.inl (row_zero_eq D hDn)
    | succ i =>
      exact Or.inr ⟨rowPos D i, Finset.mem_image_of_mem _ (Finset.mem_univ i),
        row_succ_eq D hDn i⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨0, row_zero_eq D hDn⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j.succ, row_succ_eq D hDn j⟩

theorem mem_range_col (z : ℤ) :
    z ∈ Set.range D.col ↔ z = 0 ∨ ∃ s ∈ colSet D, z = (s : ℤ) := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k using Fin.lastCases with
    | last => exact Or.inl hDn
    | cast j =>
      exact Or.inr ⟨colPos D j, Finset.mem_image_of_mem _ (Finset.mem_univ j),
        col_castSucc_eq D hDn j⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨Fin.last n, hDn⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j.castSucc, col_castSucc_eq D hDn j⟩

end Normalized

theorem colSet_eq_of_coframe_eq {D : BetaDiagram (n + 1)} {E : BetaDiagram (m + 1)}
    (hD : D.Connected) (hE : E.Connected) (h : coframe D = coframe E) :
    colSet D = colSet E := by
  have key : ∀ {k : ℕ} (F : BetaDiagram (k + 1)), F.Connected → ∀ s,
      s ∈ colSet F ↔ 0 < s ∧ (coframe F).coeff s ≠ 0 := by
    intro k F hF s
    constructor
    · intro hs
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨colPos_pos F j, (coframe_coeff_ne_zero_iff hF (colPos_pos F j)).2 hs⟩
    · rintro ⟨h1, h2⟩
      exact (coframe_coeff_ne_zero_iff hF h1).1 h2
  ext s
  rw [key D hD, key E hE, h]

theorem rowSet_eq_of_coframe_eq {D : BetaDiagram (n + 1)} {E : BetaDiagram (m + 1)}
    (hD : D.Connected) (hE : E.Connected) (hs : span D = span E) (h : coframe D = coframe E) :
    rowSet D = rowSet E := by
  have hnum : numerator D = numerator E := by
    unfold numerator numeratorOf
    change PowerSeries.trunc (span D) (letterSeries * (coframe D : PowerSeries CohField)) =
      PowerSeries.trunc (span E) (letterSeries * (coframe E : PowerSeries CohField))
    rw [hs, h]
  have key : ∀ {k : ℕ} (F : BetaDiagram (k + 1)), F.Connected → ∀ i,
      i ∈ rowSet F ↔ 0 < i ∧ i < span F ∧ (numerator F).coeff i = 0 := by
    intro k F hF i
    constructor
    · intro hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨rowPos_pos F j, rowPos_lt_span F j,
        (numerator_coeff_eq_zero_iff hF (rowPos_pos F j) (rowPos_lt_span F j)).2 hi⟩
    · rintro ⟨h1, h2, h3⟩
      exact (numerator_coeff_eq_zero_iff hF h1 h2).1 h3
  ext i
  rw [key D hD, key E hE, hnum, hs]

theorem eq_of_coframe_eq {D : BetaDiagram (n + 1)} {E : BetaDiagram (m + 1)}
    (hDn : D.col (Fin.last n) = 0) (hEn : E.col (Fin.last m) = 0)
    (hD : D.Connected) (hE : E.Connected) (hs : span D = span E)
    (h : coframe D = coframe E) : n = m ∧ HEq D E := by
  have hcol := colSet_eq_of_coframe_eq hD hE h
  have hrow := rowSet_eq_of_coframe_eq hD hE hs h
  have hnm : n = m := by
    rw [← card_colSet D, ← card_colSet E, hcol]
  subst hnm
  refine ⟨rfl, heq_of_eq ?_⟩
  have hr : D.row = E.row := by
    apply strictAnti_eq_of_range_eq D.row_strictAnti E.row_strictAnti
    ext z
    rw [mem_range_row D hDn, mem_range_row E hEn, hs, hrow]
  have hc : D.col = E.col := by
    apply strictAnti_eq_of_range_eq D.col_strictAnti E.col_strictAnti
    ext z
    rw [mem_range_col D hDn, mem_range_col E hEn, hcol]
  obtain ⟨r1, c1, _, _, _⟩ := D
  obtain ⟨r2, c2, _, _, _⟩ := E
  simp only at hr hc
  subst hr hc
  rfl

end SkewCoframeRigidity.Coframe
