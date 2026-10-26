/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Congr
import SkewCoframeRigidity.Coframe.CoequalData

/-!
# The top strict component and its endpoint column

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner).  For a normalized connected diagram `D` whose
top proper row sits at position `M - 1`, the endpoint column `a = -∑_c Π_{c,m} z^c` is
`-z^A g / k`, where the top strict component is either a unit (`g = 1`, `k = ϑ`, span `L = 0`) or
a connected diagram translated by `-A` of span `L`, with `g` its own coframe and `k = [H g]_L`.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem blockIdx_zero (D : BetaDiagram (n + 1)) (hn : 0 < n) : blockIdx D ⟨0, hn⟩ = 0 := by
  classical
  unfold blockIdx
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro c - ⟨hc, j, hj, -⟩
  have : c.val = 0 := by
    have := Fin.le_iff_val_le_val.mp hc
    simpa using this
  omega

/-- The top component data of the endpoint column. -/
theorem top_data (D : BetaDiagram (n + 1)) (hD : D.Connected) (hDn : D.col (Fin.last n) = 0)
    (h : ℕ → CohField) (hh : ∀ k, k + 1 < span D → h k = cohLetters k) (hh0 : h 0 ≠ 0)
    (hport : ∃ i, rowPos D i + 1 = span D) :
    ∃ (A L cnt : ℕ) (g : CohField[X]) (k : CohField), 1 ≤ A ∧ A + L + 1 = span D ∧
      g.coeff 0 = 1 ∧ (0 < L → ∀ j, L ≤ j → g.coeff j = 0) ∧
      k = PowerSeries.coeff L (seriesOf h * (g : PowerSeries CohField)) ∧ k ≠ 0 ∧
      endpointA h D = Polynomial.C (-1 / k) * (Polynomial.X ^ A * g) ∧
      ((L = 0 ∧ g = 1 ∧ k = h 0 ∧ cnt = 1) ∨ ∃ (e : ℕ) (E : BetaDiagram (e + 1)), E.Connected ∧
        E.col (Fin.last e) = 0 ∧ span E = L ∧ g = coframe E ∧ cnt = e + 1) ∧
      ∃ hn : 0 < n, 0 < cnt ∧ cnt ≤ n ∧ (∀ i : Fin n, blockIdx D i = 0 ↔ i.val < cnt) ∧
        ∃ hlt : cnt - 1 < n, colPos D ⟨cnt - 1, hlt⟩ = A := by
  classical
  have hn : 0 < n := by
    obtain ⟨i, -⟩ := hport
    exact Fin.pos i
  have hhead := rowPos_zero_succ hDn hport hn
  have hT : (properMatrixOf h D).det ≠ 0 := by
    rw [properMatrixOf_congr D (h' := cohLetters) hh]
    exact properDet_cohLetters_ne_zero hD
  have hk0 : (0 : ℕ) ∈ Finset.univ.image (blockIdx D) :=
    Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, blockIdx_zero D hn⟩
  obtain ⟨s, m, hsm, hm, hfib, hcase⟩ := strict_component h hD hk0
  have hs0 : s = 0 := by
    have := ((hfib ⟨0, hn⟩).mp (blockIdx_zero D hn)).1
    exact Nat.le_zero.mp (by simpa using this)
  subst hs0
  rcases hcase with ⟨hm1, hu, -⟩ | ⟨hpos, hconn, -⟩
  · -- a unit
    subst hm1
    have hu0 : IsUnit' D ⟨0, hn⟩ := hu ⟨0, hn⟩ rfl
    have hpos : rowPos D ⟨0, hn⟩ = colPos D ⟨0, hn⟩ := by
      have h1 := rowPos_cast D ⟨0, hn⟩
      have h2 := colPos_cast D ⟨0, hn⟩
      unfold IsUnit' at hu0
      have : (rowPos D ⟨0, hn⟩ : ℤ) = colPos D ⟨0, hn⟩ := by
        rw [h1, h2, hu0]
      exact_mod_cast this
    have hz : ∀ i, i ≠ (⟨0, hn⟩ : Fin n) → properMatrixOf h D i ⟨0, hn⟩ = 0 := by
      intro i hi
      apply properMatrixOf_eq_zero
      have hne : blockIdx D i ≠ blockIdx D ⟨0, hn⟩ := fun e =>
        hi (blockIdx_eq_imp_of_unit hu0 e)
      have hle := blockIdx_mono D (show (⟨0, hn⟩ : Fin n) ≤ i from Fin.mk_le_of_le_val (Nat.zero_le _))
      omega
    have key := endpointA_unit h D hT ⟨0, hn⟩ ⟨0, hn⟩ hpos hz hhead hh0
    have hA1 := colPos_pos D ⟨0, hn⟩
    refine ⟨colPos D ⟨0, hn⟩, 0, 1, 1, h 0, hA1, by omega, ?_, fun h' => absurd h' (lt_irrefl 0),
      ?_, hh0, ?_, Or.inl ⟨rfl, rfl, rfl, rfl⟩, hn, one_pos, hsm, ?_, by omega, ?_⟩
    · simp
    · simp [seriesOf]
    · have : endpointA h D = -(Polynomial.X ^ colPos D ⟨0, hn⟩) * Polynomial.C ((h 0)⁻¹) := by
        have := congrArg (fun F => F * Polynomial.C ((h 0)⁻¹)) key
        simp only [mul_assoc, ← map_mul, mul_inv_cancel₀ hh0, map_one, mul_one] at this
        exact this
      rw [this]
      simp only [mul_one, div_eq_mul_inv, neg_mul, one_mul, map_neg, map_one]
      ring
    · intro i
      constructor
      · intro e
        have := blockIdx_eq_imp_of_unit hu0 (e.trans (blockIdx_zero D hn).symm)
        simp [this]
      · intro hi
        have : i = ⟨0, hn⟩ := Fin.ext (by simp; omega)
        subst this; exact blockIdx_zero D hn
    · simp
  · -- a connected component
    obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
    set r : Fin (e + 1) → Fin n := blockEmb 0 (e + 1) hsm with hr
    have hrval : ∀ i, (r i).val = i.val := fun i => by simp [hr, blockEmb]
    set A : ℕ := colPos D (r (Fin.last e)) with hA
    have hAcast : (A : ℤ) = D.col (r (Fin.last e)).castSucc := by
      have := colPos_cast D (r (Fin.last e)); rw [hDn] at this; simpa [hA] using this
    set E' := blockDiagram D 0 (e + 1) hsm hpos with hE'
    set E := E'.translate (-(A : ℤ)) with hE
    have hErow : ∀ p, E.row p = D.row (r p).succ - A := fun p => by
      simp only [hE, BetaDiagram.translate, hE', blockDiagram, hr]; ring
    have hEcol : ∀ q, E.col q = D.col (r q).castSucc - A := fun q => by
      simp only [hE, BetaDiagram.translate, hE', blockDiagram, hr]; ring
    have hEn : E.col (Fin.last e) = 0 := by rw [hEcol, hAcast]; ring
    have hEc : E.Connected := hconn.translate _
    have hA1 : 1 ≤ A := colPos_pos D _
    have hr0 : r 0 = ⟨0, hn⟩ := Fin.ext (by rw [hrval]; rfl)
    have hrow : ∀ p, (rowPos D (r p) : ℤ) = E.row p + A := fun p => by
      have := rowPos_cast D (r p); rw [hDn] at this; rw [hErow]; omega
    have hcol : ∀ q, (colPos D (r q) : ℤ) = E.col q + A := fun q => by
      have := colPos_cast D (r q); rw [hDn] at this; rw [hEcol]; omega
    have hspanE : span E + A + 1 = span D := by
      have h1 := span_cast E
      have h2 := span_cast D
      have h3 := rowPos_cast D (r 0)
      have h4 := span_pos E
      have h5 := hrow 0
      have h6 := hhead
      rw [hr0] at h5
      unfold BetaDiagram.largestLabel at h1 h2
      rw [hDn] at h2
      have h7 := rowPos_cast D (⟨0, hn⟩ : Fin n)
      rw [hDn] at h7
      rw [hEn] at h1
      omega
    have hhE : ∀ k, k ≤ span E → h k = cohLetters k := fun k hk => hh k (by omega)
    have hTE : (properMatrixOf h E).det ≠ 0 := by
      rw [properMatrixOf_congr E (h' := cohLetters) (fun k hk => hhE k (by omega))]
      exact properDet_cohLetters_ne_zero hEc
    have hF : (fullMatrixOf h E).det ≠ 0 := by
      have : fullMatrixOf h E = fullMatrixOf cohLetters E := by
        ext i j
        simp only [fullMatrixOf, Matrix.of_apply]
        have h1 := E.row_strictAnti.antitone (Fin.zero_le i)
        have h2 := E.col_strictAnti.antitone (Fin.le_last j)
        have h3 := span_cast E
        unfold BetaDiagram.largestLabel at h3
        rw [hEn] at h3
        unfold letterOf
        split_ifs with hneg
        · rfl
        · exact hhE _ (by omega)
      rw [this]
      exact schurOf_cohLetters_ne_zero E
    have hz : ∀ i, i ∉ Set.range r → ∀ q, properMatrixOf h D i (r q) = 0 := by
      intro i hi q
      apply properMatrixOf_eq_zero
      have hq : blockIdx D (r q) = 0 := (hfib _).mpr ⟨by omega, by rw [hrval]; omega⟩
      have hne : blockIdx D i ≠ 0 := fun e0 => hi ⟨⟨i.val, by have := ((hfib i).mp e0).2; omega⟩,
        Fin.ext (by rw [hrval])⟩
      omega
    have hrinj : Function.Injective r := fun i j hij => Fin.ext (by
      have := congrArg Fin.val hij; rwa [hrval, hrval] at this)
    have key := endpointA_block h D hT E A r r hrinj hrow hcol hEn hz (by rw [hr0]; exact hhead)
      hTE hF
    have hgE : coframeOf h E = coframe E :=
      coframeOf_congr E (fun k hk => hh k (by omega))
    have hkE : topQuotientOf h E = PowerSeries.coeff (span E)
        (seriesOf h * (coframe E : PowerSeries CohField)) := by
      unfold topQuotientOf; rw [hgE]
    refine ⟨A, span E, e + 1, coframe E, topQuotientOf h E, hA1, by omega, coframe_coeff_zero E,
      ?_, hkE, key.1, ?_, Or.inr ⟨e, E, hEc, hEn, rfl, rfl, rfl⟩, hn, by omega, by omega, ?_, ?_⟩
    · intro hL j hj
      have := natDegree_coframe_le E
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · have h2 := key.2
      rw [hgE] at h2
      have hk0 := key.1
      have : endpointA h D = -(Polynomial.X ^ A * coframe E) * Polynomial.C ((topQuotientOf h E)⁻¹) := by
        have := congrArg (fun F => F * Polynomial.C ((topQuotientOf h E)⁻¹)) h2
        simp only [mul_assoc, ← map_mul, mul_inv_cancel₀ hk0, map_one, mul_one] at this
        exact this
      rw [this]
      simp only [div_eq_mul_inv, neg_mul, one_mul, map_neg, map_one]
      ring
    · intro i
      rw [hfib]
      omega
    · refine ⟨by omega, ?_⟩
      have : r (Fin.last e) = ⟨e + 1 - 1, by omega⟩ := Fin.ext (by rw [hrval]; simp)
      rw [← this]

end SkewCoframeRigidity.Unshifted
