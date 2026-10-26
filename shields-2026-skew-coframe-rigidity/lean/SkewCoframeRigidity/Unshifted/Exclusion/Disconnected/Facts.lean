/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Low
import SkewCoframeRigidity.Unshifted.CellAlpha
import SkewCoframeRigidity.Unshifted.SmallSpan

/-!
# Nonvanishing facts of an end component

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner).  For an end component of span `L` carrying the
endpoint column, the coordinate `α_{E,p}` is nonzero unless `p = 2` and the component is the
literal two-cell row, and for span three the numerator `h₁² g₂ - 2 h₂²` is nonzero.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

theorem span_eq_one_imp {e : ℕ} (E : BetaDiagram (e + 1)) (hs : span E = 1) : e = 0 := by
  by_contra hne
  have hpos : 0 < e := Nat.pos_of_ne_zero hne
  have h1 := colPos_pos E ⟨0, hpos⟩
  have h2 := colPos_lt_span E ⟨0, hpos⟩
  omega

theorem coframe_eq_one_imp {e : ℕ} (E : BetaDiagram (e + 1)) (hE : E.Connected)
    (h : coframe E = 1) : e = 0 := by
  by_contra hne
  have hpos : 0 < e := Nat.pos_of_ne_zero hne
  have := (coframe_coeff_ne_zero_iff hE (colPos_pos E ⟨0, hpos⟩)).2
    (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  rw [h, Polynomial.coeff_one, ite_eq_right (by have := colPos_pos E ⟨0, hpos⟩; omega)] at this
  exact this rfl

theorem comp_facts {n : ℕ} (p : ℕ) (hp : 2 ≤ p) (D : BetaDiagram (n + 1)) (h : ℕ → CohField)
    (hh : ∀ k, k + 1 < span D → h k = cohLetters k) (A L cnt : ℕ) (g : CohField[X]) (k : CohField)
    (hA2 : 2 ≤ A) (hAL : A + L + 1 = span D)
    (hkind : (L = 0 ∧ g = 1 ∧ k = h 0 ∧ cnt = 1) ∨ ∃ (e : ℕ) (E : BetaDiagram (e + 1)),
      E.Connected ∧ E.col (Fin.last e) = 0 ∧ span E = L ∧ g = coframe E ∧ cnt = e + 1) :
    (alphaOf h g p L ≠ 0 ∨ (p = 2 ∧ L = 2 ∧ g = 1 ∧ cnt = 1)) ∧
      (L = 3 → h 1 ^ 2 * g.coeff 2 ≠ 2 * h 2 ^ 2) := by
  have hcongr : alphaOf h g p L = alphaOf cohLetters g p L :=
    alphaOf_congr g p L (fun k hk => hh k (by omega))
  have hp0 : (p : CohField) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : ((p - 1 : ℕ) : CohField) ≠ 0 := by exact_mod_cast (by omega : p - 1 ≠ 0)
  rcases hkind with ⟨rfl, rfl, -, -⟩ | ⟨e, E, hE, hEn, hs, rfl, rfl⟩
  · refine ⟨Or.inl ?_, fun h3 => absurd h3 (by norm_num)⟩
    rw [hcongr, alphaOf_unit]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hp0 hp1)
      (pow_ne_zero _ (cohLetters_ne_zero 0))) (cohLetters_ne_zero 1)) (cohLetters_ne_zero 0))
  · refine ⟨?_, ?_⟩
    · have hLpos := span_pos E
      rw [hs] at hLpos
      by_cases hL1 : L = 1
      · have he : e = 0 := span_eq_one_imp E (hs.trans hL1)
        subst he
        left
        rw [hcongr, coframe_of_zero, hL1]
        exact alphaOf_cell_ne_zero cohLetters p hp (cohLetters_ne_zero 0) (cohLetters_ne_zero 1)
      · by_cases hexc : p = 2 ∧ e = 0 ∧ span E = 2
        · right
          obtain ⟨hp2, he, hs2⟩ := hexc
          subst he
          exact ⟨hp2, by omega, coframe_of_zero E, rfl⟩
        · left
          rw [hcongr]
          have := alphaE_ne_zero hE hp (by omega) hexc
          rw [← hs]
          exact this
    · intro h3
      have hs3 : span E = 3 := hs.trans h3
      have := small_span_numerator_ne_zero_of_diagram E hE hEn hs3
      rw [hh 1 (by omega), hh 2 (by omega)]
      intro heq
      apply this
      linear_combination heq

end SkewCoframeRigidity.Unshifted
