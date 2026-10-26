/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Atlas
import SkewCoframeRigidity.Stationary.ComponentRemainder

/-!
# Support of the difference of two coframes with a matched top

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:top-support`.  Two connected diagrams of
the same span whose row and column flags agree at every position `≥ a` have distinct complete
coframes only if the difference `C - G` has order between `1` and `a - 2`.  The argument is the
paper's: a difference vanishing through degree `a - 2` makes the native supports agree there
(`sc:atlas`, support), the numerators agree there, hence the numerator-zero test identifies the
rows there; the flags at `a - 1` follow from the equal row and column counts; all flags agree and
the coframes are equal.  The matched-component hypothesis of the paper is the special case in which
the flags at positions `≥ a` are those of the common highest strict proper component.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- Two strictly decreasing sequences of the same length with the same set of values agree. -/
theorem eq_of_image_eq {f g : Fin n → ℕ} (hf : StrictAnti f) (hg : StrictAnti g)
    (h : Finset.univ.image f = Finset.univ.image g) : f = g := by
  have hrev : StrictAnti (Fin.rev : Fin n → Fin n) := fun a b hab => Fin.rev_lt_rev.2 hab
  have h1 : StrictMono (f ∘ Fin.rev) := StrictAnti.comp hf hrev
  have h2 : StrictMono (g ∘ Fin.rev) := StrictAnti.comp hg hrev
  have hr : ∀ k : Fin n → ℕ, Set.range (k ∘ Fin.rev) = Set.range k := fun k => by
    rw [Set.range_comp, Fin.rev_surjective.range_eq, Set.image_univ]
  have : Set.range (f ∘ Fin.rev) = Set.range (g ∘ Fin.rev) := by
    rw [hr, hr]
    simpa [Finset.coe_image] using congrArg (fun s : Finset ℕ => (s : Set ℕ)) h
  have := (h1.range_inj_of_wellFoundedLT h2).1 this
  funext i
  have := congrFun this (Fin.rev i)
  simpa using this

theorem rowPos_strictAnti (D : BetaDiagram (n + 1)) : StrictAnti (rowPos D) := by
  intro i j hij
  have h1 : D.row j.succ < D.row i.succ := D.row_strictAnti (Fin.succ_lt_succ_iff.2 hij)
  have := rowPos_cast D i
  have := rowPos_cast D j
  omega

theorem colPos_strictAnti (D : BetaDiagram (n + 1)) : StrictAnti (colPos D) := by
  intro i j hij
  have h1 : D.col j.castSucc < D.col i.castSucc :=
    D.col_strictAnti (Fin.castSucc_lt_castSucc_iff.2 hij)
  have := colPos_cast D i
  have := colPos_cast D j
  omega

/-- The complete coframe depends on a diagram only through its flags. -/
theorem coframe_eq_of_flags {D E : BetaDiagram (n + 1)} (hr : rowSet D = rowSet E)
    (hc : colSet D = colSet E) : coframe D = coframe E := by
  have hrp : rowPos D = rowPos E := eq_of_image_eq (rowPos_strictAnti D) (rowPos_strictAnti E) hr
  have hcp : colPos D = colPos E := eq_of_image_eq (colPos_strictAnti D) (colPos_strictAnti E) hc
  have hT : properMatrixOf cohLetters D = properMatrixOf cohLetters E := by
    ext i j
    simp only [properMatrixOf, Matrix.of_apply]
    rw [← rowPos_sub_colPos D, ← rowPos_sub_colPos E, hrp, hcp]
  have hv : topVecOf cohLetters D = topVecOf cohLetters E := by
    ext i
    simp only [topVecOf]
    rw [← rowPos_cast D, ← rowPos_cast E, hrp]
  unfold coframe coframeOf coframeVecOf
  rw [hT, hv, hcp]

/-- Two finite sets with the same cardinality that agree off one point agree there too. -/
theorem mem_iff_of_card_eq {R R' : Finset ℕ} (c : ℕ) (h : ∀ i, i ≠ c → (i ∈ R ↔ i ∈ R'))
    (hc : R.card = R'.card) : c ∈ R ↔ c ∈ R' := by
  have he : R.erase c = R'.erase c := by
    ext i
    by_cases hi : i = c
    · simp [hi]
    · simp [hi, h i hi]
  by_cases ha : c ∈ R <;> by_cases hb : c ∈ R'
  · exact ⟨fun _ => hb, fun _ => ha⟩
  · exfalso
    have h1 := Finset.card_erase_add_one ha
    rw [he, Finset.erase_eq_of_notMem hb] at h1
    omega
  · exfalso
    have h2 := Finset.card_erase_add_one hb
    rw [← he, Finset.erase_eq_of_notMem ha] at h2
    omega
  · exact ⟨fun h => absurd h ha, fun h => absurd h hb⟩

theorem numerator_coeff_eq_of_agree {D E : BetaDiagram (n + 1)} (hs : span D = span E) {i : ℕ}
    (h : ∀ j ≤ i, (coframe D).coeff j = (coframe E).coeff j) :
    (numerator D).coeff i = (numerator E).coeff i := by
  unfold numerator numeratorOf
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, ← hs]
  split_ifs
  · rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [Polynomial.coeff_coe, Polynomial.coeff_coe]
    exact congrArg _ (h x.2 (by omega))
  · rfl

/-- `sc:top-support`: a pair of coframes with matched flags from position `a` upward and
distinct complete coframes has `1 ≤ ord (C - G) ≤ a - 2`. -/
theorem top_support {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hE : E.Connected)
    (hs : span D = span E) (a : ℕ)
    (hrow : ∀ i, a ≤ i → (i ∈ rowSet D ↔ i ∈ rowSet E))
    (hcol : ∀ s, a ≤ s → (s ∈ colSet D ↔ s ∈ colSet E))
    (hne : coframe D ≠ coframe E) :
    1 ≤ (coframe E - coframe D).natTrailingDegree ∧
      (coframe E - coframe D).natTrailingDegree ≤ a - 2 := by
  have hdiff : coframe E - coframe D ≠ 0 := sub_ne_zero.2 hne.symm
  refine ⟨?_, ?_⟩
  · by_contra h0
    have h0' : (coframe E - coframe D).natTrailingDegree = 0 := by omega
    have : (coframe E - coframe D).coeff 0 ≠ 0 := by
      have := mt Polynomial.trailingCoeff_eq_zero.1 hdiff
      rwa [Polynomial.trailingCoeff, h0'] at this
    apply this
    rw [Polynomial.coeff_sub, coeff_zero_coframe, coeff_zero_coframe, sub_self]
  · by_contra hlt
    have hagree : ∀ j, j + 2 ≤ a → (coframe D).coeff j = (coframe E).coeff j := by
      intro j hj
      have : j < (coframe E - coframe D).natTrailingDegree := by omega
      have := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree this
      rw [Polynomial.coeff_sub] at this
      exact (sub_eq_zero.1 this).symm
    apply hne
    apply coframe_eq_of_flags
    · -- rows
      have hoff : ∀ i, i ≠ a - 1 → (i ∈ rowSet D ↔ i ∈ rowSet E) := by
        intro i hi
        by_cases hia : a ≤ i
        · exact hrow i hia
        · have hi2 : i + 2 ≤ a := by omega
          by_cases h0 : i = 0
          · subst h0
            constructor <;> intro hm <;> exfalso <;>
            · simp only [rowSet, Finset.mem_image, Finset.mem_univ, true_and] at hm
              obtain ⟨k, hk⟩ := hm
              exact (rowPos_pos _ k).ne' hk
          · have h0' : 0 < i := Nat.pos_of_ne_zero h0
            by_cases hspan : i < span D
            · rw [← numerator_coeff_eq_zero_iff hD h0' hspan,
                ← numerator_coeff_eq_zero_iff hE h0' (hs ▸ hspan)]
              rw [numerator_coeff_eq_of_agree hs (fun j hj => hagree j (by omega))]
            · constructor <;> intro hm <;> exfalso <;>
              · simp only [rowSet, Finset.mem_image, Finset.mem_univ, true_and] at hm
                obtain ⟨k, hk⟩ := hm
                have := rowPos_lt_span D k
                have := rowPos_lt_span E k
                omega
      have hc := mem_iff_of_card_eq (a - 1) hoff
        (by rw [card_rowSet, card_rowSet])
      ext i
      by_cases hi : i = a - 1
      · rw [hi]; exact hc
      · exact hoff i hi
    · have hoff : ∀ i, i ≠ a - 1 → (i ∈ colSet D ↔ i ∈ colSet E) := by
        intro i hi
        by_cases hia : a ≤ i
        · exact hcol i hia
        · have hi2 : i + 2 ≤ a := by omega
          by_cases h0 : i = 0
          · subst h0
            constructor <;> intro hm <;> exfalso <;>
            · simp only [colSet, Finset.mem_image, Finset.mem_univ, true_and] at hm
              obtain ⟨k, hk⟩ := hm
              exact (colPos_pos _ k).ne' hk
          · have h0' : 0 < i := Nat.pos_of_ne_zero h0
            rw [← coframe_coeff_ne_zero_iff hD h0', ← coframe_coeff_ne_zero_iff hE h0',
              hagree i hi2]
      have hc := mem_iff_of_card_eq (a - 1) hoff
        (by rw [card_colSet, card_colSet])
      ext i
      by_cases hi : i = a - 1
      · rw [hi]; exact hc
      · exact hoff i hi

end SkewCoframeRigidity.Coframe
