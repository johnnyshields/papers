/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.NonnegativeRigidity
import SkewJacobiNegative.AffineHomogenization
import Mathlib.Tactic.FinCases

/-!
# Three-row rigidity

The three-row assertion of `lem:small-rows` in
`shields-2026-skew-jacobi-negative.tex`.  In the one-negative-cell case,
coefficient-one monomials recover the unordered pair of adjacent coarsenings.
This also proves the height-three ribbon case directly; no ribbon classification
is assumed.  Gamma retains unit factors before transporting polynomial equality.
-/

namespace SkewJacobiNegative
open scoped BigOperators

private def tripleMatch (a b c d e f : ℤ) : Prop :=
  (a = d ∧ b = e ∧ c = f) ∨ (a = d ∧ b = f ∧ c = e) ∨
  (a = e ∧ b = d ∧ c = f) ∨ (a = e ∧ b = f ∧ c = d) ∨
  (a = f ∧ b = d ∧ c = e) ∨ (a = f ∧ b = e ∧ c = d)

-- TODO-COPIED: skew-cofactor-independence/lean/SkewCofactorIndependence/NonnegativeRigidity.lean
private theorem triple_product_reading {a b c d e f : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h : complete a * complete b * complete c = complete d * complete e * complete f) :
    tripleMatch a b c d e f := by
  have hi : Base.complete a * Base.complete b * Base.complete c =
      Base.complete d * Base.complete e * Base.complete f := by
    apply integerLift_injective
    simpa only [map_mul, complete] using h
  have hcast : ∀ x : ℤ, 0 < x → (x.toNat : ℤ) = x := fun x hx => by omega
  have hm : (([a.toNat, b.toNat, c.toNat] : List ℕ) : Multiset ℕ) =
      (([d.toNat, e.toNat, f.toNat] : List ℕ) : Multiset ℕ) := by
    apply (Base.prod_complete_eq_iff_of_pos _ _ (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> omega) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> omega)).mp
    simpa [hcast a ha, hcast b hb, hcast c hc, hcast d hd, hcast e he, hcast f hf,
      mul_assoc] using hi
  have hmema : a.toNat = d.toNat ∨ a.toNat = e.toNat ∨ a.toNat = f.toNat := by
    have hh : a.toNat ∈ (([a.toNat, b.toNat, c.toNat] : List ℕ) : Multiset ℕ) := by simp
    rw [hm] at hh
    simpa using hh
  have hpair {x y : ℤ} (hx : 0 < x) (hy : 0 < y)
      (hh : complete a * complete b * complete c = complete a * complete x * complete y) :
      (b = x ∧ c = y) ∨ (b = y ∧ c = x) := by
    apply complete_two_product_reading hb hc hx hy
    apply mul_left_cancel₀ ((complete_ne_zero_iff a).mpr ha.le)
    simpa only [mul_assoc] using hh
  rcases hmema with h₁ | h₁ | h₁
  · have h₁ : a = d := by omega
    subst d
    have h₂ := hpair he hf h
    rcases h₂ with ⟨hb', hc'⟩ | ⟨hb', hc'⟩
    · exact Or.inl ⟨rfl, hb', hc'⟩
    · exact Or.inr (Or.inl ⟨rfl, hb', hc'⟩)
  · have h₁ : a = e := by omega
    subst e
    have h₂ := hpair hd hf (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)
    rcases h₂ with ⟨hb', hc'⟩ | ⟨hb', hc'⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hb', hc'⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hb', hc'⟩)))
  · have h₁ : a = f := by omega
    subst f
    have h₂ := hpair hd he (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)
    rcases h₂ with ⟨hb', hc'⟩ | ⟨hb', hc'⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hb', hc'⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hb', hc'⟩))))

private theorem monomial_pair_reading (a b c d : ℕ+ →₀ ℕ)
    (h : (MvPolynomial.monomial a 1 : CompleteRing) + MvPolynomial.monomial b 1 =
      MvPolynomial.monomial c 1 + MvPolynomial.monomial d 1) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have hinj := MvPolynomial.monomial_left_injective (σ := ℕ+)
    (show (1 : ℚ) ≠ 0 by norm_num)
  by_cases hac : a = c
  · subst c
    exact Or.inl ⟨rfl, hinj (add_left_cancel h)⟩
  · have had : a = d := by
      by_contra had
      have hh := congrArg (fun p : CompleteRing => p.coeff a) h
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial] at hh
      by_cases hab : a = b
      · subst b
        simp only [ite_eq_right (Ne.symm hac), ite_eq_right (Ne.symm had)] at hh
        norm_num at hh
      · simp only [ite_eq_right (Ne.symm hac), ite_eq_right (Ne.symm had),
          ite_eq_right (Ne.symm hab)] at hh
        norm_num at hh
    subst d
    have hh : MvPolynomial.monomial b (1 : ℚ) = MvPolynomial.monomial c 1 := by
      linear_combination h
    exact Or.inr ⟨rfl, hinj hh⟩

private theorem triple_sum_reading {a b c d e f u v w x y z : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : complete a * complete b * complete c + complete d * complete e * complete f =
      complete u * complete v * complete w + complete x * complete y * complete z) :
    (tripleMatch a b c u v w ∧ tripleMatch d e f x y z) ∨
      (tripleMatch a b c x y z ∧ tripleMatch d e f u v w) := by
  let mon (i j k : ℤ) := Gluing.hExp i.toNat + Gluing.hExp j.toNat + Gluing.hExp k.toNat
  have hm {i j k : ℤ} (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
      complete i * complete j * complete k = MvPolynomial.monomial (mon i j k) 1 := by
    rw [complete_eq_hh, complete_eq_hh, complete_eq_hh,
      Gluing.hh_eq_monomial hi.le, Gluing.hh_eq_monomial hj.le,
      Gluing.hh_eq_monomial hk.le,
      MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
    simp only [mul_one, mon]
  have hh := h
  rw [hm ha hb hc, hm hd he hf, hm hu hv hw, hm hx hy hz] at hh
  rcases monomial_pair_reading _ _ _ _ hh with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    constructor
    · apply triple_product_reading ha hb hc hu hv hw
      rw [hm ha hb hc, hm hu hv hw, h₁]
    · apply triple_product_reading hd he hf hx hy hz
      rw [hm hd he hf, hm hx hy hz, h₂]
  · right
    constructor
    · apply triple_product_reading ha hb hc hx hy hz
      rw [hm ha hb hc, hm hx hy hz, h₁]
    · apply triple_product_reading hd he hf hu hv hw
      rw [hm hd he hf, hm hu hv hw, h₂]

namespace BetaDiagram

/-- The actual three-row determinant, with every signed index and unit retained. -/
theorem schur_three_expansion (D : BetaDiagram 3) :
    D.schur =
      complete (D.rowLength 0) * complete (D.rowLength 1) * complete (D.rowLength 2) -
      complete (D.row 0 - D.col 1) * complete (D.row 1 - D.col 0) * complete (D.rowLength 2) -
      complete (D.rowLength 0) * complete (D.row 1 - D.col 2) * complete (D.row 2 - D.col 1) +
      complete (D.row 0 - D.col 2) * complete (D.row 1 - D.col 0) * complete (D.row 2 - D.col 1) +
      complete (D.row 0 - D.col 1) * complete (D.row 1 - D.col 2) * complete (D.row 2 - D.col 0) -
      complete (D.row 0 - D.col 2) * complete (D.rowLength 1) * complete (D.row 2 - D.col 0) := by
  rw [schur, Matrix.det_fin_three]
  simp only [matrix, Matrix.of_apply, rowLength]
  ring

/-- The literal corner formula for three full rows. -/
theorem cornerPolynomial_three (D : BetaDiagram 3) :
    D.cornerPolynomial = complete (D.row 1 - D.col 0) * complete (D.row 2 - D.col 1) -
      complete (D.rowLength 1) * complete (D.row 2 - D.col 0) := by
  rw [cornerPolynomial, Matrix.det_fin_two]
  rfl

private theorem bottom_left_negative (D : BetaDiagram 3) (_hD : D.Connected)
    (hN : ¬ D.Nonnegative) : D.row 2 < D.col 0 := by
  by_contra hn
  have hn : D.col 0 ≤ D.row 2 := by omega
  apply hN
  intro i j
  have hr := D.row_strictAnti.antitone (Fin.le_last i)
  have hc := D.col_strictAnti.antitone (Fin.zero_le j)
  change D.row 2 ≤ D.row i at hr
  omega

private theorem positive_adjacent (D : BetaDiagram 3) (hD : D.Connected)
    (hZ : D.ZeroFree) : 0 < D.row 1 - D.col 0 ∧ 0 < D.row 2 - D.col 1 := by
  have h₀ := hD.2 0 (by decide)
  have h₁ := hD.2 1 (by decide)
  have hz₀ := hZ 1 0
  have hz₁ := hZ 2 1
  change D.col 0 ≤ D.row 1 at h₀
  change D.col 1 ≤ D.row 2 at h₁
  omega

private theorem motion_symm (D E : BetaDiagram 3)
    (h : E.TranslationEquivalent D ∨ E.RotationEquivalent D) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  rcases h with ⟨c, hr, hc⟩ | ⟨c, hr, hc⟩
  · left
    refine ⟨-c, ?_, ?_⟩ <;> intro i
    · have := hr i; omega
    · have := hc i; omega
  · right
    refine ⟨c, ?_, ?_⟩ <;> intro i
    · have hh := hc i.rev
      rw [Fin.rev_rev] at hh
      omega
    · have hh := hr i.rev
      rw [Fin.rev_rev] at hh
      omega

set_option maxHeartbeats 0 in
-- Structural permutations of three factors produce many independent arithmetic branches.
set_option maxRecDepth 10000 in
private theorem negative_profile_reading
    (a b c s t A B C S T : ℤ)
    (_hs : 0 < s) (_ht : 0 < t) (_hS : 0 < S) (_hT : 0 < T)
    (hsa : s < a) (hsb : s < b) (htb : t < b) (htc : t < c)
    (hSA : S < A) (hSB : S < B) (hTB : T < B) (hTC : T < C)
    (_hn : s + t < b) (_hN : S + T < B)
    (hr : tripleMatch a b c A B C)
    (hg : (s = S ∧ t = T) ∨ (s = T ∧ t = S))
    (hp :
      (tripleMatch (a + b - s) s c (A + B - S) S C ∧
        tripleMatch a (b + c - t) t A (B + C - T) T) ∨
      (tripleMatch (a + b - s) s c A (B + C - T) T ∧
        tripleMatch a (b + c - t) t (A + B - S) S C)) :
    (a = A ∧ b = B ∧ c = C ∧ s = S ∧ t = T) ∨
      (a = C ∧ b = B ∧ c = A ∧ s = T ∧ t = S) := by
  unfold tripleMatch at hr hp
  rcases hr with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
    ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases hg with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rcases h₁ with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases h₂ with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- Zero-free three-row boards are rigid, including their one-negative-cell branch. -/
theorem rigidity_three_zeroFree (D E : BetaDiagram 3)
    (hD : D.Connected) (hE : E.Connected) (hZD : D.ZeroFree) (hZE : E.ZeroFree)
    (he : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  by_cases hND : D.Nonnegative
  · exact D.nonnegative_rigidity_same_order E hD hE hND he
  by_cases hNE : E.Nonnegative
  · exact motion_symm D E (E.nonnegative_rigidity_same_order D hE hD hNE he.symm)
  have hnD := bottom_left_negative D hD hND
  have hnE := bottom_left_negative E hE hNE
  obtain ⟨hs, ht⟩ := positive_adjacent D hD hZD
  obtain ⟨hS, hT⟩ := positive_adjacent E hE hZE
  let a := D.rowLength 0
  let b := D.rowLength 1
  let c := D.rowLength 2
  let s := D.row 1 - D.col 0
  let t := D.row 2 - D.col 1
  let A := E.rowLength 0
  let B := E.rowLength 1
  let C := E.rowLength 2
  let S := E.row 1 - E.col 0
  let T := E.row 2 - E.col 1
  have hrow := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [D.square_initialForm, E.square_initialForm] at hrow
  have hrow' : complete a * complete b * complete c =
      complete A * complete B * complete C := by
    simpa [Fin.prod_univ_three, a, b, c, A, B, C, rowLength, mul_assoc] using hrow
  have hr := triple_product_reading (D.rowLength_pos 0) (D.rowLength_pos 1)
    (D.rowLength_pos 2) (E.rowLength_pos 0) (E.rowLength_pos 1)
    (E.rowLength_pos 2) hrow'
  have hcorner := D.cornerPolynomial_eq_of_schur_eq E hD hE he
  rw [D.cornerPolynomial_three, E.cornerPolynomial_three,
    complete_of_neg (sub_neg.mpr hnD), complete_of_neg (sub_neg.mpr hnE)] at hcorner
  simp only [mul_zero, sub_zero] at hcorner
  have hg := complete_two_product_reading hs ht hS hT hcorner
  have hlabel := D.largestLabel_eq_of_schur_eq E hD hE he
  have hlabel' : D.row 0 - D.col 2 = E.row 0 - E.col 2 := hlabel
  have hfull : complete (D.row 0 - D.col 2) * complete s * complete t =
      complete (E.row 0 - E.col 2) * complete S * complete T := by
    rw [hlabel']
    simpa only [mul_assoc] using congrArg
      (fun p => complete (E.row 0 - E.col 2) * p) hcorner
  have h01D : D.row 0 - D.col 1 = a + b - s := by dsimp [a, b, s, rowLength]; ring
  have h12D : D.row 1 - D.col 2 = b + c - t := by dsimp [b, c, t, rowLength]; ring
  have h01E : E.row 0 - E.col 1 = A + B - S := by dsimp [A, B, S, rowLength]; ring
  have h12E : E.row 1 - E.col 2 = B + C - T := by dsimp [B, C, T, rowLength]; ring
  have hp : complete (a + b - s) * complete s * complete c +
      complete a * complete (b + c - t) * complete t =
      complete (A + B - S) * complete S * complete C +
      complete A * complete (B + C - T) * complete T := by
    rw [D.schur_three_expansion, E.schur_three_expansion,
      complete_of_neg (sub_neg.mpr hnD), complete_of_neg (sub_neg.mpr hnE),
      h01D, h12D, h01E, h12E] at he
    change complete a * complete b * complete c -
      complete (a + b - s) * complete s * complete c -
      complete a * complete (b + c - t) * complete t +
      complete (D.row 0 - D.col 2) * complete s * complete t +
      complete (a + b - s) * complete (b + c - t) * 0 -
      complete (D.row 0 - D.col 2) * complete b * 0 =
      complete A * complete B * complete C -
      complete (A + B - S) * complete S * complete C -
      complete A * complete (B + C - T) * complete T +
      complete (E.row 0 - E.col 2) * complete S * complete T +
      complete (A + B - S) * complete (B + C - T) * 0 -
      complete (E.row 0 - E.col 2) * complete B * 0 at he
    linear_combination -he + hrow' + hfull
  have hsa : s < a := by
    have := D.row_strictAnti (show (0 : Fin 3) < 1 by decide)
    dsimp [s, a, rowLength]; omega
  have hsb : s < b := by
    have := D.col_strictAnti (show (0 : Fin 3) < 1 by decide)
    dsimp [s, b, rowLength]; omega
  have htb : t < b := by
    have := D.row_strictAnti (show (1 : Fin 3) < 2 by decide)
    dsimp [t, b, rowLength]; omega
  have htc : t < c := by
    have := D.col_strictAnti (show (1 : Fin 3) < 2 by decide)
    dsimp [t, c, rowLength]; omega
  have hSA : S < A := by
    have := E.row_strictAnti (show (0 : Fin 3) < 1 by decide)
    dsimp [S, A, rowLength]; omega
  have hSB : S < B := by
    have := E.col_strictAnti (show (0 : Fin 3) < 1 by decide)
    dsimp [S, B, rowLength]; omega
  have hTB : T < B := by
    have := E.row_strictAnti (show (1 : Fin 3) < 2 by decide)
    dsimp [T, B, rowLength]; omega
  have hTC : T < C := by
    have := E.col_strictAnti (show (1 : Fin 3) < 2 by decide)
    dsimp [T, C, rowLength]; omega
  have hcoarsen := triple_sum_reading
    (show 0 < a + b - s by have := D.rowLength_pos 0; change 0 < a at this; omega)
    hs (D.rowLength_pos 2) (D.rowLength_pos 0)
    (show 0 < b + c - t by have := D.rowLength_pos 2; change 0 < c at this; omega)
    ht
    (show 0 < A + B - S by have := E.rowLength_pos 0; change 0 < A at this; omega)
    hS (E.rowLength_pos 2) (E.rowLength_pos 0)
    (show 0 < B + C - T by have := E.rowLength_pos 2; change 0 < C at this; omega)
    hT hp
  have hneg : s + t < b := by dsimp [s, t, b, rowLength]; omega
  have hNeg : S + T < B := by dsimp [S, T, B, rowLength]; omega
  have hm := negative_profile_reading a b c s t A B C S T
    hs ht hS hT hsa hsb htb htc hSA hSB hTB hTC hneg hNeg hr hg hcoarsen
  dsimp [a, b, c, s, t, A, B, C, S, T, rowLength] at hm
  rcases hm with ⟨ha, hb, hc, hs, ht⟩ | ⟨ha, hb, hc, hs, ht⟩
  · left
    change D.row 0 - D.col 0 = E.row 0 - E.col 0 at ha
    change D.row 1 - D.col 1 = E.row 1 - E.col 1 at hb
    change D.row 2 - D.col 2 = E.row 2 - E.col 2 at hc
    change D.row 1 - D.col 0 = E.row 1 - E.col 0 at hs
    change D.row 2 - D.col 1 = E.row 2 - E.col 1 at ht
    refine ⟨D.col 2 - E.col 2, ?_, ?_⟩
    · intro i
      fin_cases i
      · change D.row 0 = E.row 0 + (D.col 2 - E.col 2)
        omega
      · change D.row 1 = E.row 1 + (D.col 2 - E.col 2)
        omega
      · change D.row 2 = E.row 2 + (D.col 2 - E.col 2)
        omega
    · intro i
      fin_cases i
      · change D.col 0 = E.col 0 + (D.col 2 - E.col 2)
        omega
      · change D.col 1 = E.col 1 + (D.col 2 - E.col 2)
        omega
      · change D.col 2 = E.col 2 + (D.col 2 - E.col 2)
        ring
  · right
    change D.row 0 - D.col 0 = E.row 2 - E.col 2 at ha
    change D.row 1 - D.col 1 = E.row 1 - E.col 1 at hb
    change D.row 2 - D.col 2 = E.row 0 - E.col 0 at hc
    change D.row 1 - D.col 0 = E.row 2 - E.col 1 at hs
    change D.row 2 - D.col 1 = E.row 1 - E.col 0 at ht
    refine ⟨D.row 0 + E.col 2, ?_, ?_⟩
    · intro i
      fin_cases i
      · change D.row 0 = D.row 0 + E.col 2 - E.col 2
        ring
      · change D.row 1 = D.row 0 + E.col 2 - E.col 1
        omega
      · change D.row 2 = D.row 0 + E.col 2 - E.col 0
        omega
    · intro i
      fin_cases i
      · change D.col 0 = D.row 0 + E.col 2 - E.row 2
        omega
      · change D.col 1 = D.row 0 + E.col 2 - E.row 1
        omega
      · change D.col 2 = D.row 0 + E.col 2 - E.row 0
        omega

/-- Gamma discharges every positive-parameter boundary and every common beta entry. -/
theorem rigidity_three (D E : BetaDiagram 3)
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  have h := D.gamma.rigidity_three_zeroFree E.gamma
    (D.gamma_connected_iff.mpr hD) (E.gamma_connected_iff.mpr hE)
    D.gamma_zeroFree E.gamma_zeroFree
    ((D.gamma_schur_eq_iff_same_order E hD hE).mpr he)
  rcases h with h | h
  · exact Or.inl ((D.gamma_translation_iff E).mp h)
  · exact Or.inr ((D.gamma_rotation_iff E).mp h)

end BetaDiagram
end SkewJacobiNegative
