/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.NestedJ
import SkewRibbonCoarsenings.NestedCut

/-!
# The bottom three-probe computation

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector` (`thm:nested`, last step
of the proof): `𝓙_y(r, s, z) = -H_y(r, s, z)`.  `chainSum_three` expands the chain sum of three
labels into the six ordered pairs; `pair_term` is the per-pair evaluation (the contribution with
first label `q₁` and last label `q₃`); `JJ_bottom` assembles them.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset Nested

section Three

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R]

lemma chainSum_three (g : ℕ → R) (m : ι → ℕ) {α β γ : ι} (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) :
    chainSum (fun X => g (∑ i ∈ X, m i)) ∅ {α, β, γ} =
      g (m α) * (g (m α + m β) + g (m α + m γ)) + g (m β) * (g (m α + m β) + g (m β + m γ)) +
        g (m γ) * (g (m α + m γ) + g (m β + m γ)) := by
  have hT : ({α, β, γ} : Finset ι).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hαβ, hαγ]), Finset.card_pair hβγ]
  -- chain sums from a singleton vertex to the top
  have top : ∀ {u v w : ι}, u ≠ v → u ≠ w → v ≠ w → ({u, v, w} : Finset ι) = {α, β, γ} →
      chainSum (fun X => g (∑ i ∈ X, m i)) {u} {α, β, γ} =
        g (m u + m v) + g (m u + m w) := by
    intro u v w huv huw hvw hset
    rw [← hset]
    have hd : ({u, v, w} : Finset ι) \ {u} = {v, w} := by
      ext x; simp only [mem_sdiff, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h | h | h, h'⟩
        · exact absurd h h'
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact ⟨Or.inr (Or.inl h), by rw [h]; exact fun e => huv e.symm⟩
        · exact ⟨Or.inr (Or.inr h), by rw [h]; exact fun e => huw e.symm⟩
    rw [chainSum_of_two_le (by rw [hd, Finset.card_pair hvw]), hd, Finset.sum_pair hvw]
    have h1 : chainSum (fun X => g (∑ i ∈ X, m i)) (insert v {u}) {u, v, w} = 1 := by
      apply chainSum_of_card_le
      have : ({u, v, w} : Finset ι) \ insert v {u} = {w} := by
        ext x; simp only [mem_sdiff, mem_insert, mem_singleton]
        constructor
        · rintro ⟨h | h | h, h'⟩
          · exact absurd (Or.inr h) h'
          · exact absurd (Or.inl h) h'
          · exact h
        · rintro rfl
          exact ⟨Or.inr (Or.inr rfl), by rintro (h | h) <;> [exact hvw h.symm; exact huw h.symm]⟩
      rw [this]; simp
    have h2 : chainSum (fun X => g (∑ i ∈ X, m i)) (insert w {u}) {u, v, w} = 1 := by
      apply chainSum_of_card_le
      have : ({u, v, w} : Finset ι) \ insert w {u} = {v} := by
        ext x; simp only [mem_sdiff, mem_insert, mem_singleton]
        constructor
        · rintro ⟨h | h | h, h'⟩
          · exact absurd (Or.inr h) h'
          · exact h
          · exact absurd (Or.inl h) h'
        · rintro rfl
          exact ⟨Or.inr (Or.inl rfl), by rintro (h | h) <;> [exact hvw h; exact huv h.symm]⟩
      rw [this]; simp
    rw [h1, h2]
    simp only [mul_one, Finset.sum_pair huv.symm, Finset.sum_pair huw.symm]
    rw [add_comm (m v) (m u), add_comm (m w) (m u)]
  have hcard : 2 ≤ (({α, β, γ} : Finset ι) \ ∅).card := by rw [Finset.sdiff_empty, hT]; omega
  rw [chainSum_of_two_le hcard, Finset.sdiff_empty, Finset.sum_insert (by simp [hαβ, hαγ]),
    Finset.sum_pair hβγ]
  simp only [insert_empty_eq]
  rw [top hαβ hαγ hβγ rfl, top (u := β) (v := α) (w := γ) hαβ.symm hβγ hαγ
      (by rw [Finset.insert_comm]),
    top (u := γ) (v := α) (w := β) hαγ.symm hβγ.symm hαβ
      (by rw [Finset.insert_comm, Finset.pair_comm, Finset.insert_comm, Finset.pair_comm])]
  simp only [Finset.sum_singleton]
  ring_nf

end Three

section Bottom3

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

/-- Off the `p`-grid the reflected cut value is `b(-q) = b(q) - w(q)`
(`eq:mask-odd` of `prop:normalization` at the mask `𝓑_p`). -/
lemma cutInd_neg_eq [NeZero n] (h : NormalizedSetting n S S' d e) {p : ℕ} (hpn : p ∣ n)
    (hep : e ∣ p) (hpd : p ∣ d) {q : ℕ} (hq : ¬ p ∣ q) :
    cutInd n S (-(q : ZMod n)) = cutInd n S (q : ZMod n) - wFun n S S' d (q : ZMod n) := by
  have := h.mask_odd p hep hpd (q : ZMod n)
  rw [maskFun_nat_of_ndvd hpn hq] at this
  have h2 : maskFun n S p (-(q : ZMod n)) = cutInd n S (-(q : ZMod n)) := by
    unfold maskFun; rw [if_neg (not_dvd_val_neg hpn hq)]
  rw [h2] at this
  linarith

/-- `w` is unchanged by adding a multiple of its period `e`. -/
lemma wFun_add_of_dvd (h : NormalizedSetting n S S' d e) {y : ℕ} (q : ℕ) (hy : e ∣ y) :
    wFun n S S' d ((y + q : ℕ) : ZMod n) = wFun n S S' d (q : ZMod n) := by
  have := isPeriod_add_dvd h.e_least.2.2.1 hy (q : ZMod n)
  rw [Nat.cast_add, add_comm]
  exact this

/-- The function `f_y(x) = 𝓑_e(x + y) - 𝓑_e(x)` of `eq:deltaH`, at a natural argument `x`. -/
def fY (n : ℕ) (S : Finset ℕ) (e y x : ℕ) : ℤ :=
  maskFun n S e ((x + y : ℕ) : ZMod n) - maskFun n S e (x : ZMod n)

/-- `H_y(r, s, z)` of `eq:deltaH`. -/
def Hfun (n : ℕ) (S S' : Finset ℕ) (d e y r s z : ℕ) : ℤ :=
  fY n S e y r * (wFun n S S' d (s : ZMod n) + wFun n S S' d (z : ZMod n)) +
    fY n S e y s * (wFun n S S' d (r : ZMod n) + wFun n S S' d (z : ZMod n)) +
      fY n S e y z * (wFun n S S' d (r : ZMod n) + wFun n S S' d (s : ZMod n))

lemma fY_eq [NeZero n] {y x : ℕ} (hen : e ∣ n) (hy : e ∣ y) (hx : ¬ e ∣ x) :
    fY n S e y x = cutInd n S ((y + x : ℕ) : ZMod n) - cutInd n S (x : ZMod n) := by
  unfold fY
  have hxy : ¬ e ∣ x + y := fun h' => hx ((Nat.dvd_add_left hy).mp h')
  rw [maskFun_nat_of_ndvd hen hxy, maskFun_nat_of_ndvd hen hx, add_comm x y]

/-- The contribution of one ordered pair of bottom labels, with first label `q₁`, last label `q₃`,
and `Q = q₁ + q₂` the sum of the first two: with `y + q₁ + q₂ + q₃ ≡ 0 (mod p₁)` this is
`f_y(q₁) b(q₃) - b(q₁) f_y(q₃) - f_y(q₁) w(q₃)`. -/
lemma pair_term [NeZero n] (h : NormalizedSetting n S S' d e) {p₁ y R q₁ Q q₃ : ℕ}
    (hen : e ∣ n) (hed : e ∣ d) (hep : e ∣ p₁)
    (hper : IsPeriod (maskFun n S e) p₁) (hp1 : p₁ ∣ y + R)
    (hy : e ∣ y) (h1 : ¬ e ∣ q₁) (h3 : ¬ e ∣ q₃) (hQ : Q + q₃ = R) :
    cutInd n S ((y + q₁ : ℕ) : ZMod n) * cutInd n S ((y + Q : ℕ) : ZMod n) -
        cutInd n S (q₁ : ZMod n) * cutInd n S (Q : ZMod n) =
      (cutInd n S ((y + q₁ : ℕ) : ZMod n) - cutInd n S (q₁ : ZMod n)) *
          cutInd n S (q₃ : ZMod n) -
        cutInd n S (q₁ : ZMod n) *
          (cutInd n S ((y + q₃ : ℕ) : ZMod n) - cutInd n S (q₃ : ZMod n)) -
        (cutInd n S ((y + q₁ : ℕ) : ZMod n) - cutInd n S (q₁ : ZMod n)) *
          wFun n S S' d (q₃ : ZMod n) := by
  have h3' : ¬ e ∣ y + q₃ := fun h' => h3 ((Nat.dvd_add_right hy).mp h')
  have hA : ((y + Q : ℕ) : ZMod n) = ((y + R : ℕ) : ZMod n) - (q₃ : ZMod n) := by
    rw [← hQ]; push_cast; ring
  have hB : ((Q : ℕ) : ZMod n) = ((y + R : ℕ) : ZMod n) - ((y + q₃ : ℕ) : ZMod n) := by
    rw [← hQ]; push_cast; ring
  have e1 : cutInd n S ((y + Q : ℕ) : ZMod n) = cutInd n S (-(q₃ : ZMod n)) := by
    rw [hA]; exact cutInd_sub_of_period hen hper hep hp1 h3
  have e2 : cutInd n S (Q : ZMod n) = cutInd n S (-((y + q₃ : ℕ) : ZMod n)) := by
    rw [hB]; exact cutInd_sub_of_period hen hper hep hp1 h3'
  rw [e1, e2, cutInd_neg_eq h hen dvd_rfl hed h3, cutInd_neg_eq h hen dvd_rfl hed h3',
    wFun_add_of_dvd h q₃ hy]
  ring

/-- `f_y` and `w` are disjoint: a nonzero value of `w` forces the binary cut value, which is
unchanged by an `e`-multiple shift. -/
lemma fY_mul_w [NeZero n] (h : NormalizedSetting n S S' d e) {y x : ℕ} (hen : e ∣ n)
    (hy : e ∣ y) (hx : ¬ e ∣ x) : fY n S e y x * wFun n S S' d (x : ZMod n) = 0 := by
  have hxy : ¬ e ∣ y + x := fun h' => hx ((Nat.dvd_add_right hy).mp h')
  rw [fY_eq hen hy hx]
  have n1 := cutInd_neg_eq h hen dvd_rfl h.e_dvd_d hx
  have n2 := cutInd_neg_eq h hen dvd_rfl h.e_dvd_d hxy
  rw [wFun_add_of_dvd h x hy] at n2
  rcases cutInd_cases (n := n) S (x : ZMod n) with a1 | a1 <;>
  rcases cutInd_cases (n := n) S (-(x : ZMod n)) with a2 | a2 <;>
  rcases cutInd_cases (n := n) S ((y + x : ℕ) : ZMod n) with a3 | a3 <;>
  rcases cutInd_cases (n := n) S (-((y + x : ℕ) : ZMod n)) with a4 | a4 <;>
  simp only [a1, a2, a3, a4] at n1 n2 ⊢ <;> omega

lemma fY_cases [NeZero n] (S : Finset ℕ) (e y x : ℕ) :
    fY n S e y x = -1 ∨ fY n S e y x = 0 ∨ fY n S e y x = 1 := by
  unfold fY
  rcases maskFun_cases (n := n) S e ((x + y : ℕ) : ZMod n) with a | a <;>
  rcases maskFun_cases (n := n) S e (x : ZMod n) with b | b <;> omega

/-- The bound `|H| ≤ 2` for disjoint ternary functions on three positions. -/
lemma H_bound_aux (f₁ f₂ f₃ w₁ w₂ w₃ : ℤ) (hf₁ : f₁ = -1 ∨ f₁ = 0 ∨ f₁ = 1)
    (hf₂ : f₂ = -1 ∨ f₂ = 0 ∨ f₂ = 1) (hf₃ : f₃ = -1 ∨ f₃ = 0 ∨ f₃ = 1)
    (hw₁ : w₁ = -1 ∨ w₁ = 0 ∨ w₁ = 1) (hw₂ : w₂ = -1 ∨ w₂ = 0 ∨ w₂ = 1)
    (hw₃ : w₃ = -1 ∨ w₃ = 0 ∨ w₃ = 1) (h₁ : f₁ * w₁ = 0) (h₂ : f₂ * w₂ = 0) (h₃ : f₃ * w₃ = 0) :
    |f₁ * (w₂ + w₃) + f₂ * (w₁ + w₃) + f₃ * (w₁ + w₂)| ≤ 2 := by
  rcases hf₁ with rfl | rfl | rfl <;> rcases hf₂ with rfl | rfl | rfl <;>
  rcases hf₃ with rfl | rfl | rfl <;> rcases hw₁ with rfl | rfl | rfl <;>
  rcases hw₂ with rfl | rfl | rfl <;> rcases hw₃ with rfl | rfl | rfl <;>
  simp_all

/-- The bottom step of `thm:nested`: `𝓙_y(r, s, z) = -H_y(r, s, z)`, for three distinct
positions carrying `r, s, z` (all off the `e`-grid), `e ∣ y`, and `p₁ ∣ y + r + s + z` with `p₁` a
period of `𝓑_e`.  Numerical coincidences among the labels are allowed. -/
theorem JJ_bottom [NeZero n] (h : NormalizedSetting n S S' d e)
    {ι : Type*} [DecidableEq ι] {α β γ : ι} (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (m : ι → ℕ) {p₁ y : ℕ} (hen : e ∣ n) (hed : e ∣ d) (hep : e ∣ p₁)
    (hper : IsPeriod (maskFun n S e) p₁) (hp1 : p₁ ∣ y + (m α + m β + m γ))
    (hy : e ∣ y) (hα : ¬ e ∣ m α) (hβ : ¬ e ∣ m β) (hγ : ¬ e ∣ m γ) :
    JJ n S m y {α, β, γ} = - Hfun n S S' d e y (m α) (m β) (m γ) := by
  unfold JJ Hfun
  rw [chainSum_three (fun t => cutInd n S ((y + t : ℕ) : ZMod n)) m hαβ hαγ hβγ,
    chainSum_three (fun t => cutInd n S ((t : ℕ) : ZMod n)) m hαβ hαγ hβγ,
    fY_eq hen hy hα, fY_eq hen hy hβ, fY_eq hen hy hγ]
  have pt : ∀ {q₁ Q q₃ : ℕ}, ¬ e ∣ q₁ → ¬ e ∣ q₃ → Q + q₃ = m α + m β + m γ →
      cutInd n S ((y + q₁ : ℕ) : ZMod n) * cutInd n S ((y + Q : ℕ) : ZMod n) -
          cutInd n S (q₁ : ZMod n) * cutInd n S (Q : ZMod n) =
        (cutInd n S ((y + q₁ : ℕ) : ZMod n) - cutInd n S (q₁ : ZMod n)) *
            cutInd n S (q₃ : ZMod n) -
          cutInd n S (q₁ : ZMod n) *
            (cutInd n S ((y + q₃ : ℕ) : ZMod n) - cutInd n S (q₃ : ZMod n)) -
          (cutInd n S ((y + q₁ : ℕ) : ZMod n) - cutInd n S (q₁ : ZMod n)) *
            wFun n S S' d (q₃ : ZMod n) :=
    fun h1 h3 hQ => pair_term h hen hed hep hper hp1 hy h1 h3 hQ
  have e1 := pt (q₁ := m α) (Q := m α + m β) (q₃ := m γ) hα hγ (by ring)
  have e2 := pt (q₁ := m α) (Q := m α + m γ) (q₃ := m β) hα hβ (by ring)
  have e3 := pt (q₁ := m β) (Q := m α + m β) (q₃ := m γ) hβ hγ (by ring)
  have e4 := pt (q₁ := m β) (Q := m β + m γ) (q₃ := m α) hβ hα (by ring)
  have e5 := pt (q₁ := m γ) (Q := m α + m γ) (q₃ := m β) hγ hβ (by ring)
  have e6 := pt (q₁ := m γ) (Q := m β + m γ) (q₃ := m α) hγ hα (by ring)
  linear_combination e1 + e2 + e3 + e4 + e5 + e6

end Bottom3

end SkewRibbonCoarsenings
