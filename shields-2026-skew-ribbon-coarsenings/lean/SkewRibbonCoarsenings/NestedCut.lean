/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Setting

/-!
# Cut functions at natural-number arguments

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector` (`thm:nested`): the
pointwise facts about `b`, the mask `𝓑_p`, and `w` that the nested marked identity consumes.
All arguments are natural numbers (block sums) cast into `ℤ/n`.  The facts are: off the `p`-grid
the mask equals `b`, on it the mask vanishes, a period of the mask moves the argument by any
multiple, `w` vanishes on the `e`-grid, the reflection `eq:mask-odd`, and the ternary and
disjointness properties used in the bound `|H| ≤ 2`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

namespace Nested

open Finset

section Cut

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

lemma val_natCast_dvd [NeZero n] {p : ℕ} (hp : p ∣ n) (t : ℕ) :
    p ∣ ((t : ℕ) : ZMod n).val ↔ p ∣ t := by
  rw [ZMod.val_natCast]; exact Nat.dvd_mod_iff hp

lemma maskFun_nat_of_dvd [NeZero n] {p : ℕ} (hp : p ∣ n) {t : ℕ} (ht : p ∣ t) :
    maskFun n S p (t : ZMod n) = 0 := by
  unfold maskFun; rw [if_pos ((val_natCast_dvd hp t).mpr ht)]

lemma maskFun_nat_of_ndvd [NeZero n] {p : ℕ} (hp : p ∣ n) {t : ℕ} (ht : ¬ p ∣ t) :
    maskFun n S p (t : ZMod n) = cutInd n S (t : ZMod n) := by
  unfold maskFun; rw [if_neg (fun h => ht ((val_natCast_dvd hp t).mp h))]

lemma isPeriod_mul_cast {f : ZMod n → ℤ} {q : ℕ} (hq : IsPeriod f q) (k : ℕ) (z : ZMod n) :
    f (z + ((k * q : ℕ) : ZMod n)) = f z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : (((k + 1) * q : ℕ) : ZMod n) = ((k * q : ℕ) : ZMod n) + (q : ZMod n) := by
      push_cast; ring
    rw [this, ← add_assoc, hq, ih]

/-- A period `q` of `f` absorbs any natural multiple of `q` added to the argument. -/
lemma isPeriod_add_dvd {f : ZMod n → ℤ} {q A : ℕ} (hq : IsPeriod f q) (hA : q ∣ A)
    (z : ZMod n) : f (z + (A : ZMod n)) = f z := by
  obtain ⟨k, rfl⟩ := hA
  rw [mul_comm]
  exact isPeriod_mul_cast hq k z

lemma cutInd_cases (S : Finset ℕ) (x : ZMod n) : cutInd n S x = 0 ∨ cutInd n S x = 1 := by
  unfold cutInd; split_ifs <;> simp

lemma maskFun_cases (S : Finset ℕ) (p : ℕ) (x : ZMod n) :
    maskFun n S p x = 0 ∨ maskFun n S p x = 1 := by
  unfold maskFun; split_ifs
  · exact Or.inl rfl
  · exact cutInd_cases S x

lemma wFun_ternary (S S' : Finset ℕ) (d : ℕ) (x : ZMod n) :
    wFun n S S' d x = -1 ∨ wFun n S S' d x = 0 ∨ wFun n S S' d x = 1 := by
  unfold wFun uFun
  split_ifs
  · exact Or.inr (Or.inl rfl)
  · rcases cutInd_cases (n := n) S x with h | h <;>
      rcases cutInd_cases (n := n) S' (-x) with h' | h' <;> simp [h, h']

lemma wFun_nat_of_dvd_e [NeZero n] (h : NormalizedSetting n S S' d e) {t : ℕ} (ht : e ∣ t) :
    wFun n S S' d (t : ZMod n) = 0 := by
  obtain ⟨k, rfl⟩ := ht
  have h0 : wFun n S S' d 0 = 0 := by
    have := h.w_odd 0
    rw [neg_zero] at this
    omega
  have := isPeriod_mul_cast h.e_least.2.2.1 k 0
  rw [zero_add] at this
  rw [mul_comm e k, this, h0]

lemma dvd_val_iff_hom [NeZero n] {p : ℕ} (hp : p ∣ n) (x : ZMod n) :
    p ∣ x.val ↔ ZMod.castHom hp (ZMod p) x = 0 := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]

lemma not_dvd_val_sub [NeZero n] {p A z : ℕ} (hp : p ∣ n) (hA : p ∣ A) (hz : ¬ p ∣ z) :
    ¬ p ∣ ((A : ZMod n) - (z : ZMod n)).val := by
  rw [dvd_val_iff_hom hp]
  intro h
  rw [map_sub, map_natCast, map_natCast] at h
  have hA' : ((A : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hA
  rw [hA', zero_sub, neg_eq_zero, ZMod.natCast_eq_zero_iff] at h
  exact hz h

lemma not_dvd_val_neg [NeZero n] {p z : ℕ} (hp : p ∣ n) (hz : ¬ p ∣ z) :
    ¬ p ∣ (-(z : ZMod n)).val := by
  have := not_dvd_val_sub (n := n) hp (dvd_zero p) hz
  simpa using this

/-- Reflecting an argument across a multiple `A` of a period of the mask: off the `p`-grid the mask
agrees with `b`, so `b(A - z) = b(-z)`. -/
lemma cutInd_sub_of_period [NeZero n] {p q A z : ℕ} (hp : p ∣ n)
    (hper : IsPeriod (maskFun n S p) q) (hpq : p ∣ q) (hqA : q ∣ A) (hz : ¬ p ∣ z) :
    cutInd n S ((A : ZMod n) - z) = cutInd n S (-(z : ZMod n)) := by
  have h1 : maskFun n S p ((A : ZMod n) - z) = cutInd n S ((A : ZMod n) - z) := by
    unfold maskFun; rw [if_neg (not_dvd_val_sub hp (hpq.trans hqA) hz)]
  have h2 : maskFun n S p (-(z : ZMod n)) = cutInd n S (-(z : ZMod n)) := by
    unfold maskFun; rw [if_neg (not_dvd_val_neg hp hz)]
  have h3 : (A : ZMod n) - z = -(z : ZMod n) + A := by ring
  rw [← h1, ← h2, h3]
  exact isPeriod_add_dvd hper hqA _

/-- Off the `p`-grid, adding a multiple of a period of the mask does not change `b`. -/
lemma cutInd_add_of_period [NeZero n] {p q A σ : ℕ} (hp : p ∣ n)
    (hper : IsPeriod (maskFun n S p) q) (hpq : p ∣ q) (hqA : q ∣ A) (hσ : ¬ p ∣ σ) :
    cutInd n S ((A + σ : ℕ) : ZMod n) = cutInd n S (σ : ZMod n) := by
  have hAσ : ¬ p ∣ A + σ := fun h => hσ ((Nat.dvd_add_right (hpq.trans hqA)).mp h)
  have h1 : maskFun n S p ((A + σ : ℕ) : ZMod n) = cutInd n S ((A + σ : ℕ) : ZMod n) :=
    maskFun_nat_of_ndvd hp hAσ
  have h2 : maskFun n S p (σ : ZMod n) = cutInd n S (σ : ZMod n) := maskFun_nat_of_ndvd hp hσ
  rw [← h1, ← h2, Nat.cast_add, add_comm]
  exact isPeriod_add_dvd hper hqA _

lemma dvd_val_of_ne' [NeZero n] (f : ZMod n → ℤ) {x : ZMod n} (hx : f x ≠ 0) :
    supportGcd f ∣ x.val := by
  unfold supportGcd
  refine (Nat.gcd_dvd_right _ _).trans ?_
  have hmem : x.val ∈ (Finset.range n).filter fun k : ℕ => f (k : ZMod n) ≠ 0 := by
    rw [Finset.mem_filter, Finset.mem_range, ZMod.natCast_zmod_val]
    exact ⟨ZMod.val_lt x, hx⟩
  exact Finset.gcd_dvd (f := id) hmem

lemma d_dvd_n (h : NormalizedSetting n S S' d e) : d ∣ n := by
  rw [h.d_eq]; exact Nat.gcd_dvd_left _ _

lemma vFun_eq_zero_of_ndvd [NeZero n] (h : NormalizedSetting n S S' d e) {z : ℕ}
    (hz : ¬ d ∣ z) : vFun n S S' (z : ZMod n) = 0 := by
  by_contra hne
  have := dvd_val_of_ne' (vFun n S S') hne
  rw [← h.d_eq] at this
  exact hz ((val_natCast_dvd (d_dvd_n h) z).mp this)

lemma dvd_of_vFun_ne [NeZero n] (h : NormalizedSetting n S S' d e) {z : ℕ}
    (hz : vFun n S S' (z : ZMod n) ≠ 0) : d ∣ z := by
  by_contra hd
  exact hz (vFun_eq_zero_of_ndvd h hd)

/-- At an argument on the `e`-grid and off the `d`-grid the cut value is even under reflection. -/
lemma cutInd_neg_of_offgrid [NeZero n] (h : NormalizedSetting n S S' d e) {z : ℕ}
    (hez : e ∣ z) (hdz : ¬ d ∣ z) : cutInd n S (-(z : ZMod n)) = cutInd n S (z : ZMod n) := by
  have hv := vFun_eq_zero_of_ndvd h hdz
  have hw := wFun_nat_of_dvd_e h hez
  have hwu : wFun n S S' d (z : ZMod n) = uFun n S S' (z : ZMod n) := by
    unfold wFun
    rw [if_neg (fun h' => hdz ((val_natCast_dvd (d_dvd_n h) z).mp h'))]
  rw [hwu] at hw
  have htau := h.tau_eq (z : ZMod n)
  unfold uFun at hw
  unfold vFun at hv
  omega

end Cut

end Nested

end SkewRibbonCoarsenings
