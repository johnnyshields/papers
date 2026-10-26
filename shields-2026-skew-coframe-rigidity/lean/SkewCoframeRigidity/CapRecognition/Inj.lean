/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Support

/-!
# A scalar multiple of the numerator determines the cap

If the numerators of two weak caps agree up to a nonzero rational scalar `q`, and so do their
board determinants, the caps coincide.  The number of caps' columns is the size of the
`z`-support, `Y_1` is its top exponent, `X_1` the top label, and the condensation identity passes
the relation to the tails.  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence MvPolynomial

theorem ι_C (q : ℚ) : ι (C q) = (C q : J) := by
  unfold ι
  exact rename_C _ _

theorem ι_C_mul (q : ℚ) (s : CompleteRing) : ι (C q * s) = C q * ι s := by
  rw [map_mul, ι_C]

namespace WeakCap

theorem coefZ_num_Y0 {m : ℕ} (c : WeakCap (m + 1)) :
    coefZ (c.Y 0).toNat c.num = (-1 : CompleteRing) ^ (m + 1) * c.minor 0 := by
  have := c.coefZ_num_Y 0
  simpa using this

theorem not_dvd_ι {m : ℕ} (c : WeakCap (m + 1)) {s : CompleteRing} (hs : s ≠ 0) :
    ¬ c.num ∣ ι s := by
  intro h
  have hz : none ∉ c.num.vars :=
    notMem_vars_of_dvd ((map_ne_zero_iff _ ι_injective).mpr hs) h (ι_notMem_none s)
  have hsub : (↑c.num.vars : Set (Option ℕ+)) ⊆ Set.range some := by
    intro x hx
    rcases x with _ | y
    · exact absurd hx hz
    · exact ⟨y, rfl⟩
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range c.num some (Option.some_injective _) hsub
  have hnum : c.num = ι q := hq.symm
  have h1 := coefZ_num_Y0 c
  have hY0 := c.Y_pos 0
  rw [hnum, coefZ_ι_of_ne (by omega)] at h1
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (c.minor_ne_zero 0) h1.symm

end WeakCap

theorem cross_mul_of_ratio_eq {a b a' b' : J} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (h : algebraMap J (FractionRing J) a / algebraMap J (FractionRing J) b =
      algebraMap J (FractionRing J) a' / algebraMap J (FractionRing J) b') :
    a * b' = a' * b := by
  have hb1 : algebraMap J (FractionRing J) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective J (FractionRing J))).mpr hb
  have hb2 : algebraMap J (FractionRing J) b' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective J (FractionRing J))).mpr hb'
  rw [div_eq_div_iff hb1 hb2] at h
  apply IsFractionRing.injective J (FractionRing J)
  simpa using h

namespace WeakCap

theorem exists_scalar {m m' : ℕ} (c : WeakCap (m + 1)) (c' : WeakCap (m' + 1))
    (h : c.num * ι c'.detA = c'.num * ι c.detA) :
    ∃ q : ℚ, q ≠ 0 ∧ c'.num = C q * c.num ∧ ι c'.detA = C q * ι c.detA := by
  have hp : Prime c.num := UniqueFactorizationMonoid.irreducible_iff_prime.mp c.num_irreducible
  have hp' : Prime c'.num := UniqueFactorizationMonoid.irreducible_iff_prime.mp c'.num_irreducible
  have h1 : c.num ∣ c'.num := by
    have : c.num ∣ c'.num * ι c.detA := ⟨_, h.symm⟩
    exact (hp.dvd_or_dvd this).resolve_right (c.not_dvd_ι c.detA_ne_zero)
  have h2 : c'.num ∣ c.num := by
    have : c'.num ∣ c.num * ι c'.detA := ⟨_, h⟩
    exact (hp'.dvd_or_dvd this).resolve_right (c'.not_dvd_ι c'.detA_ne_zero)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd h1 h2
  obtain ⟨q, hq, hqu⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hnum : c'.num = C q * c.num := by rw [← hu, hqu, mul_comm]
  refine ⟨q, hq.ne_zero, hnum, ?_⟩
  have h0 : c.num ≠ 0 := hp.ne_zero
  apply mul_left_cancel₀ h0
  rw [h, hnum]
  ring

theorem support_eq {m m' : ℕ} (c : WeakCap m) (c' : WeakCap m') (q : ℚ) (hq : q ≠ 0)
    (h : c'.num = C q * c.num) : (φ c'.num).support = (φ c.num).support := by
  ext k
  rw [Polynomial.mem_support_iff, Polynomial.mem_support_iff]
  have h1 : (φ c'.num).coeff k = C q * (φ c.num).coeff k := by
    have := coefZ_C_mul q k c.num
    simpa [coefZ, h] using this
  have hC : (C q : CompleteRing) ≠ 0 := fun h0 => hq (by simpa using h0)
  rw [h1]
  exact ⟨fun h2 h3 => h2 (by rw [h3, mul_zero]), fun h2 h3 => h2 ((mul_eq_zero.mp h3).resolve_left hC)⟩

theorem length_eq {m m' : ℕ} (c : WeakCap m) (c' : WeakCap m') (q : ℚ) (hq : q ≠ 0)
    (h : c'.num = C q * c.num) : m = m' := by
  have h1 := congrArg Finset.card (c.support_eq c' q hq h)
  rw [card_support_num, card_support_num] at h1
  omega

theorem Y0_le {m : ℕ} (c c' : WeakCap (m + 1)) (hs : (φ c'.num).support = (φ c.num).support) :
    c.Y 0 ≤ c'.Y 0 := by
  have hmem : (c.Y 0).toNat ∈ (φ c.num).support := by
    rw [support_num]
    exact Finset.mem_image.mpr ⟨(0 : Fin (m + 1)).castSucc, Finset.mem_univ _,
      congrArg Int.toNat (c.cols_castSucc 0)⟩
  rw [← hs, support_num] at hmem
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmem
  have h1 : c'.cols p ≤ c'.cols 0 := c'.cols_anti.antitone (Fin.zero_le p)
  have h2 : c'.cols 0 = c'.Y 0 := c'.cols_castSucc 0
  have h3 := c'.cols_nonneg p
  have h4 := c.Y_pos 0
  omega

theorem X0_le {m : ℕ} (c c' : WeakCap (m + 1)) (q : ℚ) (hq : q ≠ 0)
    (h : c'.num = C q * c.num) :
    c.X 0 ≤ c'.X 0 := by
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < c.X 0 := c.X_pos 0
  have hz : pderiv (lvar (c.X 0) hpos) c'.num = 0 :=
    pderiv_eq_zero_of_notMem_vars ((c'.num_noLabel hlt).notMem hpos)
  rw [h, pderiv_C_mul, c.pderiv_num hpos rfl] at hz
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact hq (by simpa using h0)
  · exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) c.aux_ne_zero h0

theorem X0_eq {m : ℕ} (c c' : WeakCap (m + 1)) (q : ℚ) (hq : q ≠ 0)
    (h : c'.num = C q * c.num) : c.X 0 = c'.X 0 := by
  refine le_antisymm (X0_le c c' q hq h) (X0_le c' c q⁻¹ (inv_ne_zero hq) ?_)
  rw [h, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hq]
  simp

theorem tail_rel {m : ℕ} (c c' : WeakCap (m + 1)) (q : ℚ) (hq : q ≠ 0)
    (hnum : c'.num = C q * c.num) (hdet : ι c'.detA = C q * ι c.detA)
    (hY : c.Y 0 = c'.Y 0) (hX : c.X 0 = c'.X 0) :
    c'.tail.num = C q * c.tail.num ∧ ι c'.tail.detA = C q * ι c.tail.detA := by
  have hpos : 0 < c.X 0 := c.X_pos 0
  have hCq : (C q : J) ≠ 0 := fun h0 => hq (by simpa using h0)
  have hCqS : (C q : CompleteRing) ≠ 0 := fun h0 => hq (by simpa using h0)
  -- the corner coefficients
  have haux : c'.aux = C q * c.aux := by
    have h1 := c'.pderiv_num hpos hX
    rw [hnum, pderiv_C_mul, c.pderiv_num hpos rfl] at h1
    have hu : ((-1 : J) ^ (m + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    apply mul_left_cancel₀ hu
    rw [← h1]
    ring
  have hdetT : c'.tail.detA = C q * c.tail.detA := by
    have h1 := c'.coefZ_aux
    rw [← hY, haux, coefZ_C_mul, c.coefZ_aux] at h1
    have hu : ((-1 : CompleteRing) ^ m) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    apply mul_left_cancel₀ hu
    rw [← h1]
    ring
  have hdetT' : ι c'.tail.detA = C q * ι c.tail.detA := by
    rw [hdetT, ι_C_mul]
  have hmin : ι (c'.minor 0) = C q * ι (c.minor 0) := by
    have h1 := c'.coefZ_num_Y0
    rw [← hY, hnum, coefZ_C_mul, c.coefZ_num_Y0] at h1
    have hu : ((-1 : CompleteRing) ^ (m + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    have : c'.minor 0 = C q * c.minor 0 := by
      apply mul_left_cancel₀ hu
      rw [← h1]
      ring
    rw [this, ι_C_mul]
  refine ⟨?_, hdetT'⟩
  have hdj := c.num_dj
  have hdj' := c'.num_dj
  rw [hnum, hdetT', haux, hmin, hdet] at hdj'
  have hne : C q * ι c.detA ≠ 0 :=
    mul_ne_zero hCq ((map_ne_zero_iff _ ι_injective).mpr c.detA_ne_zero)
  apply mul_left_cancel₀ hne
  linear_combination (-1 : J) * hdj' + (C q) ^ 2 * hdj

theorem eq_of_scalar : ∀ (m : ℕ) (c c' : WeakCap m) (q : ℚ), q ≠ 0 → c'.num = C q * c.num →
    ι c'.detA = C q * ι c.detA → c = c' := by
  intro m
  induction m with
  | zero =>
    intro c c' _ _ _ _
    exact ext' (funext fun i => i.elim0) (funext fun i => i.elim0)
  | succ m ih =>
    intro c c' q hq hnum hdet
    have hs := c.support_eq c' q hq hnum
    have hY : c.Y 0 = c'.Y 0 := le_antisymm (Y0_le c c' hs) (Y0_le c' c hs.symm)
    have hX : c.X 0 = c'.X 0 := X0_eq c c' q hq hnum
    obtain ⟨h1, h2⟩ := tail_rel c c' q hq hnum hdet hY hX
    have ht := ih c.tail c'.tail q hq h1 h2
    have htX := congrArg WeakCap.X ht
    have htY := congrArg WeakCap.Y ht
    refine ext' (funext fun i => ?_) (funext fun i => ?_)
    · induction i using Fin.cases with
      | zero => exact hX
      | succ k => exact congrFun htX k
    · induction i using Fin.cases with
      | zero => exact hY
      | succ k => exact congrFun htY k

/-- Cross-multiplied equality of ratios determines the lengths and the caps. -/
theorem eq_of_cross : ∀ {r r' : ℕ} (c : WeakCap r) (c' : WeakCap r'),
    c.num * ι c'.detA = c'.num * ι c.detA → ∃ e : r = r', e ▸ c = c' := by
  intro r r' c c' h
  rcases r with _ | m <;> rcases r' with _ | m'
  · exact ⟨rfl, ext' (funext fun i => i.elim0) (funext fun i => i.elim0)⟩
  · exfalso
    rw [num_zero, detA_zero, map_one, one_mul, mul_one] at h
    have h1 := coefZ_num_Y0 c'
    have hY0 := c'.Y_pos 0
    rw [← h, coefZ_ι_of_ne (by omega)] at h1
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (c'.minor_ne_zero 0) h1.symm
  · exfalso
    rw [num_zero, detA_zero, map_one, one_mul, mul_one] at h
    have h1 := coefZ_num_Y0 c
    have hY0 := c.Y_pos 0
    rw [h, coefZ_ι_of_ne (by omega)] at h1
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (c.minor_ne_zero 0) h1.symm
  · obtain ⟨q, hq, hnum, hdet⟩ := exists_scalar c c' h
    have hm := length_eq c c' q hq hnum
    obtain rfl : m = m' := by omega
    exact ⟨rfl, eq_of_scalar _ c c' q hq hnum hdet⟩

end WeakCap

end SkewCoframeRigidity.CapRecognition
