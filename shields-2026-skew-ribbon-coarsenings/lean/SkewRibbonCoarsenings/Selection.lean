/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.BottomProbes

/-!
# Least periods select nonzero probes

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector`
(`eq:chain`, `lem:selection`, `eq:probe-bounds`, `eq:sum-congruence`).

`MaskChain` is the strict divisibility chain of `eq:chain`; `thetaProbe` is `θ_i` of `eq:deltaH`.
Probes are natural numbers, taken as elements of `ℤ/n` by the cast.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset FourStart

/-- `eq:chain`: the chain `e = p₀ < p₁ < ⋯ < p_L = P ∣ d`, `L ≥ 1`, each term dividing the next,
with `𝓑_{p_i}` being `p_{i+1}`-periodic for `0 ≤ i < L`.  These are period hypotheses, not
least-period hypotheses. -/
structure MaskChain (n : ℕ) (S : Finset ℕ) (d e L : ℕ) (p : ℕ → ℕ) : Prop where
  one_le : 1 ≤ L
  p_zero : p 0 = e
  lt : ∀ i, i < L → p i < p (i + 1)
  dvd : ∀ i, i < L → p i ∣ p (i + 1)
  dvd_d : p L ∣ d
  periodic : ∀ i, i < L → IsPeriod (maskFun n S (p i)) (p (i + 1))

/-- `θ_i = 𝓑_{p_{i+1}}(y_i + y_{i+1}) - 𝓑_{p_{i+1}}(y_i)` of `eq:deltaH`, in terms of the
`i`-th and `(i+1)`-st probe and the modulus `q = p_{i+1}`. -/
def thetaProbe (n : ℕ) (S : Finset ℕ) (q yi yi' : ℕ) : ℤ :=
  maskFun n S q ((yi + yi' : ℕ) : ZMod n) - maskFun n S q (yi : ZMod n)

section Selection

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ}

lemma MaskChain.dvd_le (hc : MaskChain n S d e L p) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) :
    p i ∣ p j := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hc.dvd j (by omega))

lemma MaskChain.dvd_n (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p) {i : ℕ}
    (hi : i ≤ L) : p i ∣ n := by
  have h1 := hc.dvd_le hi le_rfl
  exact (h1.trans hc.dvd_d).trans h.d_dvd_n

/-- The step of the downward selection: given `y₁` with `p_{i+1} ∣ y₁` and `p_{i+2} ∤ y₁`, where
`𝓑_{p_{i+1}}` has least period `p_{i+2}` and `𝓑_{p_i}` has period `p_{i+1}`, there is
`0 < y₀ < p_{i+2}` in `p_i ℤ \ p_{i+1} ℤ` with `θ ≠ 0`. -/
lemma selection_step [NeZero n] {P Q q : ℕ} (hPq : P ∣ q) (hqQ : q ∣ Q) (hQn : Q ∣ n)
    (hperP : IsPeriod (maskFun n S P) q) (hleast : IsLeastPeriod (maskFun n S q) Q) {Y : ℕ}
    (hqY : q ∣ Y) (hQY : ¬ Q ∣ Y) :
    ∃ v : ℕ, 0 < v ∧ v < Q ∧ P ∣ v ∧ ¬ q ∣ v ∧ thetaProbe n S q v Y ≠ 0 := by
  have hQ0 : 0 < Q := hleast.1
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0] at hqQ; have := Nat.eq_zero_of_zero_dvd hqQ; omega
    · exact h0
  set D : ZMod n → ℤ := fun x => maskFun n S q (x + (Y : ZMod n)) - maskFun n S q x with hD
  have hqn : q ∣ n := hqQ.trans hQn
  have hPn : P ∣ n := hPq.trans hqn
  have hYq : q ∣ (Y : ZMod n).val := (nat_dvd_iff_val hqn Y).mp hqY
  have hYP : P ∣ (Y : ZMod n).val := hPq.trans hYq
  have hDne : ∃ x : ZMod n, D x ≠ 0 := by
    by_contra hall
    push Not at hall
    have hmem : (Y : ZMod n) ∈ periodGroup (maskFun n S q) := by
      intro x
      have := hall x
      simp only [hD] at this
      omega
    have := dvd_of_mem_periodGroup hleast hmem
    exact hQY ((nat_dvd_iff_val hQn Y).mpr this)
  obtain ⟨x, hx⟩ := hDne
  have hxq : ¬ q ∣ x.val := by
    intro hxq
    apply hx
    have h1 : q ∣ (x + (Y : ZMod n)).val := (dvd_val_add hqn hYq).mpr hxq
    simp only [hD]
    rw [maskFun_of_dvd h1, maskFun_of_dvd hxq]; ring
  have hxP : P ∣ x.val := by
    by_contra hxP
    apply hx
    have hxy : ¬ P ∣ (x + (Y : ZMod n)).val := fun hh => hxP ((dvd_val_add hPn hYP).mp hh)
    have hxyq : ¬ q ∣ (x + (Y : ZMod n)).val := fun hh => hxP (hPq.trans ((dvd_val_add hqn hYq).mp hh))
    have hpp := period_of_dvd_val hperP hYq x
    rw [maskFun_of_not_dvd hxP, maskFun_of_not_dvd hxy] at hpp
    simp only [hD]
    rw [maskFun_of_not_dvd hxq, maskFun_of_not_dvd hxyq, hpp]; ring
  have hperD : IsPeriod D Q := by
    intro y
    simp only [hD]
    have h1 := hleast.2.2.1 y
    have h2 := hleast.2.2.1 (y + (Y : ZMod n))
    rw [show y + (Q : ZMod n) + (Y : ZMod n) = y + (Y : ZMod n) + (Q : ZMod n) by ring, h2, h1]
  set v := x.val % Q with hv
  have hvQ : v < Q := Nat.mod_lt _ hQ0
  have hPv : P ∣ v := (Nat.dvd_mod_iff (hPq.trans hqQ)).mpr hxP
  have hqv : ¬ q ∣ v := fun hh => hxq ((Nat.dvd_mod_iff hqQ).mp hh)
  have hv0 : 0 < v := Nat.pos_of_ne_zero fun h0 => hqv (by rw [h0]; exact dvd_zero _)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = x.val / Q := ⟨_, rfl⟩
  have hxe : x = (v : ZMod n) + ((k : ℕ) : ℤ) * (Q : ZMod n) := by
    have h1 := Nat.mod_add_div x.val Q
    have h2 : (x : ZMod n) = ((x.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val x).symm
    have h3 : ((x.val : ℕ) : ZMod n) = ((v + Q * k : ℕ) : ZMod n) := by rw [hv, hk, h1]
    rw [h2, h3]; push_cast; ring
  have hDv : D (v : ZMod n) ≠ 0 := by
    have := period_zmul hperD ((k : ℕ) : ℤ) (v : ZMod n)
    rw [← hxe] at this
    rw [← this]; exact hx
  refine ⟨v, hv0, hvQ, hPv, hqv, ?_⟩
  unfold thetaProbe
  simp only [hD] at hDv
  push_cast
  exact hDv


/-- Downward selection of the intermediate probes `y_{L-1-k}, …, y_{L-1}`. -/
lemma selection_down [NeZero n] (h : NormalizedSetting n S S' d e)
    (hc : MaskChain n S d e L p) (hleast : ∀ i, i < L → IsLeastPeriod (maskFun n S (p i)) (p (i + 1)))
    {t : ℕ} (ht1 : p (L - 1) ∣ t) (ht2 : ¬ p L ∣ t) :
    ∀ k, k + 1 ≤ L → ∃ y : ℕ → ℕ, y (L - 1) = t ∧ ∀ i, L - 1 - k ≤ i → i ≤ L - 1 →
      (p i ∣ y i ∧ ¬ p (i + 1) ∣ y i) ∧
        (i + 2 ≤ L → 0 < y i ∧ y i < p (i + 2) ∧
          thetaProbe n S (p (i + 1)) (y i) (y (i + 1)) ≠ 0) := by
  have hL := hc.one_le
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => t, rfl, ?_⟩
    intro i h1 h2
    have hi : i = L - 1 := by omega
    subst hi
    have hL' : L - 1 + 1 = L := by omega
    refine ⟨⟨ht1, by rw [hL']; exact ht2⟩, fun h3 => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨y, hy, hprop⟩ := ih (by omega)
    set i0 := L - 1 - (k + 1) with hi0
    have hi0L : i0 + 2 ≤ L := by omega
    have hi0k : L - 1 - k = i0 + 1 := by omega
    obtain ⟨hl1, hl2⟩ := (hprop (i0 + 1) (by omega) (by omega)).1
    have hLeast1 := hleast (i0 + 1) (by omega)
    have hQn : p (i0 + 2) ∣ n := hLeast1.2.1
    obtain ⟨v, hv0, hvQ, hPv, hqv, hth⟩ := selection_step (P := p i0) (Q := p (i0 + 1 + 1))
      (q := p (i0 + 1)) (hc.dvd i0 (by omega)) (hc.dvd (i0 + 1) (by omega)) hQn
      (hc.periodic i0 (by omega)) hLeast1 hl1 hl2
    refine ⟨Function.update y i0 v, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]; exact hy
    · intro i hi1 hi2
      by_cases hii : i = i0
      · subst hii
        have hne : i0 + 1 ≠ i0 := Nat.succ_ne_self i0
        simp only [Function.update_self, Function.update_of_ne hne]
        refine ⟨⟨hPv, hqv⟩, fun _ => ⟨hv0, hvQ, hth⟩⟩
      · have hge : i0 + 1 ≤ i := by omega
        have h1 := hprop i (by omega) hi2
        simp only [Function.update_of_ne hii]
        refine ⟨h1.1, fun h3 => ?_⟩
        obtain ⟨a1, a2, a3⟩ := h1.2 h3
        refine ⟨a1, a2, ?_⟩
        rw [Function.update_of_ne (by omega : i + 1 ≠ i0)]
        exact a3

/-- `lem:selection`, `eq:probe-bounds`, `eq:sum-congruence`.  Suppose the periods of
`eq:chain` are least periods (`p_{i+1}` is the least period of `𝓑_{p_i}`), and fix
`t ∈ p_{L-1} ℤ \ P ℤ`, `P = p_L`.  The probes `y_0, …, y_{L-1}` (with `y_{L-1} = t`) and
`r, s, z` can be chosen so that `0 < y_i < p_{i+2}` and `θ_i ≠ 0` for `0 ≤ i ≤ L - 2`,
`0 < r, s, z < p_1` and `H_{y_0}(r, s, z) ≠ 0`, with the layer conditions `eq:layers`
(`y_i ∈ p_i ℤ \ p_{i+1} ℤ` for `0 ≤ i < L`, `e ∤ r, s, z`) and the sum congruence
`t + ∑_{i=0}^{L-2} y_i + r + s + z ≡ 0 (mod p_1)`. -/
theorem selection [NeZero n] (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p)
    (hleast : ∀ i, i < L → IsLeastPeriod (maskFun n S (p i)) (p (i + 1)))
    {t : ℕ} (ht1 : p (L - 1) ∣ t) (ht2 : ¬ p L ∣ t) :
    ∃ (y : ℕ → ℕ) (r s z : ℕ), y (L - 1) = t ∧
      (∀ i, i + 2 ≤ L → 0 < y i ∧ y i < p (i + 2) ∧
        thetaProbe n S (p (i + 1)) (y i) (y (i + 1)) ≠ 0) ∧
      (0 < r ∧ r < p 1 ∧ 0 < s ∧ s < p 1 ∧ 0 < z ∧ z < p 1) ∧
      probeH n S S' d e (y 0) (r : ZMod n) (s : ZMod n) (z : ZMod n) ≠ 0 ∧
      (∀ i, i < L → p i ∣ y i ∧ ¬ p (i + 1) ∣ y i) ∧ ¬ e ∣ r ∧ ¬ e ∣ s ∧ ¬ e ∣ z ∧
      ((p 1 : ℤ) ∣ (t : ℤ) + ∑ i ∈ range (L - 1), (y i : ℤ) + r + s + z) := by
  have hL := hc.one_le
  obtain ⟨y, hy, hprop⟩ := selection_down h hc hleast ht1 ht2 (L - 1) (by omega)
  have hprop' : ∀ i, i ≤ L - 1 → (p i ∣ y i ∧ ¬ p (i + 1) ∣ y i) ∧
      (i + 2 ≤ L → 0 < y i ∧ y i < p (i + 2) ∧
        thetaProbe n S (p (i + 1)) (y i) (y (i + 1)) ≠ 0) :=
    fun i hi => hprop i (by omega) hi
  have hy0 := (hprop' 0 (by omega)).1
  have hLeast0 := hleast 0 (by omega)
  rw [hc.p_zero] at hLeast0
  have hp0 : p 0 = e := hc.p_zero
  rw [hp0] at hy0
  obtain ⟨r, s, z, hr0, hr1, hs0, hs1, hz0, hz1, hre, hse, hze, hsum, hH⟩ :=
    bottom_probes h hLeast0 hy0.1 hy0.2
  refine ⟨y, r, s, z, hy, fun i hi => (hprop' i (by omega)).2 hi, ⟨hr0, hr1, hs0, hs1, hz0, hz1⟩,
    hH, fun i hi => ?_, hre, hse, hze, ?_⟩
  · exact (hprop' i (by omega)).1
  · -- divisibility of the sum
    have hdiv : ∀ i, 1 ≤ i → i ≤ L - 1 → (p 1 : ℤ) ∣ (y i : ℤ) := by
      intro i hi1 hi2
      have := (hprop' i hi2).1.1
      have h1i : p 1 ∣ p i := hc.dvd_le hi1 (by omega)
      exact_mod_cast h1i.trans this
    have hrest : (p 1 : ℤ) ∣ ∑ i ∈ range (L - 2), (y (i + 1) : ℤ) := by
      refine Finset.dvd_sum fun i hi => hdiv (i + 1) (by omega) (by simp at hi; omega)
    rcases Nat.lt_or_ge L 2 with hL2 | hL2
    · have hL1 : L = 1 := by omega
      subst hL1
      simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, add_zero, Nat.zero_add] at hy ⊢
      rw [← hy]
      have : ((y 0 : ℕ) : ℤ) + r + s + z = (r : ℤ) + s + z + y 0 := by ring
      rw [this]; exact hsum
    · have hsplit : ∑ i ∈ range (L - 1), (y i : ℤ) = ∑ i ∈ range (L - 2), (y (i + 1) : ℤ) + y 0 := by
        rw [show L - 1 = (L - 2) + 1 by omega, Finset.sum_range_succ']
      rw [hsplit]
      have ht' : (p 1 : ℤ) ∣ (t : ℤ) := by
        rw [← hy]; exact hdiv (L - 1) (by omega) le_rfl
      have : (t : ℤ) + (∑ i ∈ range (L - 2), (y (i + 1) : ℤ) + y 0) + r + s + z =
          ((t : ℤ) + ∑ i ∈ range (L - 2), (y (i + 1) : ℤ)) + ((r : ℤ) + s + z + y 0) := by ring
      rw [this]
      exact dvd_add (dvd_add ht' hrest) hsum

end Selection

end SkewRibbonCoarsenings
