/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Packing

/-!
# Realization at the original weight: propagation

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:realization`
(`prop:propagation`).

For a chain of least periods (`eq:chain`), if all applicable positive detectors vanish
(`DetectorsVanish`) then `𝓑_P`, `P = p_L`, is `d`-periodic.  The proof follows the three cases of
the paper: `P < d`; `P = d` with `d ∈ supp v`; `P = d` with `d ∉ supp v`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset Nested

section Propagation

variable {n : ℕ} {S S' : Finset ℕ} {d e L : ℕ} {p : ℕ → ℕ}

lemma MaskChain.pred_dvd (hc : MaskChain n S d e L p) : p (L - 1) ∣ p L := by
  have := hc.dvd (L - 1) (by have := hc.one_le; omega)
  rwa [Nat.sub_add_cancel hc.one_le] at this

lemma MaskChain.periodic_pred (hc : MaskChain n S d e L p) :
    IsPeriod (maskFun n S (p (L - 1))) (p L) := by
  have := hc.periodic (L - 1) (by have := hc.one_le; omega)
  rwa [Nat.sub_add_cancel hc.one_le] at this

/-- Off the `p_{L-1}`-grid, shifting by a multiple of `P = p_L` preserves `𝓑_P`: there
`𝓑_P = 𝓑_{p_{L-1}}`, which has period `P`. -/
lemma mask_shift_offgrid [NeZero n] (h : NormalizedSetting n S S' d e)
    (hc : MaskChain n S d e L p) {y x : ZMod n} (hy : p L ∣ y.val) (hx : ¬ p (L - 1) ∣ x.val) :
    maskFun n S (p L) (x + y) = maskFun n S (p L) x := by
  have hPn : p L ∣ n := hc.dvd_n h le_rfl
  have hq := hc.pred_dvd
  have hqn : p (L - 1) ∣ n := hq.trans hPn
  have hxP : ¬ p L ∣ x.val := fun hh => hx (hq.trans hh)
  have hyq : p (L - 1) ∣ y.val := hq.trans hy
  have hxy : ¬ p L ∣ (x + y).val := fun hh => hxP ((dvd_val_add hPn hy).mp hh)
  have hxyq : ¬ p (L - 1) ∣ (x + y).val := fun hh => hx ((dvd_val_add hqn hyq).mp hh)
  rw [maskFun_of_not_dvd hxy, maskFun_of_not_dvd hxP]
  have := period_of_dvd_val hc.periodic_pred hy x
  rw [maskFun_of_not_dvd hxyq, maskFun_of_not_dvd hx] at this
  exact this

/-- The nonwrapped equality of `prop:propagation`: for `a` representing an element of `supp v`
and `t ∈ p_{L-1} ℤ \ P ℤ` with `t < n - a` and `n - a ≥ 2P`, if all applicable positive detectors
vanish then `b(a + t) = b(t)` (otherwise `lem:selection` and `lem:packing` give a nonzero
detector). -/
lemma nonwrapped [NeZero n] (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p)
    (hleast : ∀ i, i < L → IsLeastPeriod (maskFun n S (p i)) (p (i + 1)))
    (hv : DetectorsVanish n S S' d e L p) {a t : ℕ} (ha0 : 0 < a) (han : a < n)
    (hva : vFun n S S' (a : ZMod n) ≠ 0) (htW : t < n - a) (ht1 : p (L - 1) ∣ t)
    (ht2 : ¬ p L ∣ t) (hW : 2 * p L ≤ n - a) :
    cutInd n S ((a + t : ℕ) : ZMod n) = cutInd n S (t : ZMod n) := by
  by_contra hne
  obtain ⟨y, r, s, z, -, hD⟩ := packing h hc hleast ha0 han hva htW ht1 ht2 hne
    (packingBudget_of_two_mul h hc hW)
  exact (not_detectorsVanish_iff.mpr ⟨a, r, s, z, y, hD⟩) hv

lemma vFun_natCast_sub [NeZero n] (h : NormalizedSetting n S S' d e) {a : ℕ} (han : a ≤ n)
    (hva : vFun n S S' (a : ZMod n) ≠ 0) : vFun n S S' ((n - a : ℕ) : ZMod n) ≠ 0 := by
  rw [natCast_sub_eq_neg' han, h.v_neg]; simpa using hva

/-- Shifting by a support element `a` with `a ≥ 2P` and `n - a ≥ 2P` preserves `𝓑_P` (the
nonwrapped equality for `a`, and the complementary application for `n - a`). -/
lemma shift_support [NeZero n] (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p)
    (hleast : ∀ i, i < L → IsLeastPeriod (maskFun n S (p i)) (p (i + 1)))
    (hv : DetectorsVanish n S S' d e L p) {a : ℕ} (ha0 : 0 < a) (han : a < n)
    (hva : vFun n S S' (a : ZMod n) ≠ 0) (h2a : 2 * p L ≤ a) (h2W : 2 * p L ≤ n - a)
    (x : ZMod n) : maskFun n S (p L) (x + (a : ZMod n)) = maskFun n S (p L) x := by
  have hL := hc.one_le
  have hPn : p L ∣ n := hc.dvd_n h le_rfl
  have hPa : p L ∣ a := hc.dvd_d.trans (dvd_of_vFun_ne h hva)
  have hPaV : p L ∣ (a : ZMod n).val := (nat_dvd_iff_val hPn a).mp hPa
  have hq := hc.pred_dvd
  by_cases hxq : p (L - 1) ∣ x.val
  swap
  · exact mask_shift_offgrid h hc hPaV hxq
  by_cases hxP : p L ∣ x.val
  · rw [maskFun_of_dvd hxP, maskFun_of_dvd ((dvd_val_add hPn hPaV).mpr hxP)]
  have hxy : ¬ p L ∣ (x + (a : ZMod n)).val := fun hh => hxP ((dvd_val_add hPn hPaV).mp hh)
  rw [maskFun_of_not_dvd hxy, maskFun_of_not_dvd hxP]
  have hPW : p L ∣ n - a := Nat.dvd_sub hPn hPa
  obtain ⟨t, ht⟩ : ∃ t, t = x.val := ⟨_, rfl⟩
  have hx : x = (t : ZMod n) := by rw [ht, ZMod.natCast_zmod_val]
  have htn : t < n := by rw [ht]; exact ZMod.val_lt x
  rw [← ht] at hxq hxP
  rw [hx]
  rcases lt_trichotomy t (n - a) with hlt | heq | hgt
  · have := nonwrapped h hc hleast hv ha0 han hva hlt hxq hxP h2W
    have e1 : (t : ZMod n) + (a : ZMod n) = ((a + t : ℕ) : ZMod n) := by push_cast; ring
    rw [e1, this]
  · exact absurd (heq ▸ hPW) hxP
  · have hva' := vFun_natCast_sub h han.le hva
    have hd1 : p (L - 1) ∣ t - (n - a) := Nat.dvd_sub hxq (hq.trans hPW)
    have hd2 : ¬ p L ∣ t - (n - a) := by
      intro hh
      apply hxP
      have := Nat.dvd_add hh hPW
      rwa [show t - (n - a) + (n - a) = t by omega] at this
    have := nonwrapped h hc hleast hv (a := n - a) (t := t - (n - a)) (by omega) (by omega)
      hva' (by omega) hd1 hd2 (by omega)
    rw [show n - a + (t - (n - a)) = t by omega] at this
    have e1 : (t : ZMod n) + (a : ZMod n) = ((t - (n - a) : ℕ) : ZMod n) := by
      have h0 : t + a = n + (t - (n - a)) := by omega
      have := congrArg (fun m : ℕ => (m : ZMod n)) h0
      simp only [Nat.cast_add, ZMod.natCast_self, zero_add] at this
      exact this
    rw [e1, this]

/-- A function whose period group contains every support element of `v` is `d`-periodic. -/
lemma period_of_support [NeZero n] (h : NormalizedSetting n S S' d e) {f : ZMod n → ℤ}
    (hall : ∀ a : ℕ, 0 < a → a < n → vFun n S S' (a : ZMod n) ≠ 0 →
      ∀ x, f (x + (a : ZMod n)) = f x) : IsPeriod f d := by
  have hsupp : ∀ k ∈ (Finset.range n).filter (fun k : ℕ => vFun n S S' (k : ZMod n) ≠ 0),
      ((k : ℕ) : ZMod n) ∈ periodGroup f := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, hvk⟩ := hk
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        exfalso
        have h00 : vFun n S S' 0 = 0 := by
          have := h.v_neg 0
          rw [neg_zero] at this
          omega
        rw [Nat.cast_zero] at hvk
        exact hvk h00
      · exact h0
    exact fun x => hall k hk0 hkn hvk x
  have hG := finset_gcd_mem_periodGroup _ hsupp
  have hn0 : (((n : ℕ)) : ZMod n) ∈ periodGroup f := by
    rw [ZMod.natCast_self]; exact zero_mem _
  have hd := gcd_mem_periodGroup hn0 hG
  have hdeq : d = Nat.gcd n (((Finset.range n).filter
      (fun k : ℕ => vFun n S S' (k : ZMod n) ≠ 0)).gcd id) := h.d_eq
  rw [← hdeq] at hd
  exact hd

lemma two_le_of_dvd_ne {q m : ℕ} (hq : ∃ k, m = q * k) (hm : 0 < m) (hne : m ≠ q) :
    2 * q ≤ m := by
  obtain ⟨k, hk⟩ := hq
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk; omega
    · exact h0
  have hk2 : 2 ≤ k := by
    by_contra hk2
    have : k = 1 := by omega
    rw [this] at hk
    exact hne (by omega)
  rw [hk]
  nlinarith

/-- `prop:propagation`.  Suppose the chain `eq:chain` consists of least periods
(`p_{i+1}` is the least period of `𝓑_{p_i}`).  If all applicable positive detectors of `thm:nested`
vanish (`DetectorsVanish`), then `𝓑_P`, `P = p_L`, is `d`-periodic. -/
theorem propagation (h : NormalizedSetting n S S' d e) (hc : MaskChain n S d e L p)
    (hleast : ∀ i, i < L → IsLeastPeriod (maskFun n S (p i)) (p (i + 1)))
    (hv : DetectorsVanish n S S' d e L p) : IsPeriod (maskFun n S (p L)) d := by
  haveI : NeZero n := neZero_of_setting h
  have hL := hc.one_le
  have hPn : p L ∣ n := hc.dvd_n h le_rfl
  have hPd : p L ∣ d := hc.dvd_d
  have hP0 : 0 < p L := hc.pos h le_rfl
  have hdn : d ∣ n := h.d_dvd_n
  have hd0 : 0 < d := h.d_pos
  have hdlt : d < n := h.d_lt
  have hPle : p L ≤ d := Nat.le_of_dvd hd0 hPd
  by_cases hPlt : p L < d
  · -- case `P < d`
    have h2P : 2 * p L ≤ d := by
      obtain ⟨k, hk⟩ := hPd
      have : 2 ≤ k := by
        by_contra hk2
        have hk1 : k ≤ 1 := by omega
        have : p L * k ≤ p L * 1 := Nat.mul_le_mul_left _ hk1
        omega
      rw [hk]; nlinarith
    refine period_of_support h fun a ha0 han hva x => ?_
    have hda : d ∣ a := dvd_of_vFun_ne h hva
    have hdW : d ∣ n - a := Nat.dvd_sub hdn hda
    have h1 : d ≤ a := Nat.le_of_dvd ha0 hda
    have h2 : d ≤ n - a := Nat.le_of_dvd (by omega) hdW
    exact shift_support h hc hleast hv ha0 han hva (by omega) (by omega) x
  · have hPeq : p L = d := le_antisymm hPle (not_lt.mp hPlt)
    by_cases hvd : vFun n S S' (d : ZMod n) ≠ 0
    · -- case `P = d`, `d ∈ supp v`
      have h3d : 3 * d ≤ n := (Nat.le_div_iff_mul_le hd0).mp h.three_le_ratio
      have hq := hc.pred_dvd
      have hqd : p (L - 1) ∣ d := hPeq ▸ hq
      have hdV : p L ∣ (d : ZMod n).val := (nat_dvd_iff_val hPn d).mp hPd
      -- the nonwrapped equalities along a residue class
      have claim : ∀ j r : ℕ, p (L - 1) ∣ r → ¬ p L ∣ r → j * d + r < n →
          cutInd n S ((j * d + r : ℕ) : ZMod n) = cutInd n S (r : ZMod n) := by
        intro j r hr1 hr2
        induction j with
        | zero => intro _; simp
        | succ j ih =>
          intro hj
          have hjn : j * d + r < n := by
            have : (j + 1) * d = j * d + d := by ring
            omega
          have e1 : (j + 1) * d + r = d + (j * d + r) := by ring
          have hnw := nonwrapped h hc hleast hv (a := d) (t := j * d + r) hd0 hdlt hvd
            (by have : (j + 1) * d = j * d + d := by ring
                omega)
            (Dvd.dvd.add (hqd.mul_left j) hr1 |> fun hh => hh) (by
              rw [hPeq]; intro hh
              apply hr2; rw [hPeq]
              exact (Nat.dvd_add_right (dvd_mul_left d j)).mp hh) (by omega)
          rw [e1, hnw]
          exact ih hjn
      intro x
      by_cases hxq : p (L - 1) ∣ x.val
      swap
      · exact mask_shift_offgrid h hc (y := (d : ZMod n)) hdV hxq
      by_cases hxP : p L ∣ x.val
      · rw [maskFun_of_dvd hxP, maskFun_of_dvd ((dvd_val_add hPn hdV).mpr hxP)]
      have hxy : ¬ p L ∣ (x + (d : ZMod n)).val := fun hh => hxP ((dvd_val_add hPn hdV).mp hh)
      rw [maskFun_of_not_dvd hxy, maskFun_of_not_dvd hxP]
      obtain ⟨t, ht⟩ : ∃ t, t = x.val := ⟨_, rfl⟩
      have hx : x = (t : ZMod n) := by rw [ht, ZMod.natCast_zmod_val]
      have htn : t < n := by rw [ht]; exact ZMod.val_lt x
      rw [← ht] at hxq hxP
      rw [hx]
      have hdec : t = (t / d) * d + t % d := by
        have := Nat.div_add_mod t d
        rw [mul_comm] at this; omega
      have hrd : t % d < d := Nat.mod_lt _ hd0
      have hr1 : p (L - 1) ∣ t % d := (Nat.dvd_mod_iff hqd).mpr hxq
      have hr2 : ¬ p L ∣ t % d := fun hh => hxP ((Nat.dvd_mod_iff (hPeq ▸ dvd_rfl)).mp hh)
      have hc0 := claim (t / d) (t % d) hr1 hr2 (by rw [← hdec]; exact htn)
      rw [← hdec] at hc0
      by_cases hwrap : t + d < n
      · have hc1 := claim (t / d + 1) (t % d) hr1 hr2 (by
          have : (t / d + 1) * d = t / d * d + d := by ring
          omega)
        have e1 : (t / d + 1) * d + t % d = d + t := by
          have : (t / d + 1) * d = t / d * d + d := by ring
          omega
        rw [e1] at hc1
        have e2 : (t : ZMod n) + (d : ZMod n) = ((d + t : ℕ) : ZMod n) := by push_cast; ring
        rw [e2, hc1, hc0]
      · obtain ⟨m, hm⟩ := hdn
        have hjm : t / d + 1 = m := by
          have hjlt : t / d < m := by
            by_contra hge
            push Not at hge
            have : m * d ≤ t / d * d := Nat.mul_le_mul_right d hge
            rw [hm] at htn
            have : d * m = m * d := mul_comm _ _
            omega
          by_contra hne
          have h2 : t / d + 2 ≤ m := by omega
          have : (t / d + 2) * d ≤ m * d := Nat.mul_le_mul_right d h2
          have e3 : (t / d + 2) * d = t / d * d + 2 * d := by ring
          have e4 : d * m = m * d := mul_comm _ _
          omega
        have h4 : t + d = n + t % d := by
          have : (t / d + 1) * d = t / d * d + d := by ring
          rw [hjm] at this
          have e4 : d * m = m * d := mul_comm _ _
          omega
        have e2 : (t : ZMod n) + (d : ZMod n) = ((t % d : ℕ) : ZMod n) := by
          have := congrArg (fun m : ℕ => (m : ZMod n)) h4
          simp only [Nat.cast_add, ZMod.natCast_self, zero_add] at this
          exact this
        rw [e2, hc0]
    · -- case `P = d`, `d ∉ supp v`
      push Not at hvd
      have hvnd : vFun n S S' ((n - d : ℕ) : ZMod n) = 0 := by
        rw [natCast_sub_eq_neg' hdlt.le, h.v_neg, hvd]; simp
      refine period_of_support h fun a ha0 han hva x => ?_
      have hda : d ∣ a := dvd_of_vFun_ne h hva
      have hdW : d ∣ n - a := Nat.dvd_sub hdn hda
      have had : a ≠ d := fun hh => hva (hh ▸ hvd)
      have hanW : a ≠ n - d := fun hh => hva (hh ▸ hvnd)
      have h1 : 2 * d ≤ a := two_le_of_dvd_ne hda ha0 had
      have h2 : 2 * d ≤ n - a :=
        two_le_of_dvd_ne hdW (by omega) (by omega)
      exact shift_support h hc hleast hv ha0 han hva (by omega) (by omega) x

end Propagation

end SkewRibbonCoarsenings
