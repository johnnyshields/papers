/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/PeriodRatios.lean
import SkewRibbonCoarsenings.Selection
import SkewRibbonCoarsenings.LiteralFactor

/-!
# Restrictions on period growth

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:depth` (`lem:ratios`).

* `ratios_three`: for `e = 3`, both cut sets have a literal inner factor of weight three, the same
  one for both (a common inner factor, without a four-block test);
* `ratios_four`: for `e = 4`, the mask `𝓑_4` does not have least period eight;
* `ratios_doubling`, `ratios_doubling_chain`: a strict chain does not contain `p, 2p, 4p`
  consecutively.

Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset FourStart

section Ratios

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

lemma natCast_val_decomp (m e : ℕ) :
    ((m : ℕ) : ZMod n) = ((m % e : ℕ) : ZMod n) + (((m / e : ℕ) : ℤ) : ZMod n) * (e : ZMod n) := by
  have h1 := Nat.mod_add_div m e
  have h2 : ((m : ℕ) : ZMod n) = ((m % e + e * (m / e) : ℕ) : ZMod n) := by rw [h1]
  rw [h2, Int.cast_natCast]; push_cast; ring

/-- `w` depends only on the residue class of the representative modulo `e`. -/
lemma w_class [NeZero n] (h : NormalizedSetting n S S' d e) (x : ZMod n) :
    wFun n S S' d x = wFun n S S' d ((x.val % e : ℕ) : ZMod n) := by
  have hx : x = ((x.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val x).symm
  conv_lhs => rw [hx, natCast_val_decomp x.val e]
  exact period_zmul h.e_least.2.2.1 _ _

/-- `w(e - r) = -w(r)`. -/
lemma w_comp [NeZero n] (h : NormalizedSetting n S S' d e) {r : ℕ} (hr : r ≤ e) :
    wFun n S S' d ((e - r : ℕ) : ZMod n) = - wFun n S S' d (r : ZMod n) := by
  have h1 : ((e - r : ℕ) : ZMod n) = -(r : ZMod n) + ((1 : ℤ) : ZMod n) * (e : ZMod n) := by
    rw [Nat.cast_sub hr]; push_cast; ring
  rw [h1, period_zmul h.e_least.2.2.1 1 (-(r : ZMod n)), h.w_odd]

/-- `w` does not vanish on all of the residues `1, …, e - 1`. -/
lemma w_class_ne [NeZero n] (h : NormalizedSetting n S S' d e) :
    ∃ r : ℕ, 0 < r ∧ r < e ∧ wFun n S S' d (r : ZMod n) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h.w_ne
  funext x
  rw [w_class h x]
  have hr := Nat.mod_lt x.val h.e_pos
  rcases Nat.eq_zero_or_pos (x.val % e) with h0 | h0
  · rw [h0, Nat.cast_zero, h.w_zero]; rfl
  · exact hcon _ h0 hr

lemma cutInd_eq_one_iff {x : ℕ} (hx : x < n) :
    cutInd n S (x : ZMod n) = 1 ↔ x ∈ S := by
  rw [cutInd_natCast hx]; split_ifs with h1 <;> simp [h1]

/-- `lem:ratios` (1): if `e = 3` the two cut sets have a common literal inner factor of weight
three.  Precisely, both cut sets are `3`-periodic off the `3`-grid, they agree off the `3`-grid,
and the inner cuts of weight three coincide; equivalently both are `compCuts (n / 3) A 3 E` for the
same inner cut set `E`. -/
theorem ratios_three (h : NormalizedSetting n S S' d 3) :
    3 ∣ n ∧ OffGridPeriodic n S 3 ∧ OffGridPeriodic n S' 3 ∧
      (∀ x, ¬ 3 ∣ x → (x ∈ S ↔ x ∈ S')) ∧ innerCuts 3 S = innerCuts 3 S' ∧
      ∃ A A' E : Finset ℕ, IsCutSet (n / 3) A ∧ IsCutSet (n / 3) A' ∧ IsCutSet 3 E ∧
        S = compCuts (n / 3) A 3 E ∧ S' = compCuts (n / 3) A' 3 E := by
  have hn := h.n_pos
  have : NeZero n := ⟨hn.ne'⟩
  have h3n : 3 ∣ n := h.e_dvd_n
  have h3d : 3 ∣ d := h.e_dvd_d
  -- `w(1) ≠ 0`, `w(2) ≠ 0`
  have hw1 : wFun n S S' d ((1 : ℕ) : ZMod n) ≠ 0 := by
    obtain ⟨r, hr0, hr3, hr⟩ := w_class_ne h
    have hr' : r = 1 ∨ r = 2 := by omega
    rcases hr' with rfl | rfl
    · exact hr
    · have := w_comp h (r := 1) (by norm_num)
      intro h0
      apply hr
      have h2 : ((3 - 1 : ℕ) : ZMod n) = ((2 : ℕ) : ZMod n) := rfl
      rw [h2] at this
      rw [this, h0]; ring
  have hw2 : wFun n S S' d ((2 : ℕ) : ZMod n) ≠ 0 := by
    have := w_comp h (r := 1) (by norm_num)
    have h2 : ((3 - 1 : ℕ) : ZMod n) = ((2 : ℕ) : ZMod n) := rfl
    rw [h2] at this
    rw [this]; intro h0; exact hw1 (by omega)
  have hwne : ∀ x : ZMod n, ¬ 3 ∣ x.val → wFun n S S' d x ≠ 0 := by
    intro x hx
    rw [w_class h x]
    have : x.val % 3 = 1 ∨ x.val % 3 = 2 := by omega
    rcases this with h1 | h1 <;> rw [h1]
    · exact hw1
    · exact hw2
  have hcut : ∀ x : ℕ, x < n → ¬ 3 ∣ x → (x ∈ S ↔ x ∈ S') ∧ cutInd n S (x : ZMod n) =
      if wFun n S S' d (x : ZMod n) = 1 then 1 else 0 := by
    intro x hxn hx3
    have hxv : ¬ 3 ∣ ((x : ℕ) : ZMod n).val := by rwa [ZMod.val_natCast_of_lt hxn]
    have hxd : ¬ d ∣ ((x : ℕ) : ZMod n).val := fun hh => hxv (h3d.trans hh)
    have hb := cutInd_of_w (S := S) h (hwne _ hxv)
    refine ⟨?_, hb⟩
    have hc := h.cutInd_eq_of_not_dvd hxd
    rw [← cutInd_eq_one_iff hxn, ← cutInd_eq_one_iff (S := S') hxn, hc]
  have hper : ∀ T : Finset ℕ, (∀ x : ℕ, x < n → ¬ 3 ∣ x →
      cutInd n T (x : ZMod n) = if wFun n S S' d (x : ZMod n) = 1 then 1 else 0) →
      OffGridPeriodic n T 3 := by
    intro T hT x hx hx3
    have h1 := hT x (by omega) hx3
    have h2 := hT (x + 3) hx (fun hh => hx3 ((Nat.dvd_add_left (dvd_refl 3)).mp hh))
    have hw : wFun n S S' d (((x + 3 : ℕ)) : ZMod n) = wFun n S S' d (x : ZMod n) := by
      have := h.w_add_e (y := ((3 : ℕ) : ZMod n)) ((nat_dvd_iff_val h3n 3).mp dvd_rfl) (x : ZMod n)
      push_cast at this ⊢
      exact this
    rw [hw] at h2
    have hxn : x < n := by omega
    rw [← cutInd_eq_one_iff (S := T) hx, ← cutInd_eq_one_iff (S := T) hxn, h1, h2]

  have hS : OffGridPeriodic n S 3 := hper S fun x hxn hx3 => (hcut x hxn hx3).2
  have hS' : OffGridPeriodic n S' 3 := hper S' fun x hxn hx3 => by
    have hxv : ¬ 3 ∣ ((x : ℕ) : ZMod n).val := by rwa [ZMod.val_natCast_of_lt hxn]
    have hxd : ¬ d ∣ ((x : ℕ) : ZMod n).val := fun hh => hxv (h3d.trans hh)
    rw [← (h.cutInd_eq_of_not_dvd hxd)]
    exact (hcut x hxn hx3).2
  have hagree : ∀ x, ¬ 3 ∣ x → (x ∈ S ↔ x ∈ S') := by
    intro x hx3
    by_cases hxn : x < n
    · exact (hcut x hxn hx3).1
    · have h1 : x ∉ S := fun hh => hxn (Finset.mem_Ioo.mp (h.cuts hh)).2
      have h2 : x ∉ S' := fun hh => hxn (Finset.mem_Ioo.mp (h.cuts' hh)).2
      simp [h1, h2]
  have hinner := (literal_factor_same_inner (by norm_num) h.cuts h.cuts' hS hS').mpr hagree
  obtain ⟨A, E, hA, hE, hSe⟩ := (literal_factor_iff (by norm_num) h3n h.cuts).mpr hS
  obtain ⟨A', E', hA', hE', hSe'⟩ := (literal_factor_iff (by norm_num) h3n h.cuts').mpr hS'
  have hn3 : 0 < n / 3 := Nat.div_pos (Nat.le_of_dvd hn h3n) (by norm_num)
  have hEq := (literal_factor_unique (by norm_num) hn3 hA hE hSe).1
  have hEq' := (literal_factor_unique (by norm_num) hn3 hA' hE' hSe').1
  refine ⟨h3n, hS, hS', hagree, hinner, A, A', E, hA, hA', hE, hSe, ?_⟩
  have : E' = E := by rw [hEq, hEq', hinner]
  rw [← this]; exact hSe'


/-- `lem:ratios` (2): if `e = 4`, the mask `𝓑_4` does not have least period eight. -/
theorem ratios_four [NeZero n] (h : NormalizedSetting n S S' d 4) :
    ¬ IsLeastPeriod (maskFun n S 4) 8 := by
  intro hleast
  obtain ⟨_, h8n, h8per, hmin⟩ := hleast
  have h4n : 4 ∣ n := h.e_dvd_n
  have h4v : 4 ∣ ((4 : ℕ) : ZMod n).val := (nat_dvd_iff_val h4n 4).mp dvd_rfl
  -- `w(2) = 0`, `w(1) ≠ 0`, `w(3) = -w(1) ≠ 0`
  have hw2 : wFun n S S' d ((2 : ℕ) : ZMod n) = 0 := by
    have := w_comp h (r := 2) (by norm_num)
    have h2 : ((4 - 2 : ℕ) : ZMod n) = ((2 : ℕ) : ZMod n) := rfl
    rw [h2] at this; omega
  have hw1 : wFun n S S' d ((1 : ℕ) : ZMod n) ≠ 0 := by
    obtain ⟨r, hr0, hr4, hr⟩ := w_class_ne h
    have hr' : r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr' with rfl | rfl | rfl
    · exact hr
    · exact absurd hw2 hr
    · have := w_comp h (r := 1) (by norm_num)
      have h2 : ((4 - 1 : ℕ) : ZMod n) = ((3 : ℕ) : ZMod n) := rfl
      rw [h2] at this
      intro h0; apply hr; rw [this, h0]; ring
  have hw3 : wFun n S S' d ((3 : ℕ) : ZMod n) ≠ 0 := by
    have := w_comp h (r := 1) (by norm_num)
    have h2 : ((4 - 1 : ℕ) : ZMod n) = ((3 : ℕ) : ZMod n) := rfl
    rw [h2] at this
    rw [this]; intro h0; exact hw1 (by omega)
  have hper4 : IsPeriod (maskFun n S 4) 4 := by
    intro x
    by_cases hx : 4 ∣ x.val
    · rw [maskFun_of_dvd hx, maskFun_of_dvd ((dvd_val_add h4n h4v).mpr hx)]
    · have hx' : ¬ 4 ∣ (x + ((4 : ℕ) : ZMod n)).val := fun hh => hx ((dvd_val_add h4n h4v).mp hh)
      have hwx : wFun n S S' d (x + ((4 : ℕ) : ZMod n)) = wFun n S S' d x := h.w_add_e h4v x
      have hcls : x.val % 4 = 1 ∨ x.val % 4 = 2 ∨ x.val % 4 = 3 := by omega
      rcases hcls with hc | hc | hc
      · have hwne : wFun n S S' d x ≠ 0 := by rw [w_class h x, hc]; exact hw1
        have hwne' : wFun n S S' d (x + ((4 : ℕ) : ZMod n)) ≠ 0 := by rw [hwx]; exact hwne
        rw [maskFun_of_not_dvd hx', maskFun_of_not_dvd hx, cutInd_of_w h hwne,
          cutInd_of_w h hwne', hwx]
      · have hwne : wFun n S S' d x = 0 := by rw [w_class h x, hc]; exact hw2
        obtain ⟨k, hk⟩ : ∃ k, x.val = 4 * k + 2 := ⟨x.val / 4, by omega⟩
        have hxe : x = ((4 * k + 2 : ℕ) : ZMod n) := by
          rw [← hk, ZMod.natCast_zmod_val]
        have e1 : -x = (x + ((4 : ℕ) : ZMod n)) + ((-(k + 1 : ℤ) : ℤ) : ZMod n) * ((8 : ℕ) : ZMod n) := by
          rw [hxe]; push_cast; ring
        have hmo := h.mask_odd_e (e := 4) x
        have h8 := period_zmul h8per (-(k + 1 : ℤ)) (x + ((4 : ℕ) : ZMod n))
        rw [← e1] at h8
        have hmo' : maskFun n S 4 x - maskFun n S 4 (-x) = 0 := by
          have := h.mask_odd 4 dvd_rfl h.e_dvd_d x
          rw [this]; exact hwne
        omega
      · have hwne : wFun n S S' d x ≠ 0 := by rw [w_class h x, hc]; exact hw3
        have hwne' : wFun n S S' d (x + ((4 : ℕ) : ZMod n)) ≠ 0 := by rw [hwx]; exact hwne
        rw [maskFun_of_not_dvd hx', maskFun_of_not_dvd hx, cutInd_of_w h hwne,
          cutInd_of_w h hwne', hwx]
  have := hmin 4 (by norm_num) h4n hper4
  omega


/-- `lem:ratios` (3), the local statement: if `e ∣ p`, `4 p ∣ d`, `𝓑_p` has period `2 p` and
`𝓑_{2p}` has least period `4 p`, we reach a contradiction.  Hence a strict chain `eq:chain`
cannot contain `p, 2p, 4p` as consecutive terms (`ratios_doubling_chain`). -/
theorem ratios_doubling [NeZero n] (h : NormalizedSetting n S S' d e) {p : ℕ} (hep : e ∣ p)
    (h4d : 4 * p ∣ d) (hp0 : 0 < p) (hper : IsPeriod (maskFun n S p) (2 * p))
    (hleast : IsLeastPeriod (maskFun n S (2 * p)) (4 * p)) : False := by
  obtain ⟨_, h4n, h4per, hmin⟩ := hleast
  have h2pn : 2 * p ∣ n := (Dvd.intro_left 2 (by ring) : 2 * p ∣ 4 * p).trans h4n
  have hpn : p ∣ n := (Dvd.intro_left 2 rfl : p ∣ 2 * p).trans h2pn
  have h2pd : 2 * p ∣ d := (Dvd.intro_left 2 (by ring) : 2 * p ∣ 4 * p).trans h4d
  have hep2 : e ∣ 2 * p := hep.mul_left 2
  have h2per : IsPeriod (maskFun n S (2 * p)) (2 * p) := by
    intro x
    have h2pv : p ∣ (((2 * p : ℕ)) : ZMod n).val := (nat_dvd_iff_val hpn (2 * p)).mp
      (Dvd.intro_left 2 rfl)
    have h2pv' : 2 * p ∣ (((2 * p : ℕ)) : ZMod n).val := (nat_dvd_iff_val h2pn (2 * p)).mp dvd_rfl
    by_cases hx : p ∣ x.val
    · by_cases hx2 : 2 * p ∣ x.val
      · rw [maskFun_of_dvd hx2, maskFun_of_dvd ((dvd_val_add h2pn h2pv').mpr hx2)]
      · obtain ⟨m, hm⟩ := hx
        have hm_odd : ¬ 2 ∣ m := fun ⟨k, hk⟩ => hx2 ⟨k, by rw [hm, hk]; ring⟩
        obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
        have hxe : x = ((p * (2 * k + 1) : ℕ) : ZMod n) := by
          rw [← hk, ← hm]; exact (ZMod.natCast_zmod_val x).symm
        have hew : wFun n S S' d x = 0 := by
          apply h.w_of_e_dvd
          exact hep.trans ⟨m, hm⟩
        have e1 : x + ((2 * p : ℕ) : ZMod n) =
            -x + (((k + 1 : ℕ) : ℤ) : ZMod n) * ((4 * p : ℕ) : ZMod n) := by
          rw [hxe]; push_cast; ring
        have h8 := period_zmul h4per ((k + 1 : ℕ) : ℤ) (-x)
        rw [← e1] at h8
        have hmo := h.mask_odd (2 * p) hep2 h2pd x
        rw [hew] at hmo
        omega
    · have hx2 : ¬ 2 * p ∣ x.val := fun hh => hx ((Dvd.intro_left 2 rfl : p ∣ 2 * p).trans hh)
      have h2pv : p ∣ (((2 * p : ℕ)) : ZMod n).val := (nat_dvd_iff_val hpn (2 * p)).mp
        (Dvd.intro_left 2 rfl)
      have hy : ¬ p ∣ (x + ((2 * p : ℕ) : ZMod n)).val := fun hh => hx ((dvd_val_add hpn h2pv).mp hh)
      have hy2 : ¬ 2 * p ∣ (x + ((2 * p : ℕ) : ZMod n)).val := fun hh =>
        hy ((Dvd.intro_left 2 rfl : p ∣ 2 * p).trans hh)
      rw [maskFun_of_not_dvd hy2, maskFun_of_not_dvd hx2]
      have := hper x
      rw [maskFun_of_not_dvd hy, maskFun_of_not_dvd hx] at this
      push_cast at this ⊢
      exact this
  have := hmin (2 * p) (by omega) h2pn h2per
  omega


/-- `lem:ratios` (3): in a chain `eq:chain` whose step `i + 1` is a least-period step
(`p_{i+2}` is the least period of `𝓑_{p_{i+1}}`), the consecutive terms `p_i, p_{i+1}, p_{i+2}`
are never `p, 2p, 4p`. -/
theorem ratios_doubling_chain [NeZero n] (h : NormalizedSetting n S S' d e) {L : ℕ}
    {p : ℕ → ℕ} (hc : MaskChain n S d e L p) {i : ℕ} (hi : i + 2 ≤ L)
    (hleast : IsLeastPeriod (maskFun n S (p (i + 1))) (p (i + 2))) :
    ¬ (p (i + 1) = 2 * p i ∧ p (i + 2) = 4 * p i) := by
  rintro ⟨h1, h2⟩
  have hpi : 0 < p i := by
    have := hc.lt i (by omega)
    have hp0 : 0 < p 0 := by rw [hc.p_zero]; exact h.e_pos
    rcases Nat.eq_zero_or_pos (p i) with h0 | h0
    · rw [h0] at h1; have := hc.lt i (by omega); omega
    · exact h0
  have hep : e ∣ p i := by
    rw [← hc.p_zero]; exact hc.dvd_le (Nat.zero_le i) (by omega)
  have h4d : 4 * p i ∣ d := by
    rw [← h2]; exact (hc.dvd_le (by omega : i + 2 ≤ L) le_rfl).trans hc.dvd_d
  refine ratios_doubling h hep h4d hpi ?_ ?_
  · have := hc.periodic i (by omega)
    rw [h1] at this; exact this
  · rw [h1, h2] at hleast; exact hleast

end Ratios

end SkewRibbonCoarsenings
