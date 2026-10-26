/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/BottomProbes.lean
import SkewRibbonCoarsenings.FourStart

/-!
# Bottom probes

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:detector`
(`lem:bottom`, `eq:bottom-probes`, `eq:shifted-reflection`).

`probeF` is `f_y(x) = 𝓑_e(x + y) - 𝓑_e(x)` and `probeH` is `H_y(r, s, z)` of `eq:deltaH`
(defined here independently of the nested-identity module; the two must be identified at
assembly).  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset FourStart

/-- `f_y(x) = 𝓑_e(x + y) - 𝓑_e(x)` of `eq:deltaH`, for a natural number `y`. -/
def probeF (n : ℕ) (S : Finset ℕ) (e y : ℕ) (x : ZMod n) : ℤ :=
  maskFun n S e (x + (y : ZMod n)) - maskFun n S e x

/-- `H_y(r, s, z) = f_y(r)(w(s) + w(z)) + f_y(s)(w(r) + w(z)) + f_y(z)(w(r) + w(s))` of
`eq:deltaH`. -/
def probeH (n : ℕ) (S S' : Finset ℕ) (d e y : ℕ) (r s z : ZMod n) : ℤ :=
  probeF n S e y r * (wFun n S S' d s + wFun n S S' d z) +
    probeF n S e y s * (wFun n S S' d r + wFun n S S' d z) +
    probeF n S e y z * (wFun n S S' d r + wFun n S S' d s)

section Bottom

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

lemma mask_neg_eq [NeZero n] (h : NormalizedSetting n S S' d e) (x : ZMod n) :
    maskFun n S e (-x) = maskFun n S e x - wFun n S S' d x := by
  have := h.mask_odd_e x
  omega

/-- `lem:bottom`, `eq:shifted-reflection`: `f_y(-y - x) = -f_y(x)` for `e ∣ y`. -/
theorem probeF_reflect [NeZero n] (h : NormalizedSetting n S S' d e) {y : ℕ} (hy : e ∣ y)
    (x : ZMod n) : probeF n S e y (-(y : ZMod n) - x) = - probeF n S e y x := by
  have hyv : e ∣ ((y : ℕ) : ZMod n).val := (nat_dvd_iff_val h.e_dvd_n y).mp hy
  unfold probeF
  have e1 : -(y : ZMod n) - x + (y : ZMod n) = -x := by ring
  have e2 : maskFun n S e (-(y : ZMod n) - x) = maskFun n S e (-(x + (y : ZMod n))) := by
    congr 1; ring
  rw [e1, e2, mask_neg_eq h, mask_neg_eq h, h.w_add_e hyv x]
  ring


/-! ### The circle `ℤ/p` as `p`-periodic functions on `ℤ` -/

section Circle

variable [NeZero n]

/-- `f_y` on `ℤ`, through the cast to `ℤ/n`. -/
def probeInt (n : ℕ) (S : Finset ℕ) (e y : ℕ) (x : ℤ) : ℤ := probeF n S e y (x : ZMod n)

/-- `𝓑_e` on `ℤ`, through the cast to `ℤ/n`. -/
def maskInt (n : ℕ) (S : Finset ℕ) (e : ℕ) (x : ℤ) : ℤ := maskFun n S e (x : ZMod n)

lemma maskInt_add_p {p : ℕ} (hp : IsPeriod (maskFun n S e) p) (x : ℤ) :
    maskInt n S e (x + p) = maskInt n S e x := by
  unfold maskInt; push_cast; exact hp _

lemma wInt_add_p (h : NormalizedSetting n S S' d e) {p : ℕ}
    (hp : IsPeriod (maskFun n S e) p) (x : ℤ) :
    wInt n S S' d (x + p) = wInt n S S' d x := by
  unfold wInt
  rw [← h.mask_odd_e, ← h.mask_odd_e]
  have h1 : maskFun n S e (((x + p : ℤ)) : ZMod n) = maskFun n S e (x : ZMod n) := by
    have := maskInt_add_p hp x; exact this
  have h2 : maskFun n S e (-((x + p : ℤ) : ZMod n)) = maskFun n S e (-(x : ZMod n)) := by
    have := maskInt_add_p hp (-x)
    unfold maskInt at this
    push_cast at this ⊢
    rw [show -((x : ZMod n) + (p : ZMod n)) = -(x : ZMod n) + (p : ZMod n) - 2 * (p : ZMod n) by
      ring]
    have h3 := period_zmul hp (-2) (-(x : ZMod n) + (p : ZMod n))
    push_cast at h3
    rw [show -(x : ZMod n) + (p : ZMod n) - 2 * (p : ZMod n) =
      -(x : ZMod n) + (p : ZMod n) + -2 * (p : ZMod n) by ring, h3]
    exact this
  rw [h1, h2]

lemma e_dvd_of_period (h : NormalizedSetting n S S' d e) {p : ℕ}
    (hp : IsPeriod (maskFun n S e) p) : e ∣ p := by
  have := wInt_period_dvd h (p : ℤ) (fun x => wInt_add_p h hp x)
  exact_mod_cast this

lemma probeInt_add_p {p : ℕ} (hp : IsPeriod (maskFun n S e) p) (y : ℕ) (x : ℤ) :
    probeInt n S e y (x + p) = probeInt n S e y x := by
  unfold probeInt probeF
  have h1 : maskFun n S e (((x + p : ℤ)) : ZMod n) = maskFun n S e (x : ZMod n) :=
    maskInt_add_p hp x
  have h2 : maskFun n S e ((((x + p : ℤ)) : ZMod n) + (y : ZMod n)) =
      maskFun n S e ((x : ZMod n) + (y : ZMod n)) := by
    have := maskInt_add_p hp (x + y)
    unfold maskInt at this
    push_cast at this ⊢
    rw [show (x : ZMod n) + (p : ZMod n) + (y : ZMod n) =
      (x : ZMod n) + (y : ZMod n) + (p : ZMod n) by ring]
    exact this
  rw [h1, h2]

lemma per_Rm {W : ℕ} (hW : 0 < W) {f : ℤ → ℤ} (hf : ∀ x, f (x + W) = f x) (x : ℤ) :
    f (Rm W x : ℤ) = f x := by
  have := periodic_int_mul hf (-(x / (W : ℤ))) x
  rw [Rm_eq hW x]
  rw [← this]; congr 1; ring

lemma wInt_shift_e (h : NormalizedSetting n S S' d e) {x : ℤ} (hx : (e : ℤ) ∣ x) (y : ℤ) :
    wInt n S S' d (x + y) = wInt n S S' d y := by
  obtain ⟨k, rfl⟩ := hx
  have := periodic_int_mul (fun z => wInt_add_e h z) k y
  rw [add_comm, mul_comm]; exact this

lemma probeInt_reflect (h : NormalizedSetting n S S' d e) {y : ℕ} (hy : e ∣ y) (x : ℤ) :
    probeInt n S e y (-(y : ℤ) - x) = - probeInt n S e y x := by
  unfold probeInt
  have := probeF_reflect h hy (x : ZMod n)
  push_cast; exact this

lemma maskInt_of_dvd (h : NormalizedSetting n S S' d e) {x : ℤ} (hx : (e : ℤ) ∣ x) :
    maskInt n S e x = 0 := by
  unfold maskInt
  exact maskFun_of_dvd ((int_dvd_iff_val h.e_dvd_n x).mp hx)

lemma probeInt_of_dvd (h : NormalizedSetting n S S' d e) {y : ℕ} (hy : e ∣ y) {x : ℤ}
    (hx : (e : ℤ) ∣ x) : probeInt n S e y x = 0 := by
  have h1 : maskInt n S e (x + y) = 0 :=
    maskInt_of_dvd h (dvd_add hx (by exact_mod_cast hy))
  have h2 := maskInt_of_dvd h hx
  unfold probeInt probeF
  unfold maskInt at h1 h2
  push_cast at h1 ⊢
  rw [h1, h2]; ring

/-- `w(x) ≠ 0` forces the binary cut value: `b(x) = 1` if `w(x) = 1` and `b(x) = 0` if
`w(x) = -1`. -/
lemma cutInd_of_w (h : NormalizedSetting n S S' d e) {x : ZMod n} (hx : wFun n S S' d x ≠ 0) :
    cutInd n S x = if wFun n S S' d x = 1 then 1 else 0 := by
  have hd : ¬ d ∣ x.val := fun hh => hx (wFun_of_dvd hh)
  have := h.wFun_eq_off hd
  have c1 := cutInd_cases n S x
  have c2 := cutInd_cases n S (-x)
  split_ifs with h1 <;> omega

lemma wInt_mul_probeInt (h : NormalizedSetting n S S' d e) {y : ℕ} (hy : e ∣ y) (x : ℤ) :
    wInt n S S' d x * probeInt n S e y x = 0 := by
  by_cases hw : wInt n S S' d x = 0
  · rw [hw, zero_mul]
  · have hwx : wFun n S S' d (x : ZMod n) ≠ 0 := hw
    have hxe : ¬ e ∣ (x : ZMod n).val := fun hh => hw (h.w_of_e_dvd hh)
    have hyv : e ∣ ((y : ℕ) : ZMod n).val := (nat_dvd_iff_val h.e_dvd_n y).mp hy
    have hxy : ¬ e ∣ ((x : ZMod n) + (y : ZMod n)).val := fun hh =>
      hxe ((dvd_val_add h.e_dvd_n hyv).mp hh)
    have hwxy : wFun n S S' d ((x : ZMod n) + (y : ZMod n)) = wFun n S S' d (x : ZMod n) :=
      h.w_add_e hyv _
    have hwxy' : wFun n S S' d ((x : ZMod n) + (y : ZMod n)) ≠ 0 := by rw [hwxy]; exact hwx
    have b1 := cutInd_of_w h hwx
    have b2 := cutInd_of_w h hwxy'
    rw [hwxy] at b2
    have : probeInt n S e y x = 0 := by
      unfold probeInt probeF
      rw [maskFun_of_not_dvd hxy, maskFun_of_not_dvd hxe, b1, b2]; ring
    rw [this, mul_zero]


/-- `H_y` on integer arguments. -/
def HInt (n : ℕ) (S S' : Finset ℕ) (d e y : ℕ) (r s z : ℤ) : ℤ :=
  probeInt n S e y r * (wInt n S S' d s + wInt n S S' d z) +
    probeInt n S e y s * (wInt n S S' d r + wInt n S S' d z) +
    probeInt n S e y z * (wInt n S S' d r + wInt n S S' d s)

lemma probeH_natCast (y X Y Z : ℕ) :
    probeH n S S' d e y (X : ZMod n) (Y : ZMod n) (Z : ZMod n) =
      HInt n S S' d e y (X : ℤ) (Y : ℤ) (Z : ℤ) := by
  simp [probeH, HInt, probeInt, wInt]

/-- The sum of `f_y` over a residue class modulo `e` inside one period `p` vanishes. -/
lemma probeInt_class_sum (h : NormalizedSetting n S S' d e) {p y : ℕ}
    (hpper : IsPeriod (maskFun n S e) p) (hey : e ∣ y) (r : ℕ) :
    ∑ j ∈ range (p / e), probeInt n S e y ((r : ℤ) + j * e) = 0 := by
  have hep : e ∣ p := e_dvd_of_period h hpper
  obtain ⟨k, hk⟩ := hey
  obtain ⟨M, hM⟩ := hep
  have he0 := h.e_pos
  have hpe : p / e = M := by rw [hM]; exact Nat.mul_div_cancel_left M he0
  rw [hpe]
  set g : ℕ → ℤ := fun j => maskInt n S e ((r : ℤ) + j * e) with hg
  have hgper : ∀ j, g (j + M) = g j := by
    intro j
    simp only [hg]
    have := maskInt_add_p hpper ((r : ℤ) + j * e)
    rw [← this]; congr 1; rw [hM]; push_cast; ring
  have key : ∀ j : ℕ, probeInt n S e y ((r : ℤ) + j * e) = g (j + k) - g j := by
    intro j
    simp only [hg]
    unfold probeInt probeF maskInt
    have : (((r : ℤ) + ((j + k : ℕ) : ℤ) * e : ℤ) : ZMod n) =
        (((r : ℤ) + j * e : ℤ) : ZMod n) + (y : ZMod n) := by
      rw [hk]; push_cast; ring
    rw [this]
  simp only [key]
  rw [Finset.sum_sub_distrib, sum_range_shift_periodic g hgper k]
  ring


/-- `lem:bottom`, `eq:bottom-probes`.  If `𝓑_e` has least period `p > e`, `e ∣ y` and `p ∤ y`,
there are `0 < r, s, z < p`, all off the `e`-grid, with `r + s + z ≡ -y (mod p)` and
`H_y(r, s, z) ≠ 0`. -/
theorem bottom_probes (h : NormalizedSetting n S S' d e) {p y : ℕ}
    (hp : IsLeastPeriod (maskFun n S e) p) (hey : e ∣ y) (hpy : ¬ p ∣ y) :
    ∃ r s z : ℕ, 0 < r ∧ r < p ∧ 0 < s ∧ s < p ∧ 0 < z ∧ z < p ∧ ¬ e ∣ r ∧ ¬ e ∣ s ∧
      ¬ e ∣ z ∧ (p : ℤ) ∣ (r : ℤ) + s + z + y ∧
      probeH n S S' d e y (r : ZMod n) (s : ZMod n) (z : ZMod n) ≠ 0 := by
  obtain ⟨hp0, hpn, hpper, hpmin⟩ := hp
  have hep' : e ∣ p := e_dvd_of_period h hpper
  have he0 := h.e_pos
  by_contra hcon
  push Not at hcon
  have hfne : ∃ x : ℤ, probeInt n S e y x ≠ 0 := by
    by_contra hall
    push Not at hall
    have hmem : ((y : ℕ) : ZMod n) ∈ periodGroup (maskFun n S e) := by
      intro x
      have := hall (x.val : ℤ)
      unfold probeInt probeF at this
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at this
      omega
    have := dvd_of_mem_periodGroup ⟨hp0, hpn, hpper, hpmin⟩ hmem
    exact hpy ((nat_dvd_iff_val hpn y).mpr this)
  obtain ⟨x0, hx0⟩ := hfne
  have hwp := wInt_add_p h hpper
  have hfp := probeInt_add_p hpper y
  have hye : (e : ℤ) ∣ (y : ℤ) := by exact_mod_cast hey
  have hmain : ∀ x y' : ℤ, ¬ (e : ℤ) ∣ x → ¬ (e : ℤ) ∣ y' → ¬ (e : ℤ) ∣ (x + y') →
      wInt n S S' d x * probeInt n S e y y' + probeInt n S e y x * wInt n S S' d y' =
        wInt n S S' d (x + y') * (probeInt n S e y x + probeInt n S e y y') +
          probeInt n S e y (x + y') * (wInt n S S' d x + wInt n S S' d y') := by
    intro x y' hx hy' hxy
    set z : ℤ := -(y : ℤ) - (x + y') with hz
    have hzne : ¬ (e : ℤ) ∣ z := fun hh => hxy (by
      have : (e : ℤ) ∣ -(y : ℤ) - z := dvd_sub (dvd_neg.mpr hye) hh
      have h2 : -(y : ℤ) - z = x + y' := by rw [hz]; ring
      rwa [h2] at this)
    have hW : 0 < p := hp0
    have hXe : ¬ e ∣ Rm p x := fun hh => hx ((Rm_dvd_iff hW hep' x).mpr hh)
    have hYe : ¬ e ∣ Rm p y' := fun hh => hy' ((Rm_dvd_iff hW hep' y').mpr hh)
    have hZe : ¬ e ∣ Rm p z := fun hh => hzne ((Rm_dvd_iff hW hep' z).mpr hh)
    have hX0 : 0 < Rm p x := Nat.pos_of_ne_zero fun h0 => hXe (by rw [h0]; exact dvd_zero _)
    have hY0 : 0 < Rm p y' := Nat.pos_of_ne_zero fun h0 => hYe (by rw [h0]; exact dvd_zero _)
    have hZ0 : 0 < Rm p z := Nat.pos_of_ne_zero fun h0 => hZe (by rw [h0]; exact dvd_zero _)
    have hsum : (p : ℤ) ∣ (Rm p x : ℤ) + Rm p y' + Rm p z + y := by
      rw [Rm_eq hW x, Rm_eq hW y', Rm_eq hW z]
      have : ((x - p * (x / p)) + (y' - p * (y' / p)) + (z - p * (z / p)) + y : ℤ) =
          (x + y' + z + y) - p * (x / p + y' / p + z / p) := by ring
      rw [this]
      have h0 : x + y' + z + y = 0 := by rw [hz]; ring
      rw [h0]
      exact ⟨-(x / p + y' / p + z / p), by ring⟩
    have hH := hcon (Rm p x) (Rm p y') (Rm p z) hX0 (Rm_lt hW x) hY0 (Rm_lt hW y') hZ0
      (Rm_lt hW z) hXe hYe hZe hsum
    rw [probeH_natCast] at hH
    unfold HInt at hH
    rw [per_Rm hW hwp, per_Rm hW hwp, per_Rm hW hwp, per_Rm hW hfp, per_Rm hW hfp,
      per_Rm hW hfp] at hH
    have hfz : probeInt n S e y z = - probeInt n S e y (x + y') := by
      have := probeInt_reflect h hey (x + y'); rw [hz]; exact this
    have hwz : wInt n S S' d z = - wInt n S S' d (x + y') := by
      have e1 : z = -(x + y') + (-(y : ℤ)) := by rw [hz]; ring
      rw [e1, add_comm, wInt_shift_e h (dvd_neg.mpr hye), wInt_neg h]
    rw [hfz, hwz] at hH
    linarith
  have hfe : ∀ x y' : ℤ, wInt n S S' d x * probeInt n S e y y' + probeInt n S e y x *
      wInt n S S' d y' = wInt n S S' d (x + y') * (probeInt n S e y x + probeInt n S e y y') +
        probeInt n S e y (x + y') * (wInt n S S' d x + wInt n S S' d y') :=
    fe_of_offgrid (g := e) (wInt_neg h) (fun x y hx => wInt_shift_e h hx y)
      (fun x hx => probeInt_of_dvd h hey hx) (wInt_mul_probeInt h hey) hmain
  have hper : ∀ t : ℤ, ¬ (e : ℤ) ∣ t → probeInt n S e y (t + e) = probeInt n S e y t :=
    fun t ht => fiber_period_int (W := p) (e := e) hp0 hwp (wInt_neg h) (wInt_add_e h)
      (fun t ht => wInt_period_dvd h t ht) (wInt_mul_probeInt h hey) hfe ht
  have hzero := fiber_eq_zero_int he0 hep' hp0 hper (fun x hx => probeInt_of_dvd h hey hx)
    (fun r => probeInt_class_sum h hpper hey r) x0
  exact hx0 hzero

end Circle

end Bottom

end SkewRibbonCoarsenings
