/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Setting

/-!
# Fibers of the functional equation

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:detector`
(`lem:fiber`, `eq:fiber-period`).

The lemma is proved for functions with values in an arbitrary commutative domain `R` of
characteristic zero, which contains the rational-valued case of the paper (`R = ℚ`) and the
integer-valued case used by the later sections (`R = ℤ`).  The generic notions
`IsPeriodOf`, `IsLeastPeriodOf`, `FEqOf` agree definitionally with `IsPeriod`,
`IsLeastPeriod`, `FEq` of `SkewRibbonCoarsenings.Setting` when `R = ℤ`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

section Generic

variable {N : ℕ} {R : Type*}

/-- `p` is a period of `f : ℤ/N → R`. -/
def IsPeriodOf [Add R] (f : ZMod N → R) (p : ℕ) : Prop := ∀ x : ZMod N, f (x + (p : ZMod N)) = f x

/-- `e` is the least period of `f`: the least positive divisor of `N` that is a period. -/
def IsLeastPeriodOf [Add R] (f : ZMod N → R) (e : ℕ) : Prop :=
  0 < e ∧ e ∣ N ∧ IsPeriodOf f e ∧ ∀ p, 0 < p → p ∣ N → IsPeriodOf f p → e ≤ p

/-- The functional equation `eq:FE` for a pair of `R`-valued functions on `ℤ/N`. -/
def FEqOf [CommRing R] (u v : ZMod N → R) : Prop :=
  ∀ x y, u x * v y + v x * u y = u (x + y) * (v x + v y) + v (x + y) * (u x + u y)

lemma isPeriod_iff_isPeriodOf (f : ZMod N → ℤ) (p : ℕ) : IsPeriod f p ↔ IsPeriodOf f p := Iff.rfl

lemma isLeastPeriod_iff_isLeastPeriodOf (f : ZMod N → ℤ) (e : ℕ) :
    IsLeastPeriod f e ↔ IsLeastPeriodOf f e := Iff.rfl

lemma feq_iff_feqOf (u v : ZMod N → ℤ) : FEq u v ↔ FEqOf u v := Iff.rfl

/-- The group of periods of `f` (as elements of `ℤ/N`). -/
def periodGroup [AddCommGroup R] (f : ZMod N → R) : AddSubgroup (ZMod N) where
  carrier := {s | ∀ x, f (x + s) = f x}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro a b ha hb x
    rw [← add_assoc, hb, ha]
  neg_mem' := by
    intro a ha x
    have := ha (x + -a)
    simpa using this.symm

lemma mem_periodGroup [AddCommGroup R] {f : ZMod N → R} {s : ZMod N} :
    s ∈ periodGroup f ↔ ∀ x, f (x + s) = f x := Iff.rfl

/-- The least period divides every period. -/
lemma dvd_of_mem_periodGroup [NeZero N] [AddCommGroup R] {f : ZMod N → R} {e : ℕ}
    (he : IsLeastPeriodOf f e) {t : ZMod N} (ht : t ∈ periodGroup f) : e ∣ t.val := by
  obtain ⟨he0, heN, hper, hmin⟩ := he
  set g := Nat.gcd e t.val with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ he0
  have hgN : g ∣ N := (Nat.gcd_dvd_left e t.val).trans heN
  have hgmem : ((g : ℕ) : ZMod N) ∈ periodGroup f := by
    have h1 : ((g : ℤ) : ZMod N) = (Nat.gcdA e t.val) • ((e : ℕ) : ZMod N) +
        (Nat.gcdB e t.val) • t := by
      have := Nat.gcd_eq_gcd_ab e t.val
      have h2 := congrArg (fun z : ℤ => (z : ZMod N)) this
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h2
      rw [ZMod.natCast_zmod_val] at h2
      simp only [zsmul_eq_mul]
      rw [hg]; push_cast at h2 ⊢; linear_combination h2
    have : ((g : ℕ) : ZMod N) = (Nat.gcdA e t.val) • ((e : ℕ) : ZMod N) +
        (Nat.gcdB e t.val) • t := by
      rw [← h1]; simp
    rw [this]
    exact add_mem (zsmul_mem hper _) (zsmul_mem ht _)
  have hle := hmin g hg0 hgN hgmem
  have hge : g ≤ e := Nat.le_of_dvd he0 (Nat.gcd_dvd_left e t.val)
  have : g = e := le_antisymm hge hle
  rw [← this]
  exact Nat.gcd_dvd_right _ _

end Generic

section Fiber

variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R] [IsDomain R]

/-- The first half of `lem:fiber`, in the form: if `f(t+e) ≠ f(t)` then translation by `-t`
preserves `w`. -/
lemma fiber_translation_invariant {w f : ZMod N → R} {e : ℕ}
    (hw : ∀ x, w (-x) = -w x) (hper : IsPeriodOf w e) (hwf : ∀ x, w x * f x = 0)
    (hfe : FEqOf w f) {t : ZMod N} (ht : f (t + (e : ZMod N)) ≠ f t) :
    ∀ x, w (x - t) = w x := by
  classical
  have key : ∀ a, w a ≠ 0 → w (a - t) = w a := by
    intro a ha
    have hfa : f a = 0 := by
      rcases mul_eq_zero.mp (hwf a) with h | h
      · exact absurd h ha
      · exact h
    have hfa' : f (a + (e : ZMod N)) = 0 := by
      have h1 : w (a + (e : ZMod N)) ≠ 0 := by rw [hper a]; exact ha
      rcases mul_eq_zero.mp (hwf _) with h | h
      · exact absurd h h1
      · exact h
    have e1 := hfe a (t - a)
    have e2 := hfe (a + (e : ZMod N)) (t - a)
    have hsum : a + (t - a) = t := by ring
    have hsum2 : a + (e : ZMod N) + (t - a) = t + (e : ZMod N) := by ring
    rw [hsum] at e1
    rw [hsum2, hper a, hper t, hfa'] at e2
    rw [hfa] at e1
    have : (w a + w (t - a)) * (f (t + (e : ZMod N)) - f t) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · have : w (a - t) = w a := by
        have := hw (t - a)
        rw [show -(t - a) = a - t by ring] at this
        rw [this]; linear_combination -h
      exact this
    · exact absurd (sub_eq_zero.mp h) ht
  intro x
  by_cases hx : w x = 0
  · by_contra hne
    set S : Finset (ZMod N) := univ.filter fun x => w x ≠ 0 with hS
    have hsub : S.image (fun x => x - t) ⊆ S := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      have hy' : w y ≠ 0 := (Finset.mem_filter.mp hy).2
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [key y hy']; exact hy'
    have hcard : (S.image (fun x => x - t)).card = S.card :=
      Finset.card_image_of_injective _ (sub_left_injective)
    have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    have hmem : x - t ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h0; exact hne (by rw [h0, hx])
    rw [← heq] at hmem
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hmem
    have : y = x := sub_left_injective hyx
    subst this
    exact (Finset.mem_filter.mp hy).2 hx
  · exact key x hx

/-- `lem:fiber`, `eq:fiber-period`: for `w, f` on `ℤ/N` with `w` nonzero odd with least period `e`,
`w f = 0` and `eq:FE` for `(w, f)`, one has `f(t + e) = f(t)` for `e ∤ t`. -/
theorem fiber_period {w f : ZMod N → R} {e : ℕ} (_hw0 : ∃ x, w x ≠ 0)
    (hw : ∀ x, w (-x) = -w x) (he : IsLeastPeriodOf w e) (hwf : ∀ x, w x * f x = 0)
    (hfe : FEqOf w f) {t : ZMod N} (ht : ¬ e ∣ t.val) : f (t + (e : ZMod N)) = f t := by
  by_contra hne
  have htr := fiber_translation_invariant hw he.2.2.1 hwf hfe hne
  have hmem : -t ∈ periodGroup w := by
    intro x
    simpa [sub_eq_add_neg] using htr x
  have hmem' : t ∈ periodGroup w := by simpa using neg_mem hmem
  exact ht (dvd_of_mem_periodGroup he hmem')

/-- `lem:fiber`, second assertion: if also `f = 0` on `eℤ` and `f` sums to zero on every residue
class modulo `e`, then `f = 0`. -/
theorem fiber_eq_zero [CharZero R] {w f : ZMod N → R} {e : ℕ} (_hw0 : ∃ x, w x ≠ 0)
    (hw : ∀ x, w (-x) = -w x) (he : IsLeastPeriodOf w e) (hwf : ∀ x, w x * f x = 0)
    (hfe : FEqOf w f) (hf0 : ∀ x : ZMod N, e ∣ x.val → f x = 0)
    (hsum : ∀ c : ℕ, ∑ x ∈ univ.filter (fun x : ZMod N => x.val % e = c), f x = 0) :
    f = 0 := by
  have hper : ∀ {t : ZMod N}, ¬ e ∣ t.val → f (t + (e : ZMod N)) = f t :=
    fun {t} ht => fiber_period _hw0 hw he hwf hfe ht
  have heN : e ∣ N := he.2.1
  have he0 : 0 < e := he.1
  -- value on a translate by multiples of `e`
  have hmult : ∀ (x : ZMod N), ¬ e ∣ x.val → ∀ m : ℕ, f (x + ((e * m : ℕ) : ZMod N)) = f x := by
    intro x hx m
    induction m with
    | zero => simp
    | succ m ih =>
      have hnd : ¬ e ∣ (x + ((e * m : ℕ) : ZMod N)).val := by
        intro h
        apply hx
        have hv : (x + ((e * m : ℕ) : ZMod N)).val = (x.val + (e * m) % N) % N := by
          rw [ZMod.val_add, ZMod.val_natCast]
        have h1 : e ∣ (x.val + (e * m) % N) := by
          have := (Nat.dvd_mod_iff heN).mp (hv ▸ h)
          exact this
        have h2 : e ∣ (e * m) % N := (Nat.dvd_mod_iff heN).mpr (dvd_mul_right _ _)
        exact (Nat.dvd_add_left h2).mp h1
      have := hper hnd
      rw [show x + ((e * (m + 1) : ℕ) : ZMod N) = x + ((e * m : ℕ) : ZMod N) + (e : ZMod N) by
        push_cast; ring, this, ih]
  funext x
  by_cases hx : e ∣ x.val
  · exact hf0 x hx
  · -- the class sum
    set c := x.val % e with hc
    have hsx := hsum c
    have hconst : ∀ y ∈ univ.filter (fun x : ZMod N => x.val % e = c), f y = f x := by
      intro y hy
      have hy' : y.val % e = c := (Finset.mem_filter.mp hy).2
      have hdiv : e ∣ (y - x).val := by
        have hcast : ((y.val : ℕ) : ZMod e) = ((x.val : ℕ) : ZMod e) := by
          rw [ZMod.natCast_eq_natCast_iff']; rw [hy', hc]
        have hm : (((y - x).val : ℕ) : ZMod e) = (ZMod.castHom heN (ZMod e)) (y - x) := by
          conv_rhs => rw [← ZMod.natCast_zmod_val (y - x)]
          rw [map_natCast]
        have h3 : ((ZMod.castHom heN (ZMod e)) y) = ((y.val : ℕ) : ZMod e) := by
          conv_lhs => rw [← ZMod.natCast_zmod_val y]
          rw [map_natCast]
        have h4 : ((ZMod.castHom heN (ZMod e)) x) = ((x.val : ℕ) : ZMod e) := by
          conv_lhs => rw [← ZMod.natCast_zmod_val x]
          rw [map_natCast]
        have h2 : (((y - x).val : ℕ) : ZMod e) = 0 := by
          rw [hm, map_sub, h3, h4, hcast, sub_self]
        exact (ZMod.natCast_eq_zero_iff _ _).mp h2
      obtain ⟨m, hm⟩ := hdiv
      have : y = x + ((e * m : ℕ) : ZMod N) := by
        have := ZMod.natCast_zmod_val (y - x)
        rw [hm] at this
        rw [this]; ring
      rw [this]
      exact hmult x hx m
    have hmemx : x ∈ univ.filter (fun x : ZMod N => x.val % e = c) := by simp [hc]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const] at hsx
    have hcard : (univ.filter (fun x : ZMod N => x.val % e = c)).card ≠ 0 :=
      (Finset.card_pos.mpr ⟨x, hmemx⟩).ne'
    rcases smul_eq_zero.mp hsx with h | h
    · exact absurd h hcard
    · exact h

/-- `lem:fiber` with rational values, as stated in the paper. -/
theorem fiber_period_rat {w f : ZMod N → ℚ} {e : ℕ} (hw0 : ∃ x, w x ≠ 0)
    (hw : ∀ x, w (-x) = -w x) (he : IsLeastPeriodOf w e) (hwf : ∀ x, w x * f x = 0)
    (hfe : FEqOf w f) {t : ZMod N} (ht : ¬ e ∣ t.val) : f (t + (e : ZMod N)) = f t :=
  fiber_period hw0 hw he hwf hfe ht

end Fiber

/-! ### Integer-indexed form

For a function on the circle `ℤ/W`, presented as a `W`-periodic function on `ℤ`.  This is the form
used by the later lemmas, whose functions are defined through representatives. -/

section IntForm

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Integer multiples of a period are periods. -/
lemma periodic_int_mul {W : ℕ} {w : ℤ → R} (hwW : ∀ x, w (x + W) = w x) (m x : ℤ) :
    w (x + m * W) = w x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [show x + ((m : ℤ) + 1) * W = (x + m * W) + W by ring, hwW, ih]
  | pred m ih =>
    have := hwW (x + (-(m : ℤ) - 1) * W)
    rw [show x + (-(m : ℤ) - 1) * W + W = x + -(m : ℤ) * W by ring, ih] at this
    exact this.symm

/-- `lem:fiber`, `eq:fiber-period`, for `W`-periodic functions on `ℤ`: `w` odd, `e`-periodic, with
every translation period of `w` a multiple of `e`; `w f = 0`; `eq:FE` for `(w, f)`.  Then
`f (t + e) = f t` for `e ∤ t`. -/
theorem fiber_period_int {W e : ℕ} (hW : 0 < W) {w f : ℤ → R}
    (hwW : ∀ x, w (x + W) = w x) (hw : ∀ x, w (-x) = -w x)
    (hwe : ∀ x, w (x + e) = w x) (hper : ∀ t : ℤ, (∀ x, w (x + t) = w x) → (e : ℤ) ∣ t)
    (hwf : ∀ x, w x * f x = 0)
    (hfe : ∀ x y, w x * f y + f x * w y = w (x + y) * (f x + f y) + f (x + y) * (w x + w y))
    {t : ℤ} (ht : ¬ (e : ℤ) ∣ t) : f (t + e) = f t := by
  by_contra hne
  have key : ∀ a, w a ≠ 0 → w (a - t) = w a := by
    intro a ha
    have hfa : f a = 0 := by
      rcases mul_eq_zero.mp (hwf a) with h | h
      · exact absurd h ha
      · exact h
    have hfa' : f (a + e) = 0 := by
      have h1 : w (a + e) ≠ 0 := by rw [hwe a]; exact ha
      rcases mul_eq_zero.mp (hwf _) with h | h
      · exact absurd h h1
      · exact h
    have e1 := hfe a (t - a)
    have e2 := hfe (a + e) (t - a)
    have hsum : a + (t - a) = t := by ring
    have hsum2 : a + e + (t - a) = t + e := by ring
    rw [hsum] at e1
    rw [hsum2, hwe a, hwe t, hfa'] at e2
    rw [hfa] at e1
    have : (w a + w (t - a)) * (f (t + e) - f t) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · have h2 := hw (t - a)
      rw [show -(t - a) = a - t by ring] at h2
      rw [h2]; linear_combination -h
    · exact absurd (sub_eq_zero.mp h) hne
  have hall : ∀ x, w (x - t) = w x := by
    intro x
    by_cases hx : w x = 0
    · by_contra hne2
      have hx1 : w (x - t) ≠ 0 := fun h => hne2 (by rw [h, hx])
      have hk : ∀ k : ℕ, w (x - t - k * t) = w (x - t) ∧ w (x - t - k * t) ≠ 0 := by
        intro k
        induction k with
        | zero => exact ⟨by simp, by simpa using hx1⟩
        | succ k ih =>
          have := key _ ih.2
          refine ⟨?_, ?_⟩
          · rw [show x - t - ((k + 1 : ℕ) : ℤ) * t = x - t - k * t - t by push_cast; ring, this, ih.1]
          · rw [show x - t - ((k + 1 : ℕ) : ℤ) * t = x - t - k * t - t by push_cast; ring, this]
            exact ih.2
      have h1 := (hk (W - 1)).2
      have h2 := periodic_int_mul hwW (-t) x
      have h3 : x - t - ((W - 1 : ℕ) : ℤ) * t = x + (-t) * W := by
        have : ((W - 1 : ℕ) : ℤ) = (W : ℤ) - 1 := by omega
        rw [this]; ring
      rw [h3, h2] at h1
      exact h1 hx
    · exact key x hx
  have hmem : (e : ℤ) ∣ -t := hper (-t) (fun x => by rw [← sub_eq_add_neg]; exact hall x)
  exact ht ((dvd_neg).mp hmem)

/-- Translating by `k e` for `k : ℤ` preserves `f` off the `e`-grid, given `eq:fiber-period`. -/
lemma fiber_shift_int {e : ℕ} {f : ℤ → R} (hper : ∀ t : ℤ, ¬ (e : ℤ) ∣ t → f (t + e) = f t)
    {t : ℤ} (ht : ¬ (e : ℤ) ∣ t) (k : ℤ) : f (t + k * e) = f t := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hnd : ¬ (e : ℤ) ∣ t + k * e := fun h =>
      ht ((Int.dvd_add_left (dvd_mul_left (e : ℤ) k)).mp h)
    rw [show t + ((k : ℤ) + 1) * e = (t + k * e) + e by ring, hper _ hnd, ih]
  | pred k ih =>
    have hnd : ¬ (e : ℤ) ∣ t + (-(k : ℤ) - 1) * e := fun h =>
      ht ((Int.dvd_add_left (dvd_mul_left (e : ℤ) (-(k : ℤ) - 1))).mp h)
    have := hper _ hnd
    rw [show t + (-(k : ℤ) - 1) * e + e = t + -(k : ℤ) * e by ring, ih] at this
    exact this.symm

/-- `lem:fiber`, second assertion, for `W`-periodic functions on `ℤ` with `e ∣ W`: if also
`f = 0` on `eℤ` and `f` sums to zero on every residue class modulo `e` (a window of `W / e`
consecutive terms), then `f = 0`. -/
theorem fiber_eq_zero_int [CharZero R] {W e : ℕ} (he : 0 < e) (heW : e ∣ W) (hW : 0 < W)
    {f : ℤ → R} (hper : ∀ t : ℤ, ¬ (e : ℤ) ∣ t → f (t + e) = f t)
    (hf0 : ∀ x : ℤ, (e : ℤ) ∣ x → f x = 0)
    (hsum : ∀ r : ℕ, ∑ j ∈ range (W / e), f (r + j * e) = 0) : ∀ x, f x = 0 := by
  intro x
  by_cases hx : (e : ℤ) ∣ x
  · exact hf0 x hx
  · have hr : x % (e : ℤ) ≠ 0 := fun h => hx (Int.dvd_of_emod_eq_zero h)
    have hr0 : 0 ≤ x % (e : ℤ) := Int.emod_nonneg _ (by exact_mod_cast he.ne')
    set r : ℕ := (x % (e : ℤ)).toNat with hrdef
    have hrr : (r : ℤ) = x % (e : ℤ) := Int.toNat_of_nonneg hr0
    have hxr : x = r + (x / e) * e := by
      rw [hrr]; have := Int.emod_add_mul_ediv x e; linarith
    have hnr : ¬ (e : ℤ) ∣ (r : ℤ) := by
      rw [hrr]; intro h
      exact hx (by rw [hxr, hrr]; exact dvd_add h (dvd_mul_left _ _))
    have h1 : f x = f r := by
      rw [hxr]; exact fiber_shift_int hper hnr _
    have h2 : ∀ j : ℕ, f (r + j * e) = f r := fun j => by
      have := fiber_shift_int hper hnr (j : ℤ)
      simpa using this
    have hs := hsum r
    rw [Finset.sum_congr rfl (fun j _ => by
      have := h2 j
      push_cast at this ⊢
      exact this), Finset.sum_const, Finset.card_range] at hs
    have hM : (W / e) ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd hW heW) he; omega
    rw [h1]
    rcases smul_eq_zero.mp hs with h | h
    · exact absurd h hM
    · exact h

/-- An odd function vanishes at zero (characteristic zero). -/
lemma odd_zero_int [CharZero R] {w : ℤ → R} (hw : ∀ x, w (-x) = -w x) : w 0 = 0 := by
  have h := hw 0
  simp only [neg_zero] at h
  have h2 : (2 : R) * w 0 = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-- `eq:FE` for `(w, f)` holds everywhere once it holds off the `g`-grid: `w` shifts by `g`-multiples
are invisible, `f` vanishes on the `g`-grid, and `w f = 0`. -/
theorem fe_of_offgrid [CharZero R] {g : ℕ} {w f : ℤ → R} (hw : ∀ x, w (-x) = -w x)
    (hgw : ∀ x y : ℤ, (g : ℤ) ∣ x → w (x + y) = w y) (hf0 : ∀ x : ℤ, (g : ℤ) ∣ x → f x = 0)
    (hwf : ∀ x, w x * f x = 0)
    (hmain : ∀ x y : ℤ, ¬ (g : ℤ) ∣ x → ¬ (g : ℤ) ∣ y → ¬ (g : ℤ) ∣ (x + y) →
      w x * f y + f x * w y = w (x + y) * (f x + f y) + f (x + y) * (w x + w y)) :
    ∀ x y : ℤ, w x * f y + f x * w y = w (x + y) * (f x + f y) + f (x + y) * (w x + w y) := by
  intro x y
  by_cases hx : (g : ℤ) ∣ x
  · have h1 := hgw x y hx
    rw [hf0 x hx, h1]
    have := hwf y
    have h2 := hwf (x + y)
    rw [h1] at h2
    have hwx : w x = 0 := by
      have := hgw x 0 hx
      have h0 : w 0 = 0 := odd_zero_int hw
      simpa [h0] using this
    rw [hwx]
    linear_combination (-1 : R) * this - h2
  · by_cases hy : (g : ℤ) ∣ y
    · have h1 : w (x + y) = w x := by rw [add_comm]; exact hgw y x hy
      rw [hf0 y hy, h1]
      have := hwf x
      have h2 := hwf (x + y)
      rw [h1] at h2
      have hwy : w y = 0 := by
        have := hgw y 0 hy
        have h0 : w 0 = 0 := odd_zero_int hw
        simpa [h0] using this
      rw [hwy]
      linear_combination (-1 : R) * this - h2
    · by_cases hxy : (g : ℤ) ∣ (x + y)
      · have hfxy := hf0 _ hxy
        have hwxy : w (x + y) = 0 := by
          have := hgw (x + y) 0 hxy
          have h0 : w 0 = 0 := odd_zero_int hw
          simpa [h0] using this
        have hwy : w y = -w x := by
          have := hgw (x + y) (-x) hxy
          rw [show x + y + -x = y by ring, hw] at this
          exact this
        rw [hfxy, hwxy, hwy]
        by_cases hwx : w x = 0
        · rw [hwx]; ring
        · have hfx : f x = 0 := by
            rcases mul_eq_zero.mp (hwf x) with h | h
            · exact absurd h hwx
            · exact h
          have hfy : f y = 0 := by
            have h3 := hwf y
            rw [hwy] at h3
            rcases mul_eq_zero.mp h3 with h | h
            · exact absurd (neg_eq_zero.mp h) hwx
            · exact h
          rw [hfx, hfy]; ring
      · exact hmain x y hx hy hxy

end IntForm

/-- The sum of a periodic sequence over a window of one period is invariant under shifts. -/
lemma sum_range_shift_periodic {M : ℕ} (g : ℕ → ℤ) (hg : ∀ j, g (j + M) = g j) (k : ℕ) :
    ∑ j ∈ range M, g (j + k) = ∑ j ∈ range M, g j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := Finset.sum_range_succ' (fun j => g (j + k)) M
    have h2 := Finset.sum_range_succ (fun j => g (j + k)) M
    have h3 : g (M + k) = g k := by rw [add_comm]; exact hg k
    have h4 : ∑ j ∈ range M, g (j + (k + 1)) = ∑ j ∈ range M, g (j + 1 + k) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show j + (k + 1) = j + 1 + k by ring]
    rw [h4]
    simp only [zero_add] at h1
    linarith

/-! ### Elementary facts about the normalized setting

Everything used by `FourStart`, `BottomProbes`, `Selection` and `PeriodRatios`. -/

section Basics

variable {n : ℕ} {S S' : Finset ℕ} {d e : ℕ}

lemma cutInd_cases (n : ℕ) (S : Finset ℕ) (x : ZMod n) :
    cutInd n S x = 0 ∨ cutInd n S x = 1 := by
  unfold cutInd; split_ifs <;> simp

lemma dvd_val_iff [NeZero n] {d : ℕ} (hd : d ∣ n) (x : ZMod n) :
    d ∣ x.val ↔ ZMod.castHom hd (ZMod d) x = 0 := by
  have : ZMod.castHom hd (ZMod d) x = ((x.val : ℕ) : ZMod d) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  rw [this]; exact (ZMod.natCast_eq_zero_iff _ _).symm

lemma int_dvd_iff_val [NeZero n] {d : ℕ} (hd : d ∣ n) (t : ℤ) :
    (d : ℤ) ∣ t ↔ d ∣ (t : ZMod n).val := by
  rw [dvd_val_iff hd, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma nat_dvd_iff_val [NeZero n] {d : ℕ} (hd : d ∣ n) (m : ℕ) :
    d ∣ m ↔ d ∣ (m : ZMod n).val := by
  have := int_dvd_iff_val hd (m : ℤ)
  rw [Int.natCast_dvd_natCast] at this
  simpa using this

lemma dvd_val_neg [NeZero n] {d : ℕ} (hd : d ∣ n) (x : ZMod n) :
    d ∣ (-x).val ↔ d ∣ x.val := by
  rw [dvd_val_iff hd, dvd_val_iff hd, map_neg, neg_eq_zero]

lemma dvd_val_add [NeZero n] {d : ℕ} (hd : d ∣ n) {x y : ZMod n} (hy : d ∣ y.val) :
    d ∣ (x + y).val ↔ d ∣ x.val := by
  rw [dvd_val_iff hd, dvd_val_iff hd, map_add, (dvd_val_iff hd y).mp hy, add_zero]

lemma dvd_val_of_dvd_dvd {d e : ℕ} {x : ZMod n} (hed : e ∣ d)
    (h : d ∣ x.val) : e ∣ x.val := hed.trans h

/-- Periods in `ZMod n` are closed under integer multiples. -/
lemma period_zmul {f : ZMod n → ℤ} {p : ℕ} (hp : IsPeriod f p) (m : ℤ) (x : ZMod n) :
    f (x + (m : ZMod n) * (p : ZMod n)) = f x := by
  have hmem : (p : ZMod n) ∈ periodGroup f := fun x => hp x
  have := zsmul_mem hmem m
  have h2 := this x
  simpa [zsmul_eq_mul] using h2

/-- A function on `ℤ/n` is determined by its values at casts of integers. -/
lemma zmod_eq_intCast [NeZero n] (x : ZMod n) : ∃ k : ℤ, x = (k : ZMod n) :=
  ⟨x.val, by simp⟩

lemma wFun_of_dvd {S S' : Finset ℕ} {d : ℕ} {x : ZMod n} (hx : d ∣ x.val) : wFun n S S' d x = 0 := by
  unfold wFun; rw [if_pos hx]

lemma period_of_dvd_val [NeZero n] {f : ZMod n → ℤ} {p : ℕ} (hp : IsPeriod f p) {y : ZMod n}
    (hy : p ∣ y.val) (x : ZMod n) : f (x + y) = f x := by
  obtain ⟨k, hk⟩ := hy
  have : y = ((k : ℤ) : ZMod n) * (p : ZMod n) := by
    rw [← ZMod.natCast_zmod_val y, hk]; push_cast; ring
  rw [this]
  exact period_zmul hp (k : ℤ) x

lemma w_cases (d : ℕ) (x : ZMod n) : wFun n S S' d x = 0 ∨ wFun n S S' d x = 1 ∨
    wFun n S S' d x = -1 := by
  unfold wFun uFun
  have h1 := cutInd_cases n S x
  have h2 := cutInd_cases n S' (-x)
  split_ifs <;> omega

lemma maskFun_cases (p : ℕ) (x : ZMod n) : maskFun n S p x = 0 ∨ maskFun n S p x = 1 := by
  unfold maskFun
  have := cutInd_cases n S x
  split_ifs <;> omega

lemma maskFun_of_dvd {S : Finset ℕ} {p : ℕ} {x : ZMod n} (hx : p ∣ x.val) : maskFun n S p x = 0 := by
  unfold maskFun; rw [if_pos hx]

lemma maskFun_of_not_dvd {S : Finset ℕ} {p : ℕ} {x : ZMod n} (hx : ¬ p ∣ x.val) :
    maskFun n S p x = cutInd n S x := by
  unfold maskFun; rw [if_neg hx]

namespace NormalizedSetting

variable (h : NormalizedSetting n S S' d e)
include h

lemma d_dvd_n : d ∣ n := by
  rw [h.d_eq]; exact Nat.gcd_dvd_left _ _

lemma e_dvd_n : e ∣ n := h.e_dvd_d.trans h.d_dvd_n

lemma n_pos : 0 < n := by
  have := h.three_le_ratio
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [h0] at this; simp at this
  · exact h0

lemma e_pos : 0 < e := by have := h.three_le_e; omega

lemma d_pos : 0 < d := by
  have hdn := h.d_dvd_n
  have hn := h.n_pos
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · rw [h0] at hdn; simp at hdn; omega
  · exact h0

/-- The off-`d`-grid points where `v` vanishes: `v x ≠ 0` forces `d ∣ x`. -/
lemma dvd_of_v_ne [NeZero n] {x : ZMod n} (hx : vFun n S S' x ≠ 0) : d ∣ x.val := by
  rw [h.d_eq]
  refine (Nat.gcd_dvd_right n _).trans ?_
  have hmem : x.val ∈ (Finset.range n).filter
      (fun k : ℕ => vFun n S S' (k : ZMod n) ≠ 0) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt x, by rwa [ZMod.natCast_zmod_val]⟩
  exact Finset.gcd_dvd (f := id) hmem

lemma cutInd_eq_of_not_dvd [NeZero n] {x : ZMod n} (hx : ¬ d ∣ x.val) :
    cutInd n S x = cutInd n S' x := by
  by_contra hne
  exact hx (h.dvd_of_v_ne (by unfold vFun; omega))

lemma v_neg [NeZero n] (x : ZMod n) : vFun n S S' (-x) = - vFun n S S' x := by
  have := h.tau_eq x
  unfold vFun; omega

lemma wFun_eq_off [NeZero n] {x : ZMod n} (hx : ¬ d ∣ x.val) :
    wFun n S S' d x = cutInd n S x - cutInd n S (-x) := by
  have hn : ¬ d ∣ (-x).val := by rwa [dvd_val_neg h.d_dvd_n]
  have := h.cutInd_eq_of_not_dvd hn
  unfold wFun uFun
  rw [if_neg hx, ← this]

lemma w_zero [NeZero n] : wFun n S S' d 0 = 0 := by
  have := h.w_odd 0
  rw [neg_zero] at this
  omega

lemma w_add_e [NeZero n] {y : ZMod n} (hy : e ∣ y.val) (x : ZMod n) :
    wFun n S S' d (x + y) = wFun n S S' d x :=
  period_of_dvd_val h.e_least.2.2.1 hy x

lemma w_of_e_dvd [NeZero n] {x : ZMod n} (hx : e ∣ x.val) : wFun n S S' d x = 0 := by
  have := h.w_add_e hx 0
  rw [zero_add] at this
  rw [this, h.w_zero]

lemma w_add_d [NeZero n] {y : ZMod n} (hy : d ∣ y.val) (x : ZMod n) :
    wFun n S S' d (x + y) = wFun n S S' d x :=
  period_of_dvd_val h.w_period hy x

lemma not_e_dvd_of_not_d_dvd {x : ZMod n} (hx : ¬ e ∣ x.val) : ¬ d ∣ x.val :=
  fun hd => hx (h.e_dvd_d.trans hd)

lemma mask_odd_e (x : ZMod n) :
    maskFun n S e x - maskFun n S e (-x) = wFun n S S' d x :=
  h.mask_odd e dvd_rfl h.e_dvd_d x

end NormalizedSetting

end Basics

end SkewRibbonCoarsenings
