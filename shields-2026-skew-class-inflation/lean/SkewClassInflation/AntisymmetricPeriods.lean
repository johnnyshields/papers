/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.OverlapPeriods

/-!
# Antisymmetric interval periods with deleted multiples

The finite-period algebra used by the ribbon factorization input to
`lem:overlap-power-rigidity` of `shields-2026-skew-class-inflation.tex`.
A deleted-multiple flag describes exactly which values are available.
The residue cycle is completed from its actual punctured invariance;
no periodic extension is carried as a hypothesis.  Sorry-free.
-/

namespace SkewClassInflation

/-- Either all coordinates are defined, or precisely the positive period multiples are deleted. -/
def periodPointDefined (holes : Bool) (c x : ℕ) : Prop := holes = false ∨ ¬ c ∣ x

private theorem periodPointDefined_sub (holes : Bool) (c n : ℕ) (hcn : c ≤ n)
    (hn : periodPointDefined holes c n) : periodPointDefined holes c (n - c) := by
  rcases hn with hn | hn
  · exact Or.inl hn
  · apply Or.inr
    intro hm
    have hd := Nat.dvd_add hm (dvd_refl c)
    rw [Nat.sub_add_cancel hcn] at hd
    exact hn hd

private theorem bounded_period_reduce {A : Type*} (f : ℕ → A) (holes : Bool)
    (c d : ℕ) (hc : 0 < c)
    (hstep : ∀ x, 0 < x → x + c < d → periodPointDefined holes c x →
      periodPointDefined holes c (x + c) → f (x + c) = f x) :
    ∀ n, 0 < n → n < d → periodPointDefined holes c n →
      f n = if n % c = 0 then f c else f (n % c) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn0 hnd hdef
    by_cases hnc : n ≤ c
    · by_cases hlt : n < c
      · rw [Nat.mod_eq_of_lt hlt, ite_eq_right (Nat.ne_of_gt hn0)]
      · have he : n = c := by omega
        subst n
        simp only [Nat.mod_self, ite_true]
    · have hcn : c ≤ n := by omega
      have hm0 : 0 < n - c := by omega
      have hmn : n - c < n := Nat.sub_lt hn0 hc
      have hmd : n - c < d := by omega
      have hmdef := periodPointDefined_sub holes c n hcn hdef
      have hs := hstep (n - c) hm0 (by omega) hmdef
        (by simpa only [Nat.sub_add_cancel hcn] using hdef)
      rw [Nat.sub_add_cancel hcn] at hs
      have hi := ih (n - c) hmn hm0 hmd hmdef
      have hmod : (n - c) % c = n % c := by
        have he : n = c + (n - c) := by omega
        conv_rhs => rw [he]
        simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      rw [hmod] at hi
      exact hs.trans hi

/-- Antisymmetric interval data produce an actual cyclic function with the other period. -/
theorem antisymmetric_residue_cycle (f : ℕ → ℤ) (holes : Bool)
    (c d : ℕ) (hc : 0 < c) (hcd : c < d)
    (hantiC : ∀ x, 0 < x → x < c → f x = -f (c - x))
    (hantiD : ∀ x, 0 < x → x < d → periodPointDefined holes c x →
      periodPointDefined holes c (d - x) → f x = -f (d - x))
    (hstep : ∀ x, 0 < x → x + c < d → periodPointDefined holes c x →
      periodPointDefined holes c (x + c) → f (x + c) = f x) :
    ∃ G : ZMod c → ℤ, G 0 = 0 ∧ (∀ x, G (-x) = -G x) ∧
      (∀ x, G (x + (d : ZMod c)) = G x) ∧
      ∀ n, 0 < n → n < d → ¬ c ∣ n → G (n : ZMod c) = f n := by
  classical
  let _ : NeZero c := ⟨Nat.ne_of_gt hc⟩
  let G : ZMod c → ℤ := fun x => if x = 0 then 0 else f x.val
  have hG0 : G 0 = 0 := by simp only [G, ite_true]
  have hneg : ∀ x : ZMod c, G (-x) = -G x := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp only [neg_zero, hG0]
    · have hxn : -x ≠ 0 := neg_ne_zero.mpr hx
      have hxv : 0 < x.val := Nat.pos_of_ne_zero (fun he => hx ((ZMod.val_eq_zero x).mp he))
      have ha := hantiC x.val hxv x.val_lt
      simp only [G, ite_eq_right hxn, ZMod.neg_val, ite_eq_right hx]
      omega
  have hnat : ∀ n, 0 < n → n < d → ¬ c ∣ n → G (n : ZMod c) = f n := by
    intro n hn0 hnd hnot
    have hz : (n : ZMod c) ≠ 0 := by
      intro he
      exact hnot ((ZMod.natCast_eq_zero_iff n c).mp he)
    have hm : n % c ≠ 0 := fun he => hnot (Nat.dvd_of_mod_eq_zero he)
    have hr := bounded_period_reduce f holes c d hc hstep n hn0 hnd (Or.inr hnot)
    rw [ite_eq_right hm] at hr
    simpa only [G, ite_eq_right hz, ZMod.val_natCast] using hr.symm
  let σ : Equiv.Perm (ZMod c) := Equiv.addRight (-(d : ZMod c))
  have hσ : ∀ x : ZMod c, x ≠ 0 → σ x ≠ 0 → G (σ x) = G x := by
    intro x hx hs
    have hxv : 0 < x.val := Nat.pos_of_ne_zero (fun he => hx ((ZMod.val_eq_zero x).mp he))
    have hxc : x.val < c := x.val_lt
    have hxd : x.val < d := hxc.trans hcd
    have hn : ¬ c ∣ x.val := by
      intro he
      have hh := Nat.le_of_dvd hxv he
      omega
    let m := d - x.val
    have hm0 : 0 < m := by dsimp only [m]; omega
    have hmd : m < d := by dsimp only [m]; omega
    have hcast : (m : ZMod c) = (d : ZMod c) - x := by
      dsimp only [m]
      rw [Nat.cast_sub hxd.le, ZMod.natCast_zmod_val]
    have hnot : ¬ c ∣ m := by
      intro he
      have hz := (ZMod.natCast_eq_zero_iff m c).mpr he
      rw [hcast] at hz
      have hdx : (d : ZMod c) = x := sub_eq_zero.mp hz
      apply hs
      simp only [σ, Equiv.coe_addRight, hdx, add_neg_cancel]
    have hmneg : (m : ZMod c) = -(σ x) := by
      rw [hcast]
      simp only [σ, Equiv.coe_addRight, neg_add_rev, neg_neg, sub_eq_add_neg]
    have hxG : G x = f x.val := by simp only [G, ite_eq_right hx]
    have hmG := hnat m hm0 hmd hnot
    have ha := hantiD x.val hxv hxd (Or.inr hn) (Or.inr hnot)
    change f x.val = -f m at ha
    rw [← hxG, ← hmG, hmneg, hneg] at ha
    omega
  have hd0 : G (d : ZMod c) = 0 := by
    have he := punctured_cycle_endpoints σ 0 G hσ
    have hn := hneg (d : ZMod c)
    simp only [σ, Equiv.addRight_symm, Equiv.coe_addRight, zero_add, neg_neg] at he
    omega
  have hall : ∀ x : ZMod c, G (σ x) = G x := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp only [σ, Equiv.coe_addRight, zero_add, hneg, hd0, neg_zero, hG0]
    · by_cases hs : σ x = 0
      · have he : x = (d : ZMod c) := by
          apply sub_eq_zero.mp
          simpa only [σ, Equiv.coe_addRight, sub_eq_add_neg] using hs
        rw [hs, he, hG0, hd0]
      · exact hσ x hx hs
  refine ⟨G, hG0, hneg, ?_, hnat⟩
  intro x
  have hh := hall (x + (d : ZMod c))
  simpa only [σ, Equiv.coe_addRight, add_neg_cancel_right] using hh.symm

variable (f : ℕ → ℤ) (holes : Bool) (c d : ℕ) (hc : 0 < c) (hcd : c < d)
  (hantiC : ∀ x, 0 < x → x < c → f x = -f (c - x))
  (hantiD : ∀ x, 0 < x → x < d → periodPointDefined holes c x →
    periodPointDefined holes c (d - x) → f x = -f (d - x))
  (hstep : ∀ x, 0 < x → x + c < d → periodPointDefined holes c x →
    periodPointDefined holes c (x + c) → f (x + c) = f x)

include hc hcd hantiC hantiD hstep

/-- The stated partial interval data have an actual antisymmetric two-period extension. -/
theorem antisymmetric_interval_extension :
    ∃ F : ℤ → ℤ, Function.Periodic F (c : ℤ) ∧ Function.Periodic F (d : ℤ) ∧
      F 0 = 0 ∧ (∀ x, F (-x) = -F x) ∧
      ∀ n, 0 < n → n < d → periodPointDefined holes c n → F (n : ℤ) = f n := by
  classical
  let _ : NeZero c := ⟨Nat.ne_of_gt hc⟩
  obtain ⟨G, hG0, hneg, hperiod, hnat⟩ :=
    antisymmetric_residue_cycle f holes c d hc hcd hantiC hantiD hstep
  let F : ℤ → ℤ := fun x => G (x : ZMod c)
  have hpc : Function.Periodic F (c : ℤ) := by
    intro x
    change G (((x + (c : ℤ) : ℤ) : ZMod c)) = G (x : ZMod c)
    rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]
  have hpd : Function.Periodic F (d : ℤ) := by
    intro x
    change G (((x + (d : ℤ) : ℤ) : ZMod c)) = G (x : ZMod c)
    rw [Int.cast_add, Int.cast_natCast]
    exact hperiod (x : ZMod c)
  have hF0 : F 0 = 0 := by simpa only [F, Int.cast_zero] using hG0
  have hFneg : ∀ x : ℤ, F (-x) = -F x := by
    intro x
    change G ((-x : ℤ) : ZMod c) = -G (x : ZMod c)
    rw [Int.cast_neg]
    exact hneg _
  have hd0 : G (d : ZMod c) = 0 := by
    have hh := hperiod 0
    simpa only [zero_add, hG0] using hh
  have hc0 : holes = false → f c = 0 := by
    intro hmode
    let n := d - c
    have hn0 : 0 < n := by dsimp only [n]; omega
    have hnd : n < d := by dsimp only [n]; omega
    have ha := hantiD c hc hcd (Or.inl hmode) (Or.inl hmode)
    change f c = -f n at ha
    by_cases hn : c ∣ n
    · have hr := bounded_period_reduce f holes c d hc hstep n hn0 hnd (Or.inl hmode)
      rw [ite_eq_left (Nat.mod_eq_zero_of_dvd hn)] at hr
      rw [hr] at ha
      omega
    · have hg := hnat n hn0 hnd hn
      have he : (n : ZMod c) = (d : ZMod c) := by
        dsimp only [n]
        rw [Nat.cast_sub hcd.le, ZMod.natCast_self, sub_zero]
      rw [he, hd0] at hg
      omega
  refine ⟨F, hpc, hpd, hF0, hFneg, ?_⟩
  intro n hn0 hnd hdef
  by_cases hn : c ∣ n
  · have hmode : holes = false := hdef.elim id (fun h => (h hn).elim)
    have hr := bounded_period_reduce f holes c d hc hstep n hn0 hnd hdef
    rw [ite_eq_left (Nat.mod_eq_zero_of_dvd hn), hc0 hmode] at hr
    have hz := (ZMod.natCast_eq_zero_iff n c).mpr hn
    change G ((n : ℤ) : ZMod c) = f n
    rw [Int.cast_natCast, hz, hG0, hr]
  · simpa only [F, Int.cast_natCast] using hnat n hn0 hnd hn

/-- Actual interval antisymmetry and guarded shifts supply all three gcd-period conclusions. -/
theorem antisymmetric_interval_gcd :
    (∀ x, 0 < x → x < d → periodPointDefined holes c x → c.gcd d ∣ x → f x = 0) ∧
      (∀ x, 0 < x → x + c.gcd d < d → ¬ c.gcd d ∣ x →
        f (x + c.gcd d) = f x) ∧
      ∀ x, 0 < x → x < c.gcd d → f x = -f (c.gcd d - x) := by
  obtain ⟨F, hpc, hpd, hF0, hneg, hagree⟩ :=
    antisymmetric_interval_extension f holes c d hc hcd hantiC hantiD hstep
  have hpr := periodic_nat_gcd F c d hpc hpd
  have hrc : c.gcd d ∣ c := Nat.gcd_dvd_left c d
  have hrle : c.gcd d ≤ c := Nat.le_of_dvd hc hrc
  have hnotC (x : ℕ) (hx : ¬ c.gcd d ∣ x) : ¬ c ∣ x := fun h => hx (hrc.trans h)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx0 hxd hdef hdiv
    have hp := periodic_int_remainder F (c.gcd d : ℤ) hpr (x : ℤ)
    rw [Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mpr hdiv), hF0] at hp
    exact (hagree x hx0 hxd hdef).symm.trans hp.symm
  · intro x hx0 hxd hnot
    have hy : ¬ c.gcd d ∣ x + c.gcd d := by
      intro hh
      exact hnot ((Nat.dvd_add_iff_left (dvd_refl (c.gcd d))).mpr hh)
    have hxD : x < d := by omega
    have hy0 : 0 < x + c.gcd d := by omega
    have hax := hagree x hx0 hxD (Or.inr (hnotC x hnot))
    have hay := hagree (x + c.gcd d) hy0 hxd (Or.inr (hnotC _ hy))
    calc
      f (x + c.gcd d) = F ((x + c.gcd d : ℕ) : ℤ) := hay.symm
      _ = F ((x : ℤ) + (c.gcd d : ℤ)) := by rw [Nat.cast_add]
      _ = F (x : ℤ) := hpr (x : ℤ)
      _ = f x := hax
  · intro x hx0 hxr
    have hxc : x < c := hxr.trans_le hrle
    have hy0 : 0 < c.gcd d - x := Nat.sub_pos_of_lt hxr
    have hyc : c.gcd d - x < c := by omega
    have hnx : ¬ c ∣ x := by
      intro hh
      have := Nat.le_of_dvd hx0 hh
      omega
    have hny : ¬ c ∣ c.gcd d - x := by
      intro hh
      have := Nat.le_of_dvd hy0 hh
      omega
    have hax := hagree x hx0 (hxc.trans hcd) (Or.inr hnx)
    have hay := hagree (c.gcd d - x) hy0 (hyc.trans hcd) (Or.inr hny)
    have harg : ((c.gcd d - x : ℕ) : ℤ) = -(x : ℤ) + (c.gcd d : ℤ) := by
      rw [Nat.cast_sub hxr.le]
      ring
    have hp := hpr (-(x : ℤ))
    rw [← harg, hay, hneg, hax] at hp
    omega

end SkewClassInflation
