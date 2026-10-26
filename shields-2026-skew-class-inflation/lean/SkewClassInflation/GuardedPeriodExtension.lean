/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.AntisymmetricPeriods

/-!
# Extending partial periods across larger intervals

Residue reduction for the signed-cut period argument in the ribbon input to
`lem:overlap-power-rigidity` of `shields-2026-skew-class-inflation.tex`.
Coordinates divisible by the deleted period are never used.  Sorry-free.
-/

namespace SkewClassInflation

/-- A larger compatible step reduces every defined coordinate to its actual remainder. -/
theorem guarded_period_reduce {A : Type*} (f : ℕ → A) (c m d : ℕ)
    (hm : 0 < m) (hcm : c ∣ m)
    (hstep : ∀ x, 0 < x → x + m < d → ¬ c ∣ x → ¬ c ∣ x + m →
      f (x + m) = f x) :
    ∀ n, 0 < n → n < d → ¬ c ∣ n → f n = f (n % m) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn0 hnd hn
    by_cases hlt : n < m
    · rw [Nat.mod_eq_of_lt hlt]
    · have hmn : m ≤ n := by omega
      have hne : n ≠ m := fun he => hn (he ▸ hcm)
      have hsub0 : 0 < n - m := by omega
      have hsub : ¬ c ∣ n - m := by
        intro hd
        apply hn
        have he := Nat.dvd_add hd hcm
        rwa [Nat.sub_add_cancel hmn] at he
      have hs := hstep (n - m) hsub0 (by omega) hsub
        (by simpa only [Nat.sub_add_cancel hmn] using hn)
      rw [Nat.sub_add_cancel hmn] at hs
      have hi := ih (n - m) (Nat.sub_lt hn0 hm) hsub0 (by omega) hsub
      have he : n = m + (n - m) := by omega
      have hmod : n % m = (n - m) % m := by
        conv_lhs => rw [he]
        simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      exact hs.trans (hi.trans (congrArg f hmod.symm))

/-- A short period on the initial interval extends by a compatible longer step. -/
theorem guarded_period_extend {A : Type*} (f : ℕ → A) (c m d : ℕ)
    (hc : 0 < c) (hm : 0 < m) (hcm : c ∣ m)
    (hsmall : ∀ x, 0 < x → x + c < m → ¬ c ∣ x → ¬ c ∣ x + c →
      f (x + c) = f x)
    (hlarge : ∀ x, 0 < x → x + m < d → ¬ c ∣ x → ¬ c ∣ x + m →
      f (x + m) = f x) :
    ∀ x, 0 < x → x + c < d → ¬ c ∣ x → ¬ c ∣ x + c → f (x + c) = f x := by
  have hreduce (n : ℕ) (hn0 : 0 < n) (hnd : n < d) (hn : ¬ c ∣ n) :
      f n = f (n % c) := by
    have hfirst := guarded_period_reduce f c m d hm hcm hlarge n hn0 hnd hn
    have hr : ¬ c ∣ n % m := by
      intro hd
      apply hn
      apply Nat.dvd_of_mod_eq_zero
      rw [← Nat.mod_mod_of_dvd n hcm, Nat.mod_eq_zero_of_dvd hd]
    have hr0 : 0 < n % m := by
      by_contra he
      exact hr (by simp only [show n % m = 0 by omega, dvd_zero])
    have hsecond := guarded_period_reduce f c c m hc (dvd_refl c) hsmall
      (n % m) hr0 (Nat.mod_lt n hm) hr
    rw [Nat.mod_mod_of_dvd n hcm] at hsecond
    exact hfirst.trans hsecond
  intro x hx hxd hn hnext
  rw [hreduce (x + c) (by omega) hxd hnext,
    hreduce x hx (by omega) hn, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]

end SkewClassInflation
