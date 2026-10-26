/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.OverlapPeriods
import Mathlib.Tactic.Linarith

/-!
# Finite cut words cannot carry a proper multipart period

The finite-interval portion of `lem:overlap-power-rigidity` in
`shields-2026-skew-class-inflation.tex`.  The total length supplies the
gcd divisibility, the two half-length bounds supply every comparison
position, and the initial empty cut interval forces the proposed
internal factor word to be empty.  Sorry-free.
-/

namespace SkewClassInflation

/-- The finite cut word of an overlapped power forces every internal factor indicator to zero. -/
theorem overlap_cut_obstruction (m Q δ T q : ℕ) (hT : T = m * Q + δ)
    (hδpos : 0 < δ) (hq : 0 < q) (hqT : 2 * q ≤ T) (hQT : 2 * Q < T)
    (hqdiv : q ∣ T)
    (f : ℕ → ℤ) (t : ZMod q → ℤ)
    (hQperiod : ∀ x, x + Q ≤ T → f (x + Q) = f x)
    (hzero : ∀ x, x ≤ δ → f x = 0)
    (hread : ∀ x, x ≤ T → (x : ZMod q) ≠ 0 → f x = t (x : ZMod q)) :
    ∀ x : ZMod q, x ≠ 0 → t x = 0 := by
  classical
  let _ : NeZero q := ⟨by omega⟩
  have hqle : q ≤ T := by omega
  have hsmall (x : ZMod q) (hx : x ≠ 0) : 1 ≤ x.val ∧ x.val < q := by
    have hlt := x.val_lt
    have hpos : 0 < x.val := by
      by_contra hn
      have he : x.val = 0 := by omega
      have hh := x.natCast_zmod_val
      rw [he, Nat.cast_zero] at hh
      exact hx hh.symm
    exact ⟨hpos, hlt⟩
  by_cases hδq : δ < q
  · have hgdiv : Q.gcd q ∣ δ := by
      have hgT : Q.gcd q ∣ T := (Nat.gcd_dvd_right Q q).trans hqdiv
      have hgm : Q.gcd q ∣ m * Q := dvd_mul_of_dvd_right (Nat.gcd_dvd_left Q q) m
      rw [hT] at hgT
      exact (Nat.dvd_add_iff_right hgm).mpr hgT
    have hgδ : Q.gcd q ≤ δ := Nat.le_of_dvd hδpos hgdiv
    apply overlap_period_obstruction Q q δ hq hδq hgδ t
    · intro x hx hs
      have hh := hsmall x hx
      have hb : x.val + Q ≤ T := by omega
      have hleft := hread (x.val + Q) hb
        (by simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hs)
      have hright := hread x.val (by omega)
        (by simpa only [ZMod.natCast_zmod_val] using hx)
      have hp := hQperiod x.val hb
      rw [hleft, hright] at hp
      simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hp
    · intro r hr hrδ
      have hrq : r < q := by omega
      have hrne : (r : ZMod q) ≠ 0 := by
        intro he
        have hd := (ZMod.natCast_eq_zero_iff r q).mp he
        have hh := Nat.le_of_dvd (by omega : 0 < r) hd
        omega
      exact (hread r (by omega) hrne).symm.trans (hzero r hrδ)
  · intro x hx
    have hh := hsmall x hx
    have hinit := hzero x.val (by omega)
    have hreadx := hread x.val (by omega)
      (by simpa only [ZMod.natCast_zmod_val] using hx)
    rw [ZMod.natCast_zmod_val] at hreadx
    exact hreadx.symm.trans hinit

end SkewClassInflation
