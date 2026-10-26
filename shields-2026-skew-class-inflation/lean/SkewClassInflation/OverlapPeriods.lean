/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PuncturedCycles
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# The gcd obstruction for punctured periodic cut words

The modular-period argument in `lem:overlap-power-rigidity` and
`eq:cut-period-comparison` of
`shields-2026-skew-class-inflation.tex`.  The punctured function is
completed, Bezout's identity produces the gcd period, and the initial
zero interval meets every residue class.  Sorry-free.
-/

namespace SkewClassInflation

/-- Two integer periods supply their positive gcd period, by the actual Bezout coefficients. -/
theorem periodic_nat_gcd {A : Type*} (F : ℤ → A) (Q q : ℕ)
    (hQ : Function.Periodic F (Q : ℤ)) (hq : Function.Periodic F (q : ℤ)) :
    Function.Periodic F (Q.gcd q : ℤ) := by
  have hp := (hQ.int_mul (Q.gcdA q)).add_period (hq.int_mul (Q.gcdB q))
  simp only [Int.cast_id] at hp
  convert hp using 1
  rw [Nat.gcd_eq_gcd_ab]
  ring

/-- Integer remainder reduction preserves the value of a genuinely periodic function. -/
theorem periodic_int_remainder {A : Type*} (F : ℤ → A) (p : ℤ)
    (hp : Function.Periodic F p) (x : ℤ) : F (x % p) = F x := by
  have he := hp.int_mul (x / p) (x % p)
  simp only [Int.cast_id] at he
  have hx : x % p + (x / p) * p = x := by
    rw [mul_comm, Int.emod_add_mul_ediv]
  rw [hx] at he
  exact he.symm

/-- A punctured period and initial zeros force every nonzero cut indicator to vanish. -/
theorem overlap_period_obstruction (Q q δ : ℕ) (hq : 0 < q) (hδq : δ < q)
    (hgδ : Q.gcd q ≤ δ) (f : ZMod q → ℤ)
    (hstep : ∀ x : ZMod q, x ≠ 0 → x + (Q : ZMod q) ≠ 0 →
      f (x + (Q : ZMod q)) = f x)
    (hzero : ∀ r : ℕ, 1 ≤ r → r ≤ δ → f (r : ZMod q) = 0) :
    ∀ x : ZMod q, x ≠ 0 → f x = 0 := by
  classical
  let _ : NeZero q := ⟨by omega⟩
  let σ : Equiv.Perm (ZMod q) := Equiv.addRight (Q : ZMod q)
  let g : ZMod q → ℤ := fun x => if x = 0 then f (σ 0) else f x
  have hσ : ∀ x, g (σ x) = g x := punctured_cycle_completion σ 0 f hstep
  let F : ℤ → ℤ := fun x => g (x : ZMod q)
  have hPQ : Function.Periodic F (Q : ℤ) := by
    intro x
    change g ((x + (Q : ℤ) : ℤ) : ZMod q) = g (x : ZMod q)
    rw [Int.cast_add, Int.cast_natCast]
    exact hσ (x : ZMod q)
  have hPq : Function.Periodic F (q : ℤ) := by
    intro x
    change g ((x + (q : ℤ) : ℤ) : ZMod q) = g (x : ZMod q)
    rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]
  have hPg := periodic_nat_gcd F Q q hPQ hPq
  have hg : 0 < Q.gcd q := Nat.gcd_pos_of_pos_right Q hq
  have hinit (r : ℕ) (hr : 1 ≤ r) (hrδ : r ≤ δ) : F (r : ℤ) = 0 := by
    have hrq : r < q := by omega
    have hr0 : (r : ZMod q) ≠ 0 := by
      intro he
      have hh := (ZMod.natCast_eq_zero_iff r q).mp he
      have hle := Nat.le_of_dvd (by omega : 0 < r) hh
      omega
    change g ((r : ℤ) : ZMod q) = 0
    rw [Int.cast_natCast]
    change (if (r : ZMod q) = 0 then f (σ 0) else f (r : ZMod q)) = 0
    rw [ite_eq_right hr0]
    exact hzero r hr hrδ
  have hF0 : F 0 = 0 := by
    have he := hPg.eq
    exact he.symm.trans (hinit (Q.gcd q) hg hgδ)
  have hall (x : ℤ) : F x = 0 := by
    rw [← periodic_int_remainder F (Q.gcd q : ℤ) hPg x]
    have hr0 : 0 ≤ x % (Q.gcd q : ℤ) := Int.emod_nonneg _ (by omega)
    have hrh : x % (Q.gcd q : ℤ) < Q.gcd q := Int.emod_lt_of_pos _ (by omega)
    by_cases hr : x % (Q.gcd q : ℤ) = 0
    · rw [hr, hF0]
    · have he : ((x % (Q.gcd q : ℤ)).toNat : ℤ) = x % (Q.gcd q : ℤ) := by omega
      rw [← he]
      exact hinit _ (by omega) (by omega)
  intro x hx
  have hh := hall (x.val : ℤ)
  change g ((x.val : ℤ) : ZMod q) = 0 at hh
  rw [Int.cast_natCast, ZMod.natCast_zmod_val] at hh
  simpa only [g, ite_eq_right hx] using hh

end SkewClassInflation
