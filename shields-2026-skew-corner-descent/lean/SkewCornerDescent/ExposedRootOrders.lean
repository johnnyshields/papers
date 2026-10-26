/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedWindowPoles
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Exact exposed root orders of complete cyclic reciprocal sums

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
The numerator has order zero and the complete denominator has the actual maximal window
order. Every cyclic start and repeated wrap is retained. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

/-- Powers of a nonzero polynomial with a simple root have exactly the stated root order. -/
theorem simpleRoot_pow_order (p : Polynomial ℝ) (r : ℝ)
    (h : Polynomial.rootMultiplicity r p = 1) (m : ℕ) :
    Polynomial.rootMultiplicity r (p ^ m) = m := by
  have hp : p ≠ 0 := by
    intro hz
    rw [hz, Polynomial.rootMultiplicity_zero] at h
    exact Nat.zero_ne_one h
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ih, h]

/-- Same-sign exposed terms give the exact numerator and denominator root orders, not merely
nonvanishing of the reciprocal sum. The simple-anchor premise is supplied by the
coordinate slice. -/
theorem cyclic_inverse_window_root_orders {G α : Type*}
    [AddCommGroup G] [Fintype G] [Fintype α] [DecidableEq α]
    (word : G → α) (step : G) (j : ℕ) (X : α)
    (num den : α → Polynomial ℝ) (r sign : ℝ)
    (hroot : Polynomial.eval r (num X) = 0)
    (hsimple : Polynomial.rootMultiplicity r (num X) = 1)
    (hden : ∀ Y, 0 < Polynomial.eval r (den Y))
    (hsign : ∀ Y, Y ≠ X → 0 < sign * Polynomial.eval r (num Y)) :
    let count := fun Y i => windowSum (PhaseInventory.classMask word Y) step j i
    let bound := maximalClassWindowCount word step j
    let numerator := clearedPoleSum Finset.univ (num X) (bound X) (count X)
      (fun i => den X ^ count X i * ∏ Y ∈ Finset.univ.erase X,
        num Y ^ (bound Y - count Y i) * den Y ^ count Y i)
    let denominator := num X ^ bound X * ∏ Y ∈ Finset.univ.erase X, num Y ^ bound Y
    numerator ≠ 0 ∧ Polynomial.rootMultiplicity r numerator = 0 ∧
      denominator ≠ 0 ∧ Polynomial.rootMultiplicity r denominator = bound X := by
  classical
  dsimp only
  let bound := maximalClassWindowCount word step j
  have hpos := cyclic_inverse_window_numerator_eval_pos word step j X num den
    (Polynomial.evalRingHom r) sign hroot hden hsign
  dsimp only at hpos
  have hn : Polynomial.eval r (clearedPoleSum Finset.univ (num X) (bound X)
      (fun i => windowSum (PhaseInventory.classMask word X) step j i)
      (fun i => den X ^ windowSum (PhaseInventory.classMask word X) step j i *
        ∏ Y ∈ Finset.univ.erase X,
          num Y ^ (bound Y - windowSum (PhaseInventory.classMask word Y) step j i) *
            den Y ^ windowSum (PhaseInventory.classMask word Y) step j i)) ≠ 0 := by
    intro hz
    dsimp only [bound] at hz
    simp only [Polynomial.coe_evalRingHom] at hpos
    rw [hz, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hp : num X ≠ 0 := by
    intro hz
    rw [hz, Polynomial.rootMultiplicity_zero] at hsimple
    exact Nat.zero_ne_one hsimple
  have hoff : ∀ Y ∈ Finset.univ.erase X, Polynomial.eval r (num Y) ≠ 0 := by
    intro Y hY hz
    have hs := hsign Y (Finset.mem_erase.mp hY).1
    rw [hz, mul_zero] at hs
    exact (lt_irrefl 0) hs
  have he : Polynomial.eval r (∏ Y ∈ Finset.univ.erase X, num Y ^ bound Y) ≠ 0 := by
    change (Polynomial.evalRingHom r) (∏ Y ∈ Finset.univ.erase X, num Y ^ bound Y) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun Y hY => by
      rw [map_pow]
      exact pow_ne_zero _ (hoff Y hY)
  have hprod : (∏ Y ∈ Finset.univ.erase X, num Y ^ bound Y) ≠ 0 := by
    intro hz
    exact he (by rw [hz, Polynomial.eval_zero])
  have hd := mul_ne_zero (pow_ne_zero (bound X) hp) hprod
  refine ⟨?_, Polynomial.rootMultiplicity_eq_zero hn, hd, ?_⟩
  · intro hz
    exact hn (by rw [hz, Polynomial.eval_zero])
  · rw [Polynomial.rootMultiplicity_mul hd, simpleRoot_pow_order (num X) r hsimple,
      Polynomial.rootMultiplicity_eq_zero he, add_zero]

end SkewCornerDescent.CyclicWindows
