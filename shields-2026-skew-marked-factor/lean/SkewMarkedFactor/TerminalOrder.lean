/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.PowerCoordinates
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# Terminal order of an actual period derivative

«Recovering the factors» (`sec:extraction`, `eq:terminal`) of
`shields-2026-skew-marked-factor.tex`.
The terminal order is the supremum of the actual nonzero derivative orders.
Its identification requires a proved nonzero terminal derivative and a proved
vanishing tail; neither is built into the definition.
-/

namespace SkewMarkedFactor
open Gluing Gluing.Plan

/-- The actual repeated derivative, with order zero equal to the input polynomial. -/
noncomputable def deltaAt (p n : ℕ) : Lambda →ₗ[ℚ] Lambda :=
  pDerivWord (List.replicate n p)

@[simp]
theorem deltaAt_zero (p : ℕ) (f : Lambda) : deltaAt p 0 f = f := rfl

/-- First applying one period derivative leaves the remaining actual word. -/
theorem deltaAt_succ (p n : ℕ) (f : Lambda) :
    deltaAt p (n + 1) f = deltaAt p n (pDeriv p f) := rfl

/-- Consecutive words compose without changing the actual operator. -/
theorem deltaAt_add (p n m : ℕ) (f : Lambda) :
    deltaAt p (n + m) f = deltaAt p m (deltaAt p n f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, deltaAt_succ, deltaAt_succ, ih]

/-- A vanishing derivative forces every later order to vanish. -/
theorem deltaAt_after_zero (p n m : ℕ) (f : Lambda) (hn : deltaAt p n f = 0) :
    deltaAt p (n + m) f = 0 := by
  rw [deltaAt_add, hn, map_zero]

/-- The supplied-period terminal order reads only the parent polynomial and the period. -/
noncomputable def terminalOrder (P : Lambda) (p : ℕ) : ℕ :=
  sSup {j : ℕ | deltaAt p j P ≠ 0}

/-- A true last nonzero derivative identifies the actual supremum. -/
theorem terminalOrder_eq_of_last {P : Lambda} {p a : ℕ}
    (ha : deltaAt p a P ≠ 0) (hafter : ∀ j, a < j → deltaAt p j P = 0) :
    terminalOrder P p = a := by
  apply IsGreatest.csSup_eq
  refine ⟨ha, ?_⟩
  intro j hj
  by_contra h
  exact hj (hafter j (by omega))

/-- The immediate next zero is sufficient, since all subsequent words factor through it. -/
theorem terminalOrder_eq_of_next {P : Lambda} {p a : ℕ}
    (ha : deltaAt p a P ≠ 0) (hnext : deltaAt p (a + 1) P = 0) :
    terminalOrder P p = a := by
  apply terminalOrder_eq_of_last ha
  intro j hj
  have he : j = (a + 1) + (j - (a + 1)) := by omega
  rw [he]
  exact deltaAt_after_zero p (a + 1) _ P hnext

/-- The terminal polynomial is an actual derivative of the supplied input. -/
noncomputable def terminalDerivative (P : Lambda) (p : ℕ) : Lambda :=
  deltaAt p (terminalOrder P p) P

/-- The penultimate polynomial is the preceding actual derivative. -/
noncomputable def penultimateDerivative (P : Lambda) (p : ℕ) : Lambda :=
  deltaAt p (terminalOrder P p - 1) P

/-- The order-one derivative cannot vanish if a positive-order derivative survives. -/
theorem first_derivative_ne_zero {P : Lambda} {p a : ℕ} (ha : 0 < a)
    (h : deltaAt p a P ≠ 0) : pDeriv p P ≠ 0 := by
  intro hz
  have hzero : deltaAt p 1 P = 0 := by simpa only [deltaAt_succ, deltaAt_zero] using hz
  have he : a = 1 + (a - 1) := by omega
  apply h
  rw [he]
  exact deltaAt_after_zero p 1 _ P hzero

end SkewMarkedFactor
