/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealTrueCapDualNonvanishing
import SkewCornerDescent.CyclicWindowNonvanishing

/-!
# Literal cyclic dual nonvanishing over real coefficients

Supports `shields-2026-skew-corner-descent.tex` (`thm:dual-general`, `thm:dual-period`).
The produced true-cap exposure theorem is composed with the literal closure-word
inventory identities. The conclusion concerns the actual cyclic full-period and
whole-word defects, not only their cleared surrogates. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial CyclicWindows PhaseInventory
open scoped BigOperators

/-- Literal full-period and whole-word cyclic defects cannot both vanish for a faithful
triangular family with two active classes. All inventory normalization and clearing units
are produced internally; no coprimality or geometric separation is used. -/
theorem realTrueCaps_windowDefect_nonvanishing {α F : Type*}
    [Fintype α] [DecidableEq α] [Field F] [CharZero F]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s) (hsd : s ≤ d) (hk : 0 < k)
    (φ : MvPolynomial ℕ ℝ →+* F) (hφ : Function.Injective φ)
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ ℝ)
    (htop : ∀ a, N ≤ top a)
    (hp : ∀ a j, j ∈ (p a).vars → j < (top a : ℕ))
    (hq : ∀ a j, j ∈ (q a).vars → j < (N : ℕ)) (hq0 : ∀ a, q a ≠ 0)
    (closure left right : α) (hclosure : top closure = K)
    (hleft : top left < K) (hright : top right < K)
    (word : ZMod (r * d) → α) (label : α → ℝ)
    (hactiveTop : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 → top a = K)
    (hdistinct : Function.Injective (fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)))
    (hsource : ∀ a, classDefect word 1 d s (r * s - 1) 0 a ≠ 0 →
      let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
      response a = response closure - φ (C (label a)) * (response left * response right))
    (htwo : ∃ a b, a ≠ b ∧ classDefect word 1 d s (r * s - 1) 0 a ≠ 0 ∧
      classDefect word 1 d s (r * s - 1) 0 b ≠ 0) :
    let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
    let e := classDefect word 1 d s (r * s - 1) 0
    windowDefect (response ∘ word) response e (k * d + s)
        (k * (r * d) + r * s) (r * d) ≠ 0 ∨
      windowDefect (response ∘ word) response e (k * d + s)
        (k * (r * d) + r * s) (k * (r * d) + r * s) ≠ 0 := by
  classical
  let response := fun a => φ (X (top a : ℕ)) + φ (p a) / φ (q a)
  have hreg (a : α) : response a ≠ 0 := real_triangular_source_ne_zero φ hφ
    (top a : ℕ) (p a) (q a) (hp a)
    (fun j hj => lt_of_lt_of_le (hq a j hj) (htop a)) (hq0 a)
  have hcore := realTrueCaps_dual_nonvanishing hr hd hs φ hφ N K hNK top p q
    htop hp hq hq0 closure left right hclosure hleft hright word k label
    hactiveTop hdistinct hsource htwo
  dsimp only
  rw [windowDefect_eq_last]
  exact cleared_dual_implies_window_nonvanishing hr hs hsd hk word response hreg hcore

end SkewCornerDescent
