/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.RealActiveLabels

/-!
# True cap signs in produced real chambers

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `thm:dual-general`).
Responses strictly below the closure top retain their values at every anchor section.
The simultaneous construction therefore produces positive true-cap products in both
chambers, rather than assuming cap positivity. Sorry-free.
-/

namespace SkewCornerDescent

open MvPolynomial

/-- A response below the anchor has the chamber's sign at the unchanged assignment. -/
theorem simultaneousRealChamber_sign_below {α : Type*}
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ ℝ)
    (htop : ∀ i, N ≤ top i)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (a : α) (ha : top a = K) (i : α) (hi : top i < K)
    (positive : Bool) (x : ℕ → ℝ) (hx : x ∈ simultaneousRealChamber K top p q positive) :
    eval x (q i) ≠ 0 ∧
      responseSign positive (rationalTriangularResponse (top i : ℕ) (p i) (q i) x) := by
  let root := rationalAnchorRoot (fun a : {i : α // top i = K} => p a.val)
    (fun a => q a.val) ⟨a, ha⟩ x
  let y := Function.update x (K : ℕ) root
  have hreg := (hx.2.2 ⟨a, ha⟩ ⟨i, ne_of_lt hi⟩).1
  have hsign := (hx.2.2 ⟨a, ha⟩ ⟨i, ne_of_lt hi⟩).2
  have hqeq : eval y (q i) = eval x (q i) := by
    apply eval_polynomial_eq_of_agree_below _ (K : ℕ)
      (fun j hj => lt_of_lt_of_le (hq i j hj) hNK)
    intro j hj
    simp only [y, Function.update_of_ne (Nat.ne_of_lt hj)]
  have hcorr := rational_correction_locality (top i : ℕ) (p i) (q i) (hp i)
    (fun j hj => lt_of_lt_of_le (hq i j hj) (htop i)) y x (by
      intro j hj
      dsimp only [y]
      rw [Function.update_of_ne (show j ≠ (K : ℕ) from Nat.ne_of_lt (lt_trans hj hi))])
  have heq : rationalTriangularResponse (top i : ℕ) (p i) (q i) y =
      rationalTriangularResponse (top i : ℕ) (p i) (q i) x := by
    simp only [rationalTriangularResponse, hcorr, y]
    rw [Function.update_of_ne (show (top i : ℕ) ≠ (K : ℕ) from Nat.ne_of_lt hi)]
  refine ⟨?_, ?_⟩
  · change eval y (q i) ≠ 0 at hreg
    rwa [hqeq] at hreg
  · change responseSign positive (rationalTriangularResponse (top i : ℕ) (p i) (q i) y)
      at hsign
    rwa [heq] at hsign

/-- Both true caps receive the prescribed sign and have a positive product at every
produced simultaneous point. Their denominators are also proved regular there. -/
theorem simultaneousRealChamber_true_cap_product {α : Type*}
    (N K : ℕ+) (hNK : N ≤ K) (top : α → ℕ+) (p q : α → MvPolynomial ℕ ℝ)
    (htop : ∀ i, N ≤ top i)
    (hp : ∀ i j, j ∈ (p i).vars → j < (top i : ℕ))
    (hq : ∀ i j, j ∈ (q i).vars → j < (N : ℕ))
    (closure left right : α) (hc : top closure = K)
    (hl : top left < K) (hr : top right < K)
    (positive : Bool) (x : ℕ → ℝ) (hx : x ∈ simultaneousRealChamber K top p q positive) :
    eval x (q closure) ≠ 0 ∧ eval x (q left) ≠ 0 ∧ eval x (q right) ≠ 0 ∧
      0 < rationalTriangularResponse (top left : ℕ) (p left) (q left) x *
        rationalTriangularResponse (top right : ℕ) (p right) (q right) x := by
  have hlower := simultaneousRealChamber_sign_below N K hNK top p q htop hp hq
    closure hc left hl positive x hx
  have hupper := simultaneousRealChamber_sign_below N K hNK top p q htop hp hq
    closure hc right hr positive x hx
  exact ⟨hx.1 ⟨closure, hc⟩, hlower.1, hupper.1,
    signed_cap_product_pos positive hlower.2 hupper.2⟩

end SkewCornerDescent
