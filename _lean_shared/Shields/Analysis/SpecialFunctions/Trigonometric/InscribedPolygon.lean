/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The sine sum of a partition of the circle is nonnegative

Cut the circle into arcs `a₁, …, a_m ≥ 0` with `∑ aᵢ = 2π`.  Then `∑ sin aᵢ ≥ 0` -- it is
twice the signed area of the polygon inscribed on the cut points, and a polygon inscribed
in a circle has nonnegative area however the cuts fall.

The proof is by **merging** rather than by any area computation.  The half-angle identity

`sin(2x) + sin(2y) - sin(2x + 2y) = 4 sin x · sin y · sin (x + y)`

has all three factors nonnegative when the arcs lie in `[0, 2π]`, so replacing two arcs by
their union can only lower the sine sum.  Merge down to two arcs `a` and `2π - a`, whose
sines cancel, and the bound is `0`.

Mathlib has no subadditivity for `Real.sin` and no inscribed-polygon statement of any kind;
`Geometry/Euclidean/Angle/Sphere` is the inscribed-*angle* theorem, a different result.

## Main results

* `Shields.sin_add_sin_sub_sin_add` -- the merge identity, at the half angles.
* `Shields.sin_add_le_sin_add_sin` -- `sin (a + b) ≤ sin a + sin b` for `0 ≤ a`, `0 ≤ b`,
  `a + b ≤ 2π`: merging two arcs lowers the sine sum.
* `Shields.sum_sin_nonneg_of_sum_eq_two_pi` -- the polygon lemma, for a list of arcs.
* `Shields.sum_sin_shift_ge` -- the polygon lemma for `N` arcs `θ + 2 φ k` together with
  `M` copies of `θ`, which is the shape an angle-sum constraint delivers.

## Implementation notes

The arcs are a `List ℝ` rather than a `Finset`-indexed family, because the induction merges
two entries into one and so has to shrink the carrier; the length is carried as a separate
fuel parameter so that the recursion is structural.

Used by `forgacs-tran-numerators`.

## Tags

sine, inscribed polygon, circle partition, arc, subadditive
-/

open Real

namespace Shields

/-- **`sin a + sin b - sin (a + b)` factors.**  Written at the half angles, which is where
the three sines that control its sign live. -/
theorem sin_add_sin_sub_sin_add (x y : ℝ) :
    Real.sin (2 * x) + Real.sin (2 * y) - Real.sin (2 * x + 2 * y)
      = 4 * Real.sin x * Real.sin y * Real.sin (x + y) := by
  have h : (2 : ℝ) * x + 2 * y = 2 * (x + y) := by ring
  rw [h, Real.sin_two_mul, Real.sin_two_mul, Real.sin_two_mul, Real.sin_add, Real.cos_add]
  linear_combination (-2 * Real.sin x * Real.cos x) * (Real.sin_sq_add_cos_sq y)
    + (-2 * Real.sin y * Real.cos y) * (Real.sin_sq_add_cos_sq x)

/-- **Merging two arcs lowers the sine sum.**  The one step the polygon lemma runs on. -/
theorem sin_add_le_sin_add_sin {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * π) :
    Real.sin (a + b) ≤ Real.sin a + Real.sin b := by
  have key := sin_add_sin_sub_sin_add (a / 2) (b / 2)
  rw [show (2 : ℝ) * (a / 2) + 2 * (b / 2) = a + b by ring,
    show (2 : ℝ) * (a / 2) = a by ring, show (2 : ℝ) * (b / 2) = b by ring] at key
  have hπ : (0 : ℝ) < π := pi_pos
  have hsa : 0 ≤ Real.sin (a / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsb : 0 ≤ Real.sin (b / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsab : 0 ≤ Real.sin (a / 2 + b / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  linarith [key, mul_nonneg (mul_nonneg hsa hsb) hsab]

private theorem sum_sin_nonneg_aux : ∀ (m : ℕ) (L : List ℝ), L.length ≤ m →
    (∀ x ∈ L, 0 ≤ x) → L.sum = 2 * π → 0 ≤ (L.map Real.sin).sum := by
  intro m
  induction m with
  | zero =>
      intro L hlen _ hsum
      rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)] at hsum
      simp only [List.sum_nil] at hsum
      exfalso
      have := pi_pos
      linarith
  | succ m ih =>
      intro L hlen hnn hsum
      match L with
      | [] =>
          simp only [List.sum_nil] at hsum
          exfalso
          have := pi_pos
          linarith
      | [x] =>
          have hx : x = 2 * π := by simpa using hsum
          simp [hx, Real.sin_two_pi]
      | x :: y :: t =>
          have hx : 0 ≤ x := hnn x (by simp)
          have hy : 0 ≤ y := hnn y (by simp)
          have ht : ∀ z ∈ t, 0 ≤ z := fun z hz => hnn z (by simp [hz])
          have hts : 0 ≤ t.sum := List.sum_nonneg ht
          have hsum' : x + y + t.sum = 2 * π := by simpa [add_assoc] using hsum
          have hxy : x + y ≤ 2 * π := by linarith
          have hIH := ih ((x + y) :: t) (by simpa using Nat.succ_le_succ_iff.1 hlen)
            (fun z hz => by
              rcases List.mem_cons.1 hz with rfl | hz'
              · linarith
              · exact ht z hz')
            (by simpa [add_assoc] using hsum')
          have hmerge := sin_add_le_sin_add_sin hx hy hxy
          simp only [List.map_cons, List.sum_cons] at hIH ⊢
          linarith

/-- **The polygon lemma.**  Arcs of a partition of the circle have nonnegative sine sum --
twice the area of the inscribed polygon they cut out.

Proved by merging: `sin (a + b) ≤ sin a + sin b` on arcs, so collapsing the list can only
lower the sum, and two arcs `a`, `2π - a` sum to `0`. -/
theorem sum_sin_nonneg_of_sum_eq_two_pi {L : List ℝ} (hnn : ∀ x ∈ L, 0 ≤ x)
    (hsum : L.sum = 2 * π) : 0 ≤ (L.map Real.sin).sum :=
  sum_sin_nonneg_aux L.length L le_rfl hnn hsum

/-- **The polygon lemma in the shape an angle-sum constraint delivers.**  `N` arcs
`θ + 2 φ k` and `M` copies of `θ`, with `N θ + 2 ∑ φ + M θ = 2π`. -/
theorem sum_sin_shift_ge {N M : ℕ} {φ : Fin N → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hφ : ∀ k, 0 ≤ φ k)
    (hsum : (N : ℝ) * θ + 2 * ∑ k, φ k + (M : ℝ) * θ = 2 * π) :
    -((M : ℝ) * Real.sin θ) ≤ ∑ k, Real.sin (θ + 2 * φ k) := by
  classical
  set L : List ℝ := List.ofFn (fun k : Fin N => θ + 2 * φ k) ++ List.replicate M θ with hL
  have hnn : ∀ x ∈ L, 0 ≤ x := by
    intro x hx
    rw [hL, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      have := hφ k
      linarith
    · rw [List.eq_of_mem_replicate hx]; exact hθ
  have hsumL : L.sum = 2 * π := by
    rw [hL, List.sum_append, List.sum_ofFn, List.sum_replicate, nsmul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    linarith [hsum]
  have hpoly := sum_sin_nonneg_of_sum_eq_two_pi hnn hsumL
  rw [hL, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
    List.map_replicate, List.sum_replicate, nsmul_eq_mul] at hpoly
  simp only [Function.comp_apply] at hpoly
  linarith


/-! ### Axiom footprint -/

/-- info: 'Shields.sin_add_le_sin_add_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sin_add_le_sin_add_sin

/-- info: 'Shields.sum_sin_shift_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_sin_shift_ge

end Shields
