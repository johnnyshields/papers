/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ZeroCount

/-!
# Necessity of the numerator dependence

**Scope — read this before citing the module.**  That passage asserts that
for each admissible denominator the constant `C` of `thm:main` cannot be bounded
uniformly over numerators.  That statement is **not** formalized here.  What is
proven is strictly less:

## Main statements

* `exceptional_unbounded` — for every `L` there **exists** a polynomial with at
  least `L` roots off `(0,∞)`.  No denominator `Q`, no `r`, and no coefficient
  sequence `P_m` appears; the count is of the witness's own roots.
* `dvd_exceptional_le` — root counts off a set are inherited by any multiple, the
  transfer lemma standing in for the paper's mechanism `P_m = R · H_m`.

* `negRootPoly L` — the witness `∏_{j=1}^{L}(X + j)`, with the `L` distinct negative
  roots `-1,…,-L`.

## Implementation notes

Four links to the paper's argument are therefore missing: quantification over the
denominator; the hypothesis `R ∣ P_m` that `dvd_exceptional_le` consumes and
nothing supplies; the passage from these `ℝ`-side `roots.filter` counts to the
`ℂ`-side `exceptionalRoots … posRay` that `main_bound` bounds; and the negation
`¬ ∃ C, ∀ N, …` itself.

Paper motivation, for orientation only and *not* formalized below: taking
`N(t,z) = R(z)` gives `P_m(z) = R(z) H_m(z)`, so every zero of `R` occurs in
every `P_m`; choosing `R(z) = ∏_{j=1}^{L}(z+j)` places `L` negative zeros in
every coefficient polynomial, and `L` is arbitrary.

Sorry-free.

## References

Supplies the two mechanical ingredients of
`../shields-2026-forgacs-tran-numerators.tex`, `sec:introduction` «Introduction»,
`sec:introduction`, where the paper makes the point directly: `N(t,z) = R(z)`
forces `P_m = R · H_m`, so the fixed zeros of `R` sit in every coefficient
polynomial.

## Tags

necessity, numerator dependence, uniform bound
-/

open Polynomial

open scoped BigOperators

namespace ForgacsTran

/-- Paper `sec:introduction` — `negRootPoly L = ∏_{j=1}^{L}
(X + j)`, the witness numerator with the `L` distinct negative roots `-1,…,-L`. -/
noncomputable def negRootPoly (L : ℕ) : ℝ[X] := ∏ j ∈ Finset.range L, (X + C ((j : ℝ) + 1))

/-- Paper `sec:introduction` (supporting): the witness
numerator is monic. -/
theorem negRootPoly_monic (L : ℕ) : (negRootPoly L).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

/-- Paper `sec:introduction` (supporting). -/
theorem negRootPoly_ne_zero (L : ℕ) : negRootPoly L ≠ 0 := (negRootPoly_monic L).ne_zero

/-- Paper `sec:introduction` (supporting) — `-(j+1)` is a
root of `negRootPoly L` for each `j < L`. -/
theorem negRootPoly_isRoot (L : ℕ) {j : ℕ} (hj : j ∈ Finset.range L) :
    (negRootPoly L).IsRoot (-((j : ℝ) + 1)) := by
  unfold negRootPoly
  rw [IsRoot.def, eval_prod]
  exact Finset.prod_eq_zero hj (by simp)

/-- Paper `sec:introduction` (supporting) — the `L`
distinct negative reals `-1,…,-L`. -/
noncomputable def negRootSet (L : ℕ) : Finset ℝ :=
  (Finset.range L).image (fun j : ℕ => -((j : ℝ) + 1))

/-- Paper `sec:introduction` (supporting). -/
theorem negRootSet_card (L : ℕ) : (negRootSet L).card = L := by
  have hinj : Set.InjOn (fun j : ℕ => -((j : ℝ) + 1)) ↑(Finset.range L) := by
    intro a _ b _ hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  unfold negRootSet
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- Paper `sec:introduction` (supporting). -/
theorem negRootSet_root (L : ℕ) {x : ℝ} (hx : x ∈ negRootSet L) : (negRootPoly L).IsRoot x := by
  unfold negRootSet at hx
  rw [Finset.mem_image] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact negRootPoly_isRoot L hj

/-- Paper `sec:introduction` (supporting). -/
theorem negRootSet_notMem_posReals (L : ℕ) {x : ℝ} (hx : x ∈ negRootSet L) :
    x ∈ (Set.Ioi (0 : ℝ))ᶜ := by
  unfold negRootSet at hx
  rw [Finset.mem_image] at hx
  obtain ⟨j, _, rfl⟩ := hx
  simp only [Set.mem_compl_iff, Set.mem_Ioi, not_lt]
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

/-- **`sec:introduction`, witness half.**  For every `L` there is a polynomial
`R` with at least `L` of its own roots off the positive ray.  This is the witness
family only: it does not mention `Q`, `r`, or `P_m`, and does not state the
non-uniformity of `C` as a negation.  See the module docstring for the four links
still missing. -/
theorem exceptional_unbounded (L : ℕ) :
    ∃ R : ℝ[X], R ≠ 0 ∧
      L ≤ (R.roots.filter (fun x => x ∈ (Set.Ioi (0 : ℝ))ᶜ)).card := by
  refine ⟨negRootPoly L, negRootPoly_ne_zero L, ?_⟩
  have key := le_card_filter (negRootPoly_ne_zero L) (fun x hx => negRootSet_root L hx)
    (fun x hx => negRootSet_notMem_posReals L hx)
  rw [negRootSet_card] at key
  exact key

open scoped Classical in
/-- Paper `sec:introduction` — the exceptional zeros of a
numerator are inherited by any coefficient polynomial it divides (the mechanism
`P_m = R · H_m`). -/
theorem dvd_exceptional_le {R P : ℝ[X]} (hP : P ≠ 0) (hdvd : R ∣ P) (S : Set ℝ) :
    (R.roots.filter (fun x => x ∈ S)).card ≤ (P.roots.filter (fun x => x ∈ S)).card := by
  apply Multiset.card_le_card
  apply Multiset.filter_le_filter
  exact Polynomial.roots.le_of_dvd hP hdvd

end ForgacsTran
