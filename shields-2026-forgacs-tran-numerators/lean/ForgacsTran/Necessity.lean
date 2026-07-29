/-
# Necessity of the numerator dependence

Supplies the two mechanical ingredients of
`../shields-2026-forgacs-tran-numerators.tex`, §6 «Consequences and sharpness»,
`prop:N-dependence`.

**Scope — read this before citing the module.**  `prop:N-dependence` asserts that
for each admissible denominator the constant `C` of `thm:main` cannot be bounded
uniformly over numerators.  That statement is **not** formalized here.  What is
proven is strictly less:

* `exceptional_unbounded` — for every `L` there **exists** a polynomial with at
  least `L` roots off `(0,∞)`.  No denominator `Q`, no `r`, and no coefficient
  sequence `P_m` appears; the count is of the witness's own roots.
* `dvd_exceptional_le` — root counts off a set are inherited by any multiple, the
  transfer lemma standing in for the paper's mechanism `P_m = R · H_m`.

Four links to the proposition are therefore missing: quantification over the
denominator; the hypothesis `R ∣ P_m` that `dvd_exceptional_le` consumes and
nothing supplies; the passage from these `ℝ`-side `roots.filter` counts to the
`ℂ`-side `exceptionalRoots … posRay` that `main_bound` bounds; and the negation
`¬ ∃ C, ∀ N, …` itself.  `rem:optimality-of-bounded-defect` is not formalized at
all.

Paper motivation, for orientation only and *not* formalized below: taking
`N(t,z) = R(z)` gives `P_m(z) = R(z) H_m(z)`, so every zero of `R` occurs in
every `P_m`; choosing `R(z) = ∏_{j=1}^{L}(z+j)` places `L` negative zeros in
every coefficient polynomial, and `L` is arbitrary.

* `Rneg L` — the witness `∏_{j=1}^{L}(X + j)`, with the `L` distinct negative
  roots `-1,…,-L`.

Sorry-free.
-/
import ForgacsTran.ZeroCount

open Classical Polynomial

open scoped BigOperators

namespace ForgacsTran

/-- Paper §6 `sec:consequences`, `prop:N-dependence` — `Rneg L = ∏_{j=1}^{L}
(X + j)`, the witness numerator with the `L` distinct negative roots `-1,…,-L`. -/
noncomputable def Rneg (L : ℕ) : ℝ[X] := ∏ j ∈ Finset.range L, (X + C ((j : ℝ) + 1))

/-- Paper §6 `sec:consequences`, `prop:N-dependence` (supporting): the witness
numerator is monic. -/
theorem Rneg_monic (L : ℕ) : (Rneg L).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

/-- Paper §6 `sec:consequences`, `prop:N-dependence` (supporting). -/
theorem Rneg_ne_zero (L : ℕ) : Rneg L ≠ 0 := (Rneg_monic L).ne_zero

/-- Paper §6 `sec:consequences`, `prop:N-dependence` (supporting) — `-(j+1)` is a
root of `Rneg L` for each `j < L`. -/
theorem Rneg_isRoot (L : ℕ) {j : ℕ} (hj : j ∈ Finset.range L) :
    (Rneg L).IsRoot (-((j : ℝ) + 1)) := by
  unfold Rneg
  rw [IsRoot.def, eval_prod]
  exact Finset.prod_eq_zero hj (by simp)

/-- Paper §6 `sec:consequences`, `prop:N-dependence` (supporting) — the `L`
distinct negative reals `-1,…,-L`. -/
noncomputable def Zneg (L : ℕ) : Finset ℝ :=
  (Finset.range L).image (fun j : ℕ => -((j : ℝ) + 1))

/-- Paper §6 `sec:consequences`, `prop:N-dependence` (supporting). -/
theorem Zneg_card (L : ℕ) : (Zneg L).card = L := by
  have hinj : Set.InjOn (fun j : ℕ => -((j : ℝ) + 1)) ↑(Finset.range L) := by
    intro a _ b _ hab
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  unfold Zneg
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- Paper §6 `sec:consequences`, `prop:N-dependence` (supporting). -/
theorem Zneg_root (L : ℕ) {x : ℝ} (hx : x ∈ Zneg L) : (Rneg L).IsRoot x := by
  unfold Zneg at hx
  rw [Finset.mem_image] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact Rneg_isRoot L hj

/-- Paper §6 `sec:consequences`, `prop:N-dependence` (supporting). -/
theorem Zneg_notMem_posReals (L : ℕ) {x : ℝ} (hx : x ∈ Zneg L) :
    x ∈ (Set.Ioi (0 : ℝ))ᶜ := by
  unfold Zneg at hx
  rw [Finset.mem_image] at hx
  obtain ⟨j, _, rfl⟩ := hx
  simp only [Set.mem_compl_iff, Set.mem_Ioi, not_lt]
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

/-- **`prop:N-dependence`, witness half.**  For every `L` there is a polynomial
`R` with at least `L` of its own roots off the positive ray.  This is the witness
family only: it does not mention `Q`, `r`, or `P_m`, and does not state the
non-uniformity of `C` as a negation.  See the module docstring for the four links
still missing. -/
theorem exceptional_unbounded (L : ℕ) :
    ∃ R : ℝ[X], R ≠ 0 ∧
      L ≤ (R.roots.filter (fun x => x ∈ (Set.Ioi (0 : ℝ))ᶜ)).card := by
  refine ⟨Rneg L, Rneg_ne_zero L, ?_⟩
  have key := le_card_filter (Rneg_ne_zero L) (fun x hx => Zneg_root L hx)
    (fun x hx => Zneg_notMem_posReals L hx)
  rw [Zneg_card] at key
  exact key

/-- Paper §6 `sec:consequences`, `prop:N-dependence` — the exceptional zeros of a
numerator are inherited by any coefficient polynomial it divides (the mechanism
`P_m = R · H_m`). -/
theorem dvd_exceptional_le {R P : ℝ[X]} (hP : P ≠ 0) (hdvd : R ∣ P) (S : Set ℝ) :
    (R.roots.filter (fun x => x ∈ S)).card ≤ (P.roots.filter (fun x => x ∈ S)).card := by
  apply Multiset.card_le_card
  apply Multiset.filter_le_filter
  exact Polynomial.roots.le_of_dvd hP hdvd

end ForgacsTran
