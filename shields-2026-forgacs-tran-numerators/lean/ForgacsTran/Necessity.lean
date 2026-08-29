/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.Reduction
import ForgacsTran.ZeroCount

/-!
# Necessity of the numerator dependence

`sec:introduction` asserts that for an admissible denominator the constant `C`
of `thm:main` cannot be bounded uniformly over numerators.  That statement is
`not_exists_uniform_exceptional_bound`, and its route is the paper's own:
`N(t,z) = R(z)` forces `P_m = R · H_m`, so the zeros of `R` sit in every
coefficient polynomial and `deg R` is arbitrary.

## Main statements

* `negRootPoly L` — the witness `∏_{j=1}^{L}(X + j)`, with the `L` distinct negative
  roots `-1,…,-L`.
* `exceptional_unbounded` — for every `L` there **exists** a polynomial with at
  least `L` roots off `(0,∞)`.  No denominator `Q`, no `r`, and no coefficient
  sequence `P_m` appears; the count is of the witness's own roots.
* `dvd_exceptional_le` — root counts off a set are inherited by any multiple, the
  transfer lemma standing in for the paper's mechanism `P_m = R · H_m`.
* `exceptional_unbounded_of_denomConv` — the two joined, over a denominator with
  unit diagonal: for every `L` there is a numerator `R` such that *every*
  coefficient polynomial of the recurrence it drives carries at least `L` roots
  off the positive ray.  The divisibility is `Reduction.dvd_of_denomConv_const`.
* `card_exceptionalRoots_le_map` — the real zeros of `P` off `(0,∞)` are at most
  the complex zeros of its complexification off `posRay`, which is the count
  `main_bound` bounds.  Strict where `P` has a non-real zero.
* `exceptional_unbounded_ftDenom` — the witness over the paper's own pencil
  `Q(t) + z t^r`, whose convolution diagonal `d_0 = C(Q(0))` is a unit by
  `isUnit_ftDenom_zero`.  Both counts are delivered.
* `not_exists_uniform_exceptional_bound` and its complex form
  `not_exists_uniform_exceptional_bound_complex` — the negation itself, over
  numerator sequences constrained only by the properness `thm:main` assumes.
  `not_exists_uniform_exceptional_bound_linear` instantiates it at the admissible
  `Q(t) = 1 - t`, `r = 1` of `prop:linear-case`.

## Implementation notes

The mechanism `P_m = R · H_m` is formalized: taking `N(t,z) = R(z)` — the
numerator sequence `N_m = [m = 0]·R` — the solution of the denominator recurrence
is `R` times the solution for `N_m = [m = 0]`, because the diagonal `d_0 = Q(0)`
is a unit and the convolution is linear in the coefficient sequence
(`Reduction.dvd_of_denomConv_const`).  Choosing `R(z) = ∏_{j=1}^{L}(z+j)` then
places `L` negative zeros in every coefficient polynomial, and `L` is arbitrary.

Properness enters as `N_m = 0` for `m ≥ max{deg Q, r}`, which is
`deg_t N < deg_t(Q(t) + z t^r)` read off the coefficient sequence
(`prop:initial-data`).  The witness is supported at `m = 0` alone, so it is
proper for every admissible pencil, and `r ≥ 1` is all that is needed — the
paper's extra `max{deg Q, r} > 1` is not consumed.

The negation carries its own non-vacuity.  Its conclusion is guarded by
`P_m ≠ 0`, and a guard nothing meets would make the negated statement true and
the negation unprovable; `ne_zero_of_denomConv_const` meets it at `m = 0`, where
the convolution reads `d_0 P_0 = R`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Introduction»
(`sec:introduction`, `eq:P-generating-intro`), where the paper makes the point
directly: `N(t,z) = R(z)` forces `P_m = R · H_m`, so the fixed zeros of `R` sit
in every coefficient polynomial.

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
non-uniformity of `C` as a negation; `not_exists_uniform_exceptional_bound` is
where those are added. -/
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

open scoped Classical in
/-- **`sec:introduction`, witness and transfer joined.**  For every `L` there is a
numerator `R` such that whenever the coefficient sequence `P` solves the
denominator recurrence driven by the constant numerator `N(t,z) = R(z)` over a
denominator with unit diagonal `d_0`, every nonzero `P_m` has at least `L`
exceptional zeros off the positive ray.  The witness is `negRootPoly L`, its
divisibility `R ∣ P_m` is `Reduction.dvd_of_denomConv_const`, and the inheritance
of the count is `dvd_exceptional_le`.

The denominator here is any sequence with unit diagonal.  Tied to the paper's
admissible pencil it is `exceptional_unbounded_ftDenom`, and stated as the
negation it is `not_exists_uniform_exceptional_bound`. -/
theorem exceptional_unbounded_of_denomConv (L : ℕ) :
    ∃ R : ℝ[X], R ≠ 0 ∧ ∀ d : ℕ → ℝ[X], IsUnit (d 0) → ∀ P : ℕ → ℝ[X],
      (∀ m, denomConv d P m = if m = 0 then R else 0) → ∀ m, P m ≠ 0 →
        L ≤ (exceptionalRoots (P m) (Set.Ioi (0 : ℝ))).card := by
  refine ⟨negRootPoly L, negRootPoly_ne_zero L, fun d hd P hP m hPm => ?_⟩
  have key := le_card_roots_filter (S := (Set.Ioi (0 : ℝ))ᶜ) (negRootPoly_ne_zero L)
    (fun x hx => negRootSet_root L hx) (fun x hx => negRootSet_notMem_posReals L hx)
  rw [negRootSet_card] at key
  have htrans := dvd_exceptional_le hPm (dvd_of_denomConv_const hd _ hP m)
    ((Set.Ioi (0 : ℝ))ᶜ)
  simpa [exceptionalRoots] using key.trans htrans

/-! ### From the real zero count to the complex zero count

`main_bound` counts the zeros of `P_m` in `ℂ` lying off `posRay`; the witness
above counts the real zeros of `P_m` lying off `(0,∞)`.  The passage is
`Polynomial.map_roots_le`: a real root survives, with multiplicity, in the
complexification, and `ofReal` carries the complement of `(0,∞)` into the
complement of `posRay`.  The inequality is strict in general — `X^2+1` has no
real zero and two complex ones off the ray — so the real count is a lower bound
for the complex one and never the reverse. -/

/-- Paper `sec:geometry` (supporting) — a real number lands on the positive ray
exactly when it is positive.  `Complex.ofReal` is injective, so the image
`posRay` reflects membership. -/
theorem algebraMap_mem_posRay_iff (x : ℝ) :
    (algebraMap ℝ ℂ) x ∈ posRay ↔ x ∈ Set.Ioi (0 : ℝ) := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [show y = x from Complex.ofReal_inj.mp (by simpa using hxy)] at hy
  · intro hx
    exact ⟨x, hx, by simp⟩

open scoped Classical in
/-- **The `ℝ`-side to `ℂ`-side passage.**  The real zeros of `P` off `(0,∞)`,
counted with multiplicity, are at most the complex zeros of its complexification
off `posRay`.  This is what carries the necessity witness — which counts real
zeros — into the count `thm:main` bounds. -/
theorem card_exceptionalRoots_le_map (P : Polynomial ℝ) :
    (exceptionalRoots P (Set.Ioi (0 : ℝ))).card
      ≤ (exceptionalRoots (P.map (algebraMap ℝ ℂ)) posRay).card := by
  have hinj : Function.Injective (algebraMap ℝ ℂ) := (algebraMap ℝ ℂ).injective
  have hle : P.roots.map (algebraMap ℝ ℂ) ≤ (P.map (algebraMap ℝ ℂ)).roots :=
    Polynomial.map_roots_le_of_injective P hinj
  have hfil : ((P.roots.map (algebraMap ℝ ℂ)).filter (fun z => z ∉ posRay))
      = (P.roots.filter (fun x => x ∉ Set.Ioi (0 : ℝ))).map (algebraMap ℝ ℂ) := by
    rw [Multiset.filter_map]
    exact congrArg _ (Multiset.filter_congr (fun x _ => by
      simp only [Function.comp_apply, algebraMap_mem_posRay_iff]))
  calc (exceptionalRoots P (Set.Ioi (0 : ℝ))).card
      = ((P.roots.filter (fun x => x ∉ Set.Ioi (0 : ℝ))).map (algebraMap ℝ ℂ)).card := by
        rw [Multiset.card_map]; rfl
    _ = ((P.roots.map (algebraMap ℝ ℂ)).filter (fun z => z ∉ posRay)).card := by rw [hfil]
    _ ≤ ((P.map (algebraMap ℝ ℂ)).roots.filter (fun z => z ∉ posRay)).card :=
        Multiset.card_le_card (Multiset.filter_le_filter _ hle)
    _ = (exceptionalRoots (P.map (algebraMap ℝ ℂ)) posRay).card := rfl

/-! ### The witness over an admissible pencil

`exceptional_unbounded_of_denomConv` leaves the denominator a free variable.  The
paper's denominator is the pencil `Q(t) + z t^r` of `eq:Q-hypotheses`, whose
convolution diagonal is `d_0 = C(Q(0))`; that is a unit in `ℝ[z]` exactly when
`Q(0) ≠ 0`, which is the hypothesis the paper already carries. -/

/-- Paper `sec:reduction` (supporting) — the convolution diagonal of the
admissible pencil is a unit.  `d_0 = C(Q(0))` by `ftDenom_zero`, and a constant
polynomial is a unit exactly when the constant is nonzero. -/
theorem isUnit_ftDenom_zero {𝕜 : Type*} [Field 𝕜] {Q : Polynomial 𝕜} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) : IsUnit (ftDenom Q r 0) := by
  rw [ftDenom_zero Q hr]
  exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hQ0)

/-- Paper `sec:introduction` (supporting) — the index-`0` coefficient of a
sequence driven by a nonzero constant numerator is nonzero.  The `m = 0`
equation of the convolution system reads `d_0 P_0 = R`, so `P_0 = 0` would force
`R = 0`.  This is what makes the necessity statement non-vacuous: its conclusion
is guarded by `P_m ≠ 0`, and without a witness index the guard could be empty. -/
theorem ne_zero_of_denomConv_const {A : Type*} [CommRing A] {d : ℕ → A} {R : A} (hR : R ≠ 0)
    {P : ℕ → A} (hP : ∀ m, denomConv d P m = if m = 0 then R else 0) : P 0 ≠ 0 := by
  intro h
  have h0 : d 0 * P 0 = R := by
    have hh := hP 0
    rw [denomConv_eq] at hh
    simpa using hh
  rw [h, mul_zero] at h0
  exact hR h0.symm

open scoped Classical in
/-- Paper `sec:introduction` — the count carried by the witness, over any
denominator with unit diagonal.  Extracted from
`exceptional_unbounded_of_denomConv` so that the pencil and the negation can
consume it at a fixed `R`. -/
theorem le_card_exceptionalRoots_negRootPoly {d : ℕ → Polynomial ℝ} (hd : IsUnit (d 0)) (L : ℕ)
    {P : ℕ → Polynomial ℝ} (hP : ∀ m, denomConv d P m = if m = 0 then negRootPoly L else 0)
    {m : ℕ} (hm : P m ≠ 0) :
    L ≤ (exceptionalRoots (P m) (Set.Ioi (0 : ℝ))).card := by
  have key := le_card_roots_filter (S := (Set.Ioi (0 : ℝ))ᶜ) (negRootPoly_ne_zero L)
    (fun x hx => negRootSet_root L hx) (fun x hx => negRootSet_notMem_posReals L hx)
  rw [negRootSet_card] at key
  have htrans := dvd_exceptional_le hm (dvd_of_denomConv_const hd _ hP m)
    ((Set.Ioi (0 : ℝ))ᶜ)
  simpa [exceptionalRoots] using key.trans htrans

open scoped Classical in
/-- **`sec:introduction`, the witness over the paper's own pencil.**  For an
admissible denominator `Q(t) + z t^r` — `r ≥ 1` and `Q(0) ≠ 0` — and every `L`
there is a numerator `N(t,z) = R(z)`, proper in `t`, whose coefficient sequence
exists, is nonzero at `m = 0`, and carries at least `L` zeros off the positive
ray at every index where it does not vanish.  Both counts are given: the real
one, and the complex one that `main_bound` bounds. -/
theorem exceptional_unbounded_ftDenom (Q : Polynomial ℝ) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (L : ℕ) :
    ∃ R : Polynomial ℝ, R ≠ 0 ∧ ∃ P : ℕ → Polynomial ℝ,
      (∀ m, denomConv (ftDenom Q r) P m = if m = 0 then R else 0) ∧ P 0 ≠ 0 ∧
      ∀ m, P m ≠ 0 →
        L ≤ (exceptionalRoots (P m) (Set.Ioi (0 : ℝ))).card ∧
        L ≤ (exceptionalRoots ((P m).map (algebraMap ℝ ℂ)) posRay).card := by
  have hd : IsUnit (ftDenom Q r 0) := isUnit_ftDenom_zero hr hQ0
  obtain ⟨P, hP⟩ := exists_denomConv_eq hd (fun m => if m = 0 then negRootPoly L else 0)
  refine ⟨negRootPoly L, negRootPoly_ne_zero L, P, hP,
    ne_zero_of_denomConv_const (negRootPoly_ne_zero L) hP, fun m hm => ?_⟩
  have hreal := le_card_exceptionalRoots_negRootPoly hd L hP hm
  exact ⟨hreal, hreal.trans (card_exceptionalRoots_le_map (P m))⟩

/-! ### The negation

`thm:main` gives, for each numerator, a constant `C` bounding the exceptional
zeros of every `P_m`.  The paper's `sec:introduction` claim is that no `C` serves
every numerator at once.  The numerator is presented as its coefficient sequence
`N_m` — `prop:initial-data`'s reading — and properness `deg_t N < max{deg Q, r}`
is the hypothesis `N_m = 0` for `m ≥ max{deg Q, r}`, so the statement quantifies
over exactly the numerators `thm:main` admits.  The witness `N(t,z) = R(z)` is
supported at `m = 0` alone, hence proper for every admissible pencil. -/

open scoped Classical in
/-- **`sec:introduction`, the necessity statement.**  For an admissible pencil
there is no constant bounding the real zeros off `(0,∞)` of the coefficient
polynomials uniformly over proper numerators.  Given a candidate `C`, the
numerator `R = negRootPoly (C+1)` refutes it already at `m = 0`. -/
theorem not_exists_uniform_exceptional_bound (Q : Polynomial ℝ) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) :
    ¬ ∃ C : ℕ, ∀ N P : ℕ → Polynomial ℝ,
        (∀ m, max Q.natDegree r ≤ m → N m = 0) →
        (∀ m, denomConv (ftDenom Q r) P m = N m) →
        ∀ m, P m ≠ 0 → (exceptionalRoots (P m) (Set.Ioi (0 : ℝ))).card ≤ C := by
  rintro ⟨C, hC⟩
  have hd : IsUnit (ftDenom Q r 0) := isUnit_ftDenom_zero hr hQ0
  set N : ℕ → Polynomial ℝ := fun m => if m = 0 then negRootPoly (C + 1) else 0 with hN
  obtain ⟨P, hP⟩ := exists_denomConv_eq hd N
  have hP0 : P 0 ≠ 0 := ne_zero_of_denomConv_const (negRootPoly_ne_zero (C + 1)) hP
  have hproper : ∀ m, max Q.natDegree r ≤ m → N m = 0 := by
    intro m hm
    have hmax : r ≤ max Q.natDegree r := le_max_right _ _
    have hm0 : m ≠ 0 := by omega
    simp [hN, hm0]
  have hle := hC N P hproper hP 0 hP0
  have hge := le_card_exceptionalRoots_negRootPoly hd (C + 1) hP hP0
  omega

open scoped Classical in
/-- **`sec:introduction`, the necessity statement in the count `thm:main`
bounds.**  The complex form of `not_exists_uniform_exceptional_bound`: no
constant bounds `(exceptionalRoots (P_m) posRay).card` uniformly over proper
numerators of an admissible pencil.  This is the negation of the
uniform-in-numerator reading of `main_bound`, and the passage from the real count
is `card_exceptionalRoots_le_map`. -/
theorem not_exists_uniform_exceptional_bound_complex (Q : Polynomial ℝ) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) :
    ¬ ∃ C : ℕ, ∀ N P : ℕ → Polynomial ℝ,
        (∀ m, max Q.natDegree r ≤ m → N m = 0) →
        (∀ m, denomConv (ftDenom Q r) P m = N m) →
        ∀ m, P m ≠ 0 →
          (exceptionalRoots ((P m).map (algebraMap ℝ ℂ)) posRay).card ≤ C := by
  rintro ⟨C, hC⟩
  refine not_exists_uniform_exceptional_bound Q hr hQ0 ⟨C, fun N P hprop hrec m hm => ?_⟩
  exact (card_exceptionalRoots_le_map (P m)).trans (hC N P hprop hrec m hm)

/-! ### The negation is not vacuous

A negation is only as good as the reachability of its hypotheses, so the pencil
is exhibited concretely: `Q(t) = 1 - t` and `r = 1`, which is the case
`prop:linear-case` solves in closed form as
`P_m(z) = (-1)^m R(z)(z-1)^m / q_0^{m+1}`.  It satisfies `eq:Q-hypotheses` — the
single zero `x_1 = 1` is positive — so the instance is admissible and not merely
well-typed. -/

open scoped Classical in
/-- **The necessity statement at the paper's linear pencil.**  `Q(t) = 1 + t`
and `r = 1`, so the denominator is `1 + (z-1)t` and the hypotheses of
`not_exists_uniform_exceptional_bound` hold with nothing assumed.  This is the
smallest admissible instance, and it certifies that the negation is about a
nonempty class of denominators. -/
theorem not_exists_uniform_exceptional_bound_linear :
    ¬ ∃ K : ℕ, ∀ N P : ℕ → Polynomial ℝ,
        (∀ m, max (1 - X : Polynomial ℝ).natDegree 1 ≤ m → N m = 0) →
        (∀ m, denomConv (ftDenom (1 - X : Polynomial ℝ) 1) P m = N m) →
        ∀ m, P m ≠ 0 → (exceptionalRoots (P m) (Set.Ioi (0 : ℝ))).card ≤ K :=
  not_exists_uniform_exceptional_bound (1 - X : Polynomial ℝ) le_rfl (by simp)

end ForgacsTran
