/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ZeroCount
import ForgacsTran.Reduction
import ForgacsTran.SignAlternation
import ForgacsTran.LaurentReduction

/-!
# Analytic bridge — Forgács–Tran geometry, weighted dominance, eventual degree

Rather than positing that content with global `axiom`s — where a jointly
inconsistent set would silently make every downstream statement provable — it is
collected as the fields of a single **`structure FTInputs`** and passed to `Main`
as an explicit hypothesis.  `#print axioms main_bound` then reports only Lean's
`propext`/`Classical.choice`/`Quot.sound`; the analytic dependence lives in the
theorem's type, not in the ambient axiom set.  `ftInputsWitness` exhibits a model,
so the fields are provably consistent (not vacuously contradictory).

The objects and facts bundled are:

1. **Reduction and eventual degree** — «Canonical Laurent reduction and
   eventual degree» (`sec:reduction`, `lem:laurent-reduction`, `lem:eventual-degree`,
   `eq:exact-eventual-degree-shift`).  After the Laurent–Gauss division the coefficient
   polynomial `P_m` (here `coeffPoly m`, promoted to `ℂ[X]` so its zeros live in
   `ℂ`) reduces to `[t^M] B/(Q+zt^r)` with `deg P_m = ⌊m/r⌋ + O(1)`.

2. **Forgács–Tran pole geometry** — «Spectral geometry, residues, and the
   principal amplitude»
   (`sec:geometry`, `thm:FT-geometry`).  The interval `I_{Q,r} = (a,b) ⊆ (0,∞)`
   and the real-analytic principal conjugate pair `t_±(θ) = τ(θ)e^{±iθ}` of
   `Forgacs2017RationalDenominator`.  Recorded as a single set `ftSet ⊆ posRay` rather than a pair
   of
   real endpoints, because `eq:ab-def` gives `b = +∞` *precisely* when `r > 1`,
   which no `ftB : ℝ` can express, and `a = 0` exactly when the smallest zero of
   `Q` is repeated (`ρ ≥ 2`), which `0 < ftA` would have excluded.  Build it with
   `ftInterval a b` (finite `b`) or `ftRay a` (`r > 1`).

3. **Weighted principal-pair dominance and the phase count** — `subsec:weighted-dominance` «Weighted
   principal-pair dominance» (`sec:dominance`, `thm:weighted-dominance`) feeding the
   phase count of `subsec:proof` (`prop:angular-discrepancy`).  This produces, for
   all large `m`, a set `interiorZeros m` of `≥ ⌊m/r⌋ - C` distinct genuine zeros
   of `P_m` inside `I_{Q,r}`.

**What is still assumed, and why.**  Mathlib has neither the real-analytic
implicit description of the minimum-modulus branch and its endpoint expansions
nor the contour/residue estimates of `lem:contour-separation`;
those are the analysis of a one-parameter family of complex polynomial roots,
and the paper takes the geometry itself from `Forgacs2017RationalDenominator`
rather than proving it.  The reduction field additionally needs coefficient
asymptotics of a rational generating function.

The `subsec:proof` count is *not* among the gaps.  It is an intermediate-value argument, not
a contour count: at a phase point the principal term of
`eq:principal-decomposition` is `2(-1)^k|W|` and `eq:dominance-bound` forces
`F_M` to carry that sign, so consecutive phase points enclose a zero.  That step
is formalized in `SignAlternation`, and `FTInputs.ofSignAlternation` below uses
it to *derive* `interiorZeros` and `bulk_zero_count` from the sign pattern
alone — leaving the phase points and their alternation as the hypothesis, which
is what `thm:weighted-dominance` supplies.

Nothing in the proven core (`ZeroCount`, `Reduction`, `LinearCase`, `Necessity`)
refers to `FTInputs`; `#print axioms` on those results shows only Lean/Mathlib's
`[propext, Classical.choice, Quot.sound]`.

## References

The proven core (`ZeroCount.exceptionalRoots_card_le`) turns a supply of
guaranteed interior zeros into an exceptional-zero bound.  The *supply* itself is
the analytic content of `../shields-2026-forgacs-tran-numerators.tex`,
`sec:reduction`--`sec:dominance`, and
sits well outside current Mathlib.

## Tags

hypothesis bundle, weighted dominance, eventual degree, Forgacs-Tran geometry
-/

open Polynomial

namespace ForgacsTran

/-- **Analytic inputs of `thm:main`** (paper `sec:reduction`--`sec:dominance`), bundled as
hypotheses so the theorem's dependence on the `sec:reduction`--`sec:dominance` analysis is
explicit in its type rather than posited as global axioms.  A term of this structure is exactly
the analytic supply that the exceptional-zero engine of `ZeroCount` consumes. -/
structure FTInputs where
  /-- **`sec:reduction`, `lem:laurent-reduction`.**  The paper's coefficient polynomials
  `P_m ∈ ℝ[z]`, promoted to `ℂ[X]`; their zeros in `ℂ` are the object of
  `thm:main`.  Obtained from the rational generating function `N/(Q+zt^r)`,
  whose coefficient extraction Mathlib does not provide. -/
  coeffPoly : ℕ → Polynomial ℂ
  /-- **`sec:geometry`, `thm:FT-geometry`, `eq:ab-def`.**  The Forgács–Tran interval
  `I_{Q,r}`, as a subset of `ℂ`.  Carried as a *set* rather than a pair of real
  endpoints because `eq:ab-def` puts `b = +∞` precisely when `r > 1`, which a
  real right endpoint cannot express; `ftInterval a b` builds the finite case and
  `ftRay a` the `r > 1` case, and `a = 0` (which happens exactly when the smallest
  zero of `Q` is repeated) is admissible in both. -/
  ftSet : Set ℂ
  /-- **`sec:geometry`, `thm:FT-geometry`.**  `I_{Q,r} ⊆ (0,∞)`.  Supplied by
  `ftInterval_subset_posRay` or `ftRay_subset_posRay`, each of which needs only
  `0 ≤ a`. -/
  ftSet_subset : ftSet ⊆ posRay
  /-- **`subsec:weighted-dominance`–`subsec:proof`, `thm:weighted-dominance` +
  `prop:angular-discrepancy`.**  The distinct positive zeros of `P_m` inside `I_{Q,r}` produced
  by the phase count. -/
  interiorZeros : ℕ → Finset ℂ
  /-- **`subsec:proof`, `prop:angular-discrepancy`.**  The bulk-defect constant `C = C(Q,r,N)`. -/
  Cbulk : ℕ
  /-- Each member of `interiorZeros m` is a genuine zero of `P_m`. -/
  interiorZeros_root : ∀ m, ∀ z ∈ interiorZeros m, (coeffPoly m).IsRoot z
  /-- Each member of `interiorZeros m` lies in the Forgács–Tran interval. -/
  interiorZeros_mem : ∀ m, ∀ z ∈ interiorZeros m, z ∈ ftSet
  /-- **`subsec:weighted-dominance`–`subsec:proof`, the phase count** (`prop:angular-discrepancy`,
  `eq:angular-distinct-lower`) with the **`sec:reduction` eventual degree**
  (`lem:eventual-degree`): for all large `m`, `P_m` has at least `deg P_m - C`
  distinct zeros in `I_{Q,r}`. -/
  bulk_zero_count :
      ∃ m0 : ℕ, ∀ m, m0 ≤ m → (coeffPoly m).natDegree - Cbulk ≤ (interiorZeros m).card

/-- **Consistency witness.**  A trivial model of `FTInputs`: the constant
numerator `P_m = 1`, no interior zeros, and `Cbulk = 0` on the interval `(1,2)`.
Every field is discharged, so the hypotheses of `FTInputs` are jointly
satisfiable; `main_bound` is therefore not vacuously conditional on a
contradictory bundle.  This is *not* the actual Forgács–Tran data — it only
certifies non-vacuousness. -/
noncomputable def ftInputsWitness : FTInputs where
  coeffPoly := fun _ => 1
  ftSet := ftInterval 1 2
  ftSet_subset := ftInterval_subset_posRay zero_le_one
  interiorZeros := fun _ => ∅
  Cbulk := 0
  interiorZeros_root := fun _ z hz => by simp at hz
  interiorZeros_mem := fun _ z hz => by simp at hz
  bulk_zero_count := ⟨0, fun _ _ => by simp⟩

/-- `FTInputs` is inhabited: the analytic bundle of `thm:main` is consistent. -/
theorem ftInputs_nonempty : Nonempty FTInputs := ⟨ftInputsWitness⟩

/-- **Leaner analytic inputs, degree bound derived.**  Assembles an `FTInputs`
from the `sec:reduction` defining recurrence for `coeffPoly` (`lem:laurent-reduction`) together
with the `subsec:weighted-dominance`–`subsec:proof` phase count, *deriving* the degree-laden
`bulk_zero_count` field
from the proven eventual-degree upper bound `eventual_natDegree_le` (`sec:reduction`
`lem:eventual-degree`) rather than assuming it.

The `deg P_m ≤ ⌊m/r⌋` half of `lem:eventual-degree` is therefore **not** an
independent hypothesis of `thm:main`: the constructor posits only the recurrence
`∑_i d_i F_{m-i} = C(b_m)` with `d_i = C(Q.coeff i) + [i=r]·X` over `ℂ`, and the
genuinely analytic phase count `⌊m/r⌋ - C ≤ #interior`, and machine-derives the
combined bound the engine consumes.

Note the constant right-hand side: `C (b m)` has `z`-degree `0`, so this is the
recurrence of the **reduced** sequence `F_M` of `eq:F-M-def` (equivalently of
`P_m` when the numerator is free of `z`).  For a general bivariate `N`,
`prop:initial-data` gives the right-hand side `N_m(z)`, a polynomial in `z`, and
the passage `P_m = F_{m+rE-μ}` of `lem:laurent-reduction`/`eq:exact-eventual-degree-shift` is
**not** formalized — so `coeffPoly` is being identified with `F_M` here. -/
noncomputable def FTInputs.ofRecurrence
    (coeffPoly : ℕ → ℂ[X]) (ftSet : Set ℂ) (ftSet_subset : ftSet ⊆ posRay)
    (interiorZeros : ℕ → Finset ℂ) (Cbulk : ℕ)
    (interiorZeros_root : ∀ m, ∀ z ∈ interiorZeros m, (coeffPoly m).IsRoot z)
    (interiorZeros_mem : ∀ m, ∀ z ∈ interiorZeros m, z ∈ ftSet)
    (Q : ℂ[X]) (r : ℕ) (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → ℂ)
    (hrec : ∀ M, denomConv (ftDenom Q r) coeffPoly M = C (b M))
    (phase_count : ∃ m0 : ℕ, ∀ m, m0 ≤ m → m / r - Cbulk ≤ (interiorZeros m).card) :
    FTInputs where
  coeffPoly := coeffPoly
  ftSet := ftSet
  ftSet_subset := ftSet_subset
  interiorZeros := interiorZeros
  Cbulk := Cbulk
  interiorZeros_root := interiorZeros_root
  interiorZeros_mem := interiorZeros_mem
  bulk_zero_count := by
    obtain ⟨m0, hm0⟩ := phase_count
    refine ⟨m0, fun m hm => ?_⟩
    have hdeg : (coeffPoly m).natDegree ≤ m / r :=
      eventual_natDegree_le Q hr hQ0 b coeffPoly hrec m
    exact le_trans (Nat.sub_le_sub_right hdeg Cbulk) (hm0 m hm)

/-- **Analytic inputs assembled from a general bivariate numerator.**  The
leanest constructor on the algebraic side: it takes the paper's own data — a
proper `N ∈ ℂ[z][t]`, the denominator recurrence for `P_m` with the polynomial
right-hand side `N_m(z)` that `prop:initial-data` gives, and the recurrence for
the reduced sequence — and derives `bulk_zero_count` from the phase count through
the canonical Laurent reduction.

`FTInputs.ofRecurrence` posits a recurrence whose right-hand side is the
*constant* `C (b m)`, which is the recurrence of the reduced sequence `F_M` of
`eq:F-M-def`; against it `coeffPoly` is effectively identified with `F_M`.  Here
the two sequences are distinct objects and `lem:laurent-reduction` connects them:
`reduction_coeff_eventually` gives `P_m = F_{m-λ_N}` eventually, and
`eventual_natDegree_le_shift` carries the degree bound across the shift
`eq:exact-eventual-degree-shift`.  So the reduction is consumed rather than
assumed away. -/
noncomputable def FTInputs.ofBivariateNumerator
    (coeffPoly reduced : ℕ → ℂ[X]) (ftSet : Set ℂ) (ftSet_subset : ftSet ⊆ posRay)
    (interiorZeros : ℕ → Finset ℂ) (Cbulk : ℕ)
    (interiorZeros_root : ∀ m, ∀ z ∈ interiorZeros m, (coeffPoly m).IsRoot z)
    (interiorZeros_mem : ∀ m, ∀ z ∈ interiorZeros m, z ∈ ftSet)
    (Q : ℂ[X]) (r : ℕ) (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0)
    (N : (ℂ[X])[X]) (hN : N ≠ 0)
    (hproper : ∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom Q r) coeffPoly m = (swapVars N).coeff m)
    (hF : ∀ M, denomConv (ftDenom Q r) reduced M
      = Polynomial.C ((laurentWeight Q r N).coeff M))
    (phase_count : ∃ m0 : ℕ, ∀ m, m0 ≤ m →
      (((m : ℤ) - laurentShift Q r N).toNat) / r - Cbulk ≤ (interiorZeros m).card) :
    FTInputs where
  coeffPoly := coeffPoly
  ftSet := ftSet
  ftSet_subset := ftSet_subset
  interiorZeros := interiorZeros
  Cbulk := Cbulk
  interiorZeros_root := interiorZeros_root
  interiorZeros_mem := interiorZeros_mem
  bulk_zero_count := by
    obtain ⟨m1, h1⟩ := phase_count
    obtain ⟨m2, h2⟩ :=
      eventual_natDegree_le_shift Q hr hQ0 hN hproper coeffPoly reduced hP hF
    refine ⟨max m1 m2, fun m hm => ?_⟩
    have hm1 : m1 ≤ m := le_trans (le_max_left _ _) hm
    have hm2 : m2 ≤ m := le_trans (le_max_right _ _) hm
    exact le_trans (Nat.sub_le_sub_right (h2 m hm2) Cbulk) (h1 m hm1)

/-- **Analytic inputs assembled from the `subsec:proof` sign pattern.**  Builds `FTInputs`
from what `thm:weighted-dominance` actually delivers — an alternation of sign of
the real coefficient polynomial at the phase points of `eq:Omega-M` — instead of
from  the zero set itself.

Four fields are *derived* rather than posited: `interiorZeros`,
`interiorZeros_root`, `interiorZeros_mem` and `bulk_zero_count` all come out of
the intermediate-value count `exists_interiorZeros_of_alternating`
(`prop:angular-discrepancy`).  What remains assumed is the sign alternation, which is
the paper's `eq:dominance-bound` evaluated at the phase points, together with the
count of gaps.

This is a strictly weaker hypothesis set than the plain constructor's: a supply
of `gaps m + 1` sign-alternating points is what the dominance theorem produces,
whereas `interiorZeros` is the conclusion drawn from it. -/
noncomputable def FTInputs.ofSignAlternation
    (Preal : ℕ → Polynomial ℝ) (a b : ℝ) (ha : 0 ≤ a) (Cbulk : ℕ)
    (gaps : ℕ → ℕ) (x : ∀ m, Fin (gaps m + 1) → ℝ)
    (hx : ∀ m, StrictMono (x m)) (hmem : ∀ m k, x m k ∈ Set.Ioo a b)
    (halt : ∀ m, ∀ k : Fin (gaps m),
      (Preal m).eval (x m k.castSucc) * (Preal m).eval (x m k.succ) < 0)
    (hcount : ∃ m0 : ℕ, ∀ m, m0 ≤ m →
      ((Preal m).map (algebraMap ℝ ℂ)).natDegree - Cbulk ≤ gaps m) :
    FTInputs := by
  choose Z hcard hroot hmemZ using fun m =>
    exists_interiorZeros_of_alternating (Preal m) Set.ordConnected_Ioo
      (x m) (hx m) (hmem m) (halt m)
  exact
    { coeffPoly := fun m => (Preal m).map (algebraMap ℝ ℂ)
      ftSet := ftInterval a b
      ftSet_subset := ftInterval_subset_posRay ha
      interiorZeros := Z
      Cbulk := Cbulk
      interiorZeros_root := hroot
      interiorZeros_mem := hmemZ
      bulk_zero_count := by
        obtain ⟨m0, hm0⟩ := hcount
        exact ⟨m0, fun m hm => le_trans (hm0 m hm) (hcard m)⟩ }

end ForgacsTran
