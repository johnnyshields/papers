/-
# Analytic bridge — Forgács–Tran geometry, weighted dominance, eventual degree

The proven core (`ZeroCount.exceptionalRoots_card_le`) turns a supply of
guaranteed interior zeros into an exceptional-zero bound.  The *supply* itself is
the analytic content of `../shields-2026-forgacs-tran-numerators.tex`, §§2–4, and
sits well outside current Mathlib.

Rather than positing that content with global `axiom`s — where a jointly
inconsistent set would silently make every downstream statement provable — it is
collected as the fields of a single **`structure FTInputs`** and passed to `Main`
as an explicit hypothesis.  `#print axioms main_bound` then reports only Lean's
`propext`/`Classical.choice`/`Quot.sound`; the analytic dependence lives in the
theorem's type, not in the ambient axiom set.  `ftInputsWitness` exhibits a model,
so the fields are provably consistent (not vacuously contradictory).

The objects and facts bundled are:

1. **Reduction and eventual degree** — §2 «Laurent reduction and eventual
   degree» (`sec:reduction`, `lem:laurent-reduction`, `lem:eventual-degree`,
   `rem:degree-shift`).  After the Laurent–Gauss division the coefficient
   polynomial `P_m` (here `coeffPoly m`, promoted to `ℂ[X]` so its zeros live in
   `ℂ`) reduces to `[t^M] B/(Q+zt^r)` with `deg P_m = ⌊m/r⌋ + O(1)`.

2. **Forgács–Tran pole geometry** — §3 «Pole geometry and the weighted principal
   amplitude»
   (`sec:geometry`, `thm:FT-geometry`).  The interval `I_{Q,r} = (a,b) ⊆ (0,∞)`
   and the real-analytic principal conjugate pair `t_±(θ) = τ(θ)e^{±iθ}` of
   `Forgacs2017`.  Recorded as a single set `ftSet ⊆ posRay` rather than a pair of
   real endpoints, because `eq:ab-def` gives `b = +∞` *precisely* when `r > 1`,
   which no `ftB : ℝ` can express, and `a = 0` exactly when the smallest zero of
   `Q` is repeated (`ρ ≥ 2`), which `0 < ftA` would have excluded.  Build it with
   `ftInterval a b` (finite `b`) or `ftRay a` (`r > 1`).

3. **Weighted principal-pair dominance and the phase count** — §4 «Weighted
   principal-pair dominance» (`sec:dominance`, `thm:weighted-dominance`) feeding the
   argument-principle count of §5 (`prop:univariate-main`).  This produces, for
   all large `m`, a set `interiorZeros m` of `≥ ⌊m/r⌋ - C` distinct genuine zeros
   of `P_m` inside `I_{Q,r}`.

**Missing Mathlib machinery.**  Mathlib has none of: the real-analytic implicit
description of the minimum-modulus branch and its endpoint expansions; the
contour/residue estimates of `lem:cluster-safe` and `lem:degree-drop`; or the
bounded-phase-variation argument-principle count.  These are the analysis of a
one-parameter family of complex polynomial roots (Rouché, the argument
principle, log-derivative estimates).  Discharging the geometry/dominance fields
means building that theory; the reduction field additionally needs coefficient
asymptotics of a rational generating function.

Nothing in the proven core (`ZeroCount`, `Reduction`, `LinearCase`, `Necessity`)
refers to `FTInputs`; `#print axioms` on those results shows only Lean/Mathlib's
`[propext, Classical.choice, Quot.sound]`.
-/
import ForgacsTran.ZeroCount
import ForgacsTran.Reduction

open Polynomial

namespace ForgacsTran

/-- **Analytic inputs of `thm:main`** (paper §§2–5), bundled as hypotheses so the
theorem's dependence on the §§2–4 analysis is explicit in its type rather than
posited as global axioms.  A term of this structure is exactly the analytic
supply that the exceptional-zero engine of `ZeroCount` consumes. -/
structure FTInputs where
  /-- **§2, `lem:laurent-reduction`.**  The paper's coefficient polynomials
  `P_m ∈ ℝ[z]`, promoted to `ℂ[X]`; their zeros in `ℂ` are the object of
  `thm:main`.  Obtained from the rational generating function `N/(Q+zt^r)`,
  whose coefficient extraction Mathlib does not provide. -/
  coeffPoly : ℕ → Polynomial ℂ
  /-- **§3, `thm:FT-geometry`, `eq:ab-def`.**  The Forgács–Tran interval
  `I_{Q,r}`, as a subset of `ℂ`.  Carried as a *set* rather than a pair of real
  endpoints because `eq:ab-def` puts `b = +∞` precisely when `r > 1`, which a
  real right endpoint cannot express; `ftInterval a b` builds the finite case and
  `ftRay a` the `r > 1` case, and `a = 0` (which happens exactly when the smallest
  zero of `Q` is repeated) is admissible in both. -/
  ftSet : Set ℂ
  /-- **§3, `thm:FT-geometry`.**  `I_{Q,r} ⊆ (0,∞)`.  Supplied by
  `ftInterval_subset_posRay` or `ftRay_subset_posRay`, each of which needs only
  `0 ≤ a`. -/
  ftSet_subset : ftSet ⊆ posRay
  /-- **§4–§5, `thm:weighted-dominance` + `prop:univariate-main`.**  The distinct
  positive zeros of `P_m` inside `I_{Q,r}` produced by the phase count. -/
  interiorZeros : ℕ → Finset ℂ
  /-- **§5, `prop:univariate-main`.**  The bulk-defect constant `C = C(Q,r,N)`. -/
  Cbulk : ℕ
  /-- Each member of `interiorZeros m` is a genuine zero of `P_m`. -/
  interiorZeros_root : ∀ m, ∀ z ∈ interiorZeros m, (coeffPoly m).IsRoot z
  /-- Each member of `interiorZeros m` lies in the Forgács–Tran interval. -/
  interiorZeros_mem : ∀ m, ∀ z ∈ interiorZeros m, z ∈ ftSet
  /-- **§4–§5, the phase count** (`prop:univariate-main`,
  `eq:positive-zero-lower-bound`) with the **§2 eventual degree**
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
from the §2 defining recurrence for `coeffPoly` (`lem:laurent-reduction`) together
with the §4–§5 phase count, *deriving* the degree-laden `bulk_zero_count` field
from the proven eventual-degree upper bound `eventual_natDegree_le` (§2
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
the passage `P_m = F_{m+rE-μ}` of `lem:laurent-reduction`/`rem:degree-shift` is
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

end ForgacsTran
