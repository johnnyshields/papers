# Lean 4 formalization — Bounded exceptional zeros in the Forgács–Tran family

Formalizes the core of `../shields-2026-forgacs-tran-numerators.tex` against
Mathlib (`leanprover/lean4:v4.33.0-rc1`, namespace `ForgacsTran`).  `lake build`
is green.  The elementary and combinatorial content of the paper is proven with
**no `sorry` and no project-specific `axiom`**; the analytic inputs (Forgács–Tran
pole geometry, weighted dominance, the argument-principle phase count) — none of
which Mathlib yet supports — are not posited as global axioms but carried as the
fields of a single hypothesis structure `FTInputs`, so `#print axioms` on *every*
result, the main theorem included, reports only Lean/Mathlib's three standard
axioms.

## Build

```
lake exe cache get   # fetch the pinned Mathlib build cache (once)
lake build
```

## What is proven (unconditionally)

The following are proven with no `sorry` and no project-specific axioms;
`#print axioms` reports only Lean/Mathlib's `[propext, Classical.choice,
Quot.sound]`.

| Result | Paper | Lean |
|---|---|---|
| Exceptional-zero counting engine (many interior zeros ⟹ few exterior) | `prop:univariate-main` (mechanism) | `ZeroCount.exceptionalRoots_card_le` |
| Interior roots embed into the root multiset | `prop:univariate-main` (step) | `ZeroCount.le_card_roots_filter` |
| `I_{Q,r} ⊆ (0,∞)`, finite `b` | `sec:geometry`, `eq:ab-def` | `ZeroCount.ftInterval_subset_posRay` |
| `I_{Q,r} = (a,∞) ⊆ (0,∞)`, the `r > 1` case | `sec:geometry`, `eq:ab-def` | `ZeroCount.ftRay_subset_posRay` |
| Numerator = initial data (uniqueness) | `prop:initial-data` | `Reduction.initial_data_unique` |
| Eventual degree (upper bound) `deg_z P_m ≤ ⌊m/r⌋` | `lem:eventual-degree` | `Reduction.eventual_natDegree_le` |
| Linear case closed form / recurrence | `prop:linear-case` | `LinearCase.Plin_recurrence` |
| Linear case: the recurrence **determines** the sequence (so the closed form *is* the coefficient sequence) | `prop:linear-case` | `LinearCase.Plin_unique`, `denomConv_dlin_Plin` |
| Linear case: exceptional zeros are `R`'s, `m`-uniformly | `prop:linear-case` | `LinearCase.Plin_exceptional_eq`, `Plin_exceptional_card_le` |
| Witness family with `L` roots off `(0,∞)`, `L` arbitrary — **an ingredient of** `prop:N-dependence`, not the proposition | `prop:N-dependence` | `Necessity.exceptional_unbounded` |
| Root counts inherited by any multiple `R ∣ P` — the second ingredient | `prop:N-dependence` | `Necessity.dvd_exceptional_le` |

`eventual_natDegree_le` is stated over an arbitrary field: the paper uses `ℝ` in
§2, and the bridge instantiates it at `ℂ` (see below).

The **main theorem** is proven from the analytic-input hypothesis bundle
`FTInputs`: the counting engine, the absorption of the finitely many initial
indices, and the reduction of the degree bound to the phase count are all genuine;
only the analytic *supply* of interior zeros lives in the hypothesis.

| Result | Paper | Lean |
|---|---|---|
| `≤ C` zeros off `(0,∞)`, all `m` | `thm:main` (first clause) | `Main.main_bound` |
| `≤ C` zeros off `I_{Q,r}`, large `m` | `thm:main` (second clause) | `Main.main_bound_interval` |
| off-ray bound from recurrence + phase count | `thm:main` (first clause) | `Main.main_bound_ofRecurrence` |
| `≥ deg P_m - C` **distinct** zeros inside `I_{Q,r}`, large `m` | abstract, `Corollary 6.2` | `Main.interior_distinct_count` (restates a hypothesis — see below) |

## Module map

Paper sections (of `../shields-2026-forgacs-tran-numerators.tex`): 1
`sec:introduction`, 2 `sec:reduction`, 3 `sec:geometry`, 4 `sec:dominance`, 5
`sec:proof`, 6 `sec:consequences`, 7 `sec:questions`.  Each module header names
the section(s) it formalizes.

```
ZeroCount    — §5,§3    exceptional-zero engine; posRay / ftInterval / ftRay geometry
Reduction    — §2       prop:initial-data uniqueness; eventual-degree upper bound
LinearCase   — §5,§2    prop:linear-case: closed form over ℂ, m-uniform count,
                        and its identification via Reduction.initial_data_unique
Necessity    — §6       two ingredients of prop:N-dependence (NOT the proposition)
Bridge       — §2,§3,§4 analytic inputs as the FTInputs hypothesis structure
Main         — §1,§5    thm:main from the engine + the bridge
AxiomCheck   —          regression guards; #print axioms footprints
```

The engine (`ZeroCount`) is stated over an arbitrary integral domain, so it
applies both to the real coefficient polynomials (`Necessity`) and to their
complex zero sets (`LinearCase`, `Main`).

---

# The analytic bridge — `FTInputs`

The proven core (`ZeroCount.exceptionalRoots_card_le`) turns a supply of
guaranteed interior zeros into an exceptional-zero bound.  The *supply* itself is
the analytic content of §§2–4 and sits well outside current Mathlib.

Rather than positing that content with global `axiom`s — where a jointly
inconsistent set would silently make every downstream statement provable — it is
collected as the fields of a single **`structure FTInputs`** (`Bridge.lean`) and
passed to `Main` as an explicit hypothesis.  Consequently `#print axioms
main_bound` reports only `[propext, Classical.choice, Quot.sound]`: the analytic
dependence lives in the theorem's *type*, not in the ambient axiom set.
`ftInputsWitness` exhibits a concrete model, so `ftInputs_nonempty` certifies the
fields are jointly satisfiable and `main_bound` is not vacuously conditional on a
contradictory bundle.

## Fields of `FTInputs`

| Field(s) | Paper | Content |
|---|---|---|
| `coeffPoly` | §2 `lem:laurent-reduction` | the coefficient polynomials `P_m ∈ ℝ[z]`, promoted to `ℂ[X]`; their `ℂ`-zeros are the object of `thm:main` |
| `ftSet`, `ftSet_subset` | §3 `thm:FT-geometry`, `eq:ab-def` | `I_{Q,r}` as a *set* with `ftSet ⊆ posRay`.  Carried as a set, not a pair of real endpoints: `eq:ab-def` puts `b = +∞` precisely when `r > 1`, which no `ftB : ℝ` can express, and `a = 0` exactly when the smallest zero of `Q` is repeated, which `0 < ftA` would have excluded.  Build with `ftInterval a b` or `ftRay a`; both inclusions need only `0 ≤ a` |
| `interiorZeros`, `interiorZeros_root`, `interiorZeros_mem` | §4–§5 `thm:weighted-dominance`, `prop:univariate-main` | the distinct genuine zeros of `P_m` inside `I_{Q,r}` produced by the phase count |
| `Cbulk` | §5 `prop:univariate-main` | the bulk-defect constant `C = C(Q,r,N)` |
| `bulk_zero_count` | §2 + §4–§5 | for large `m`, `deg P_m - C ≤ #interiorZeros` |

**Missing Mathlib machinery.**  Mathlib has none of: the real-analytic implicit
description of the minimum-modulus branch `t_±(θ)` of `Forgacs2017` and its
endpoint expansions; the contour/residue estimates of `lem:cluster-safe` and
`lem:degree-drop`; or the bounded-phase-variation argument-principle count.  These
are the analysis of a one-parameter family of complex polynomial roots (Rouché,
the argument principle, log-derivative estimates).  Discharging the
geometry/dominance fields means building that theory; `coeffPoly` additionally
needs the coefficient-extraction apparatus of a rational generating function.

## The degree bound is derived, not assumed

The `bulk_zero_count` field bundles two facts: the eventual-degree bound
`deg P_m ≤ ⌊m/r⌋` (§2 `lem:eventual-degree`, upper half) and the phase count
`⌊m/r⌋ - C ≤ #interiorZeros` (§4–§5).  The first is **not** analytic — it is a
purely algebraic consequence of the §2 recurrence, and it is proven in
`Reduction.eventual_natDegree_le`.

`Bridge.FTInputs.ofRecurrence` uses this: it assembles an `FTInputs` from the §2
defining recurrence `∑_i d_i F_{m-i} = C(b_m)` (`d_i = C(Q.coeff i) + [i=r]·X` over
`ℂ`) together with the genuinely analytic phase count alone, and *derives*
`bulk_zero_count` by combining `eventual_natDegree_le` with the count.  So the
degree half of `lem:eventual-degree` is not an independent hypothesis of
`thm:main`.  `Main.main_bound_ofRecurrence` states the off-ray bound directly over
these strictly weaker inputs.

## What the proven core supplies

Given the interior-zero supply, `ZeroCount.exceptionalRoots_card_le` converts
"`≥ deg P_m - C` interior zeros" into "`≤ C` exceptional zeros", and `Main`
absorbs the finitely many small `m` by the maximum degree over `range m0`.  That
conversion — the logical crux that makes the bound *uniform in `m`* — is
machine-checked, as is the reduction of the degree bound to the phase count.

## What remains — the honest scope of this development

`lake build` is green with no `sorry` and no project axiom, and that is a claim
about *axiom hygiene*, not about coverage.  This section records what the
development does **not** establish, so the green build cannot be misread.

### 1. `main_bound` and `main_bound_interval` are conditional, and the condition carries the analysis

All three `Main` theorems take `FTInputs` (or, for `ofRecurrence`, the recurrence
plus `phase_count`) as an explicit hypothesis.  What is machine-checked is the
*bookkeeping* of `thm:main`: the conversion of an interior-zero supply into an
exceptional-zero bound uniform in `m`, the absorption of small `m`, and the
derivation of the degree half from the §2 recurrence.  The analytic substance —
§3 pole geometry, §4 dominance, the §5 phase count — is assumed.  So these are
formalizations of `thm:main` **conditional on §§3–5**, not unconditional proofs of
it.

### 2. `Necessity` does not prove `prop:N-dependence`

It proves two mechanical ingredients: a witness family with arbitrarily many
off-ray roots (`exceptional_unbounded`) and root-count inheritance under
divisibility (`dvd_exceptional_le`).  Four links to the proposition are missing:
quantification over the denominator; the hypothesis `R ∣ P_m` that
`dvd_exceptional_le` consumes and nothing supplies; the passage from these
`ℝ`-side `roots.filter` counts to the `ℂ`-side `exceptionalRoots … posRay` that
`main_bound` bounds; and the negation `¬ ∃ C, ∀ N, …` itself.
`rem:optimality-of-bounded-defect` is not formalized at all.  The module docstring
states this.

### 3. `interior_distinct_count` restates a hypothesis

`FTInputs.interiorZeros m` is a `Finset ℂ`, so its members are already
pairwise-distinct, and `bulk_zero_count` already asserts the cardinality bound.
The corollary exists so the Lean statement mirrors the shape of the paper's
distinct-zero claim; it derives no new content.

### 4. `thm:main` clause 2 is formalized in one of its three parts

Clause 2 asserts, for all large `m`: (i) `P_m ≠ 0`; (ii) at most `C` zeros outside
`I_{Q,r}` with multiplicity; (iii) at least `deg P_m - C` distinct zeros inside.
Only (ii) is proven — `main_bound_interval`.  Part (iii) is `interior_distinct_count`,
i.e. assumed (see 3).  Part (i) appears as the hypothesis `coeffPoly m ≠ 0` on all
three theorems and rests on the **lower** half of `lem:eventual-degree`
(`deg F_M = ⌊M/r⌋`, not merely `≤`), which `eventual_natDegree_le` does not
provide.  That lower half — the paper's attainment argument via the leading
coefficient `B(0)λ^s/s! ≠ 0` — is the one place the paper concludes what this
development assumes.

### 5. The `P_m ↦ F_{m+rE-μ}` reduction is not formalized

`ofRecurrence` posits a recurrence with constant right-hand side `C (b m)`, which
is the recurrence of the **reduced** sequence `F_M` of `eq:F-M-def`.  For a general
bivariate `N`, `prop:initial-data` gives right-hand side `N_m(z)`, a polynomial in
`z`.  The Laurent–Gauss reduction `lem:laurent-reduction` and the index shift
`rem:degree-shift` that connect the two are absent, so `coeffPoly` is effectively
being identified with `F_M`.  `eq:P-linear-combination` (2.4) and the
denominator-only sequence `H_m` are likewise unformalized.

### 6. `ftInputsWitness` certifies non-vacuity only

It exhibits `P_m = 1`, no interior zeros, `Cbulk = 0` on `ftInterval 1 2`.  That
establishes `FTInputs` is inhabited, so the theorems are not vacuously conditional
on an empty hypothesis type.  It does **not** exhibit a non-degenerate model (every
`natDegree` is `0`, so the degree/count interaction is never exercised), and it is
not the paper's data — the structure mentions no `Q`, `r`, or `N`, so it certifies
nothing about consistency of the §§2–4 analytic claims themselves.

### 7. Not attempted

`prop:equidistribution` and `eq:portmanteau-lower` (§6), the §3 geometry and §4
dominance as *theorems* rather than hypotheses, and the §7 open questions.

## Out of scope

- The **asymptotic-concentration corollary** (`sec:consequences`,
  `#{x ∈ I_{Q,r} : P_m(x)=0}/deg P_m → 1`) follows from `bulk_zero_count` once
  `deg P_m → ∞`; the limit is a routine consequence not formalized here.
- The **further questions** of §7 are open problems, not results.

## Verification

`AxiomCheck.lean` pins the axiom footprint of every headline result with
`#guard_msgs in #print axioms …`: `exceptionalRoots_card_le`,
`le_card_roots_filter`, `ftInterval_subset_posRay`, `ftRay_subset_posRay`,
`initial_data_unique`, `eventual_natDegree_le`, `Plin_recurrence`,
`Plin_exceptional_eq`, `Plin_exceptional_card_le`, `Plin_ne_zero`,
`denomConv_dlin_Plin`, `Plin_unique`, `exceptional_unbounded`,
`dvd_exceptional_le`, `ftInputsWitness`, `ftInputs_nonempty`,
`FTInputs.ofRecurrence`, `main_bound`, `main_bound_interval`,
`main_bound_ofRecurrence`, and `interior_distinct_count` all report exactly
`[propext, Classical.choice, Quot.sound]`.  If a `sorry` or a stray `axiom` ever
enters a dependency the reported footprint changes and `#guard_msgs` turns the
mismatch into a `lake build` error.
