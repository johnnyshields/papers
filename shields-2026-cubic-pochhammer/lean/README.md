# Lean 4 formalization — Coefficientwise log-concavity of the cubic multiple-Pochhammer series

Formalizes the core of `../shields-2026-cubic-pochhammer.tex` against Mathlib
(`leanprover/lean4:v4.30.0-rc2`, namespace `CubicPochhammer`).  `lake build` is
green with **no `sorry`** and a small, fully localized set of three documented
bridge axioms, all listed below.

The paper proves Karp–Zhang Conjecture 3.8 (`KarpZhang2024`): for a nonnegative
log-concave sequence `(f_n)`, the cubic multiple-Pochhammer series
`F_f(μ;x) = Σ_{n≥1} f_n (μ)_{3n} x^n/(3n-1)!` is coefficientwise log-concave.

## Build

```
lake exe cache get   # fetch the pinned Mathlib build cache (once)
lake build
```

The project is self-contained: its own `lakefile.lean`, `lean-toolchain`, and
pinned `lake-manifest.json`.  (`.lake/` is a gitignored build directory.)

## What is proven (unconditionally, no project axioms)

The **combinatorial heart of the paper** — the third-root-of-unity positivity
certificate and the weighting principle — is proven with no `sorry` and no
project-specific axioms.  `#print axioms` reports only Lean/Mathlib's
`[propext, Classical.choice, Quot.sound]`:

| Result | Paper | Lean |
|---|---|---|
| One-sign-change weighting principle | `lem:weighting` | `Weighting.sum_weighted_nonneg`, `sum_weighted_pos_of_pivot_pos` |
| Residue-class sums, period-6 closed form `3R = 2^·+corr` | `eq:S-table` root-of-unity filter | `ResidueSums.three_R_closed` (`R_succ`, `corr_rec`) |
| Residue-class moments `∑k·C`, `∑k(k-1)·C` | `eq:S-R` | `ResidueSums.moment1_c2`, `moment_kk_c2` |
| Certificate closed form `3S_{n,j} = d·2^j + …` | `eq:S-table` | `Snj.three_Snj_dform` |
| Exponential bounds `2^j ≥ …` (equality at `j=6,7`) | `eq:exp-bound-0`, `eq:exp-bound-1` | `Snj.expb_quad0`, `expb_quad1`, `expb_a` |
| **Certificate nonnegativity `S_{n,j} ≥ 0`** | `lem:bernstein` (via `eq:S-table`) | **`Snj.Snj_nonneg`** |
| Strictly positive `[x²]` coefficient `S_{n,2}=3(n-1)` | `lem:bernstein` | `Bernstein.Snj_two_eq`, `Snj_two_pos` |

`S_{n,j} ≥ 0` for **all** `m` is the paper's main new positivity, proven here in
full: a single period-6 induction for the root-of-unity evaluation, then a
six-way case split with the two exponential bounds.  It is cross-checked in
`../scripts/verify_kernel.py` (symbolic) and `../scripts/check_kernel_stdlib.py`
(integer audit over a wide `m`-range).

## What is proven modulo the documented bridges

| Result | Paper | Lean | Uses |
|---|---|---|---|
| Bernstein certificate `J_m(t) > 0` on `(0,1)` | `lem:bernstein` | `Bernstein.Jm_pos` | `Jm_bernstein` |
| Weighted kernel `J_{m,w}(t) ≥ 0` (`G_{m,w}` monotone) | `thm:kernel` | `Kernel.Jmw_nonneg` | + `block_certificate` |
| **Cubic multiple-Pochhammer theorem** | `thm:main` | **`Main.turan_coeff_nonneg`** | + `C_schur_of_kernel` |

Each bridge is stated to **consume the proven results below it**, so exactly the
listed axiom is added at each step and nothing else (see `#print axioms`).

## Module map

Paper sections of `../shields-2026-cubic-pochhammer.tex`: §1 introduction, §2
`sec:beta-binomial`, §3 `sec:monotonicity-lemmas`, §4 `sec:kernel`, §5
`sec:proof`.

```
Weighting     — §3      one-sign-change weighting (lem:weighting)          [proven]
ResidueSums   — §4      R_a, period-6 closed form, residue-class moments   [proven]
Snj           — §4      S_{n,j} closed form + S_{n,j} ≥ 0 (eq:S-table)     [proven]
Bernstein     — §4      J_m definition, J_m(t) > 0 (lem:bernstein)         [axiom Jm_bernstein]
Kernel        — §4      J_{m,w}(t) ≥ 0 (thm:kernel)                        [+ block_certificate]
Bridge        — §2,§3,§5 C_{m,f}, Schur-concavity (eq:C-def, prop:C-schur)  [+ C_schur_of_kernel]
Main          — §5      turan_coeff_nonneg (thm:main)                      [assembles the above]
AxiomCheck    —         #print axioms regression guard
```

---

# The three bridge axioms, and how to remove them

Nothing below weakens the proven core: `Snj_nonneg`, `three_R_closed`,
`sum_weighted_nonneg` do **not** transitively use any of these (verified by
`#print axioms`).  Each isolates one paper step and is stated so that the proven
results feed into it.

## A1. `Jm_bernstein` — the Bernstein coefficient identity (§4, `eq:P-coeff`)

`3(n+1) J_m(t) = Σ_{j=0}^{n+1} S_{n,j} C(n+1,j) t^j (1-t)^{n+1-j}`, `n = 3m-2`.

**What it is.** A finite polynomial identity: the coefficients of `J_m` in the
degree-`(n+1)` Bernstein basis are `S_{n,j}/(3(n+1))`.  It is the projective
Bernstein transform `eq:P-def` together with the coefficient extraction
`eq:P-coeff`.  It is **purely combinatorial** — no analysis, no Mathlib gap.

**Why it is an axiom here.** Discharging it is a `Polynomial` coefficient
computation (two binomial revision identities and a Cauchy product); it is
verified symbolically in `../scripts/verify_kernel.py` (eq:P-coeff, the two
binomial identities, and the Bernstein reconstruction of `J_m`) and by hand at
`m=2` (both sides `90 t²(1-t)`).  Its **positive consequence** `Jm_pos` is proven
here from it and the theorem `Snj_nonneg`.

**What would remove it.** Formalize `eq:P-coeff` with `Polynomial.coeff` and the
two binomial revision identities `C(n,k)C(n-k,j-k)=C(n,j)C(j,k)` and
`C(n,k)C(n-k,j-k-1)=C(n+1,j)C(j,k)(j-k)/(n+1)`.  Then `Jm_pos` becomes an
ordinary theorem.

## A2. `block_certificate` — block decomposition and single sign change (§4.2)

Pairs the terms `r ↔ m-r` of `J_{m,w}` into blocks `B_{m,r}` (`eq:B-def`); the
block sequence has at most one sign change (`lem:block-sign`) and sums to `J_m`.

**What it is.** Two facts: (i) the algebraic pairing reindexing `eq:B-def`; and
(ii) the single sign change `lem:block-sign`, a `tanh` monotonicity —
`d ↦ d·tanh(3dx/2)` is strictly increasing.

**Why it is an axiom here.** The sign change is a real-analytic monotonicity;
Mathlib has `Real.tanh` but the argument (and the pairing reindexing) is §4.2
bookkeeping.  The **transfer** of the block structure to `J_{m,w} ≥ 0` — the
proven one-sign-change weighting `sum_weighted_nonneg` applied to the proven
constant-weight positivity `Jm_pos` — is done in `Kernel.Jmw_nonneg`.

**What would remove it.** Prove the pairing by `Finset` reflection and the sign
change from `Real.tanh` strict monotonicity plus the algebraic
`(1-t³)/(1+t³) < 3(1-t)/(1+t)` (the odd-`m` central case, an elementary
`(1-t)²(1+t) > 0`).

## A3. `C_schur_of_kernel` — the beta-binomial reduction (§2, §3, §5)

Schur-concavity of the coefficient convolution `C_{m,f}` (`prop:C-schur`): at
fixed parameter sum, smaller imbalance gives the larger value of `C_{m,f}`.

**What it is.** The beta-binomial representation `eq:C-beta`
(`C_{m,f} = Λ(s)·𝔼 G_{m,w}(P)`, `P ∼ Beta(u,v)`) followed by the likelihood-ratio
order of `lem:beta-order`.  This is the **only genuinely measure-theoretic**
step.  It is stated to consume the proven kernel monotonicity as the explicit
hypothesis `hker` (= `Kernel.Jmw_nonneg`), so the bridged content is exactly
`eq:C-beta` + `lem:beta-order`.

**Why it is an axiom.** It needs the `Beta(u,v)` law, its density after the
`q = p(1-p)` change of variables, and the likelihood-ratio ⇒ usual stochastic
order (`ShakedShanthikumar2007`).  Mathlib has pieces but not an off-the-shelf
route.

**What would remove it.** Formalize the Beta-Binomial mixture and `lem:beta-order`
(`cosh(d₂ℓ)/cosh(d₁ℓ)` strictly increasing ⇒ single density crossing ⇒ stochastic
order).  Then `turan_coeff_nonneg` follows from `Jmw_nonneg` with no axioms.

## Deliberately out of scope

- **`cor:ordinary`** (ordinary log-concavity of `μ ↦ F_f(μ;x)`): Stirling
  asymptotics, radius of convergence, and continuity in `μ` — analytic.
- **`cor:strict`** (strict coefficient classification): the strict half of
  `lem:beta-order`; same bridge as A3.

## Axiom summary

| Axiom | Paper | Kind |
|---|---|---|
| `Jm_bernstein` | `eq:P-coeff` (§4) | finite polynomial identity (combinatorial) |
| `block_certificate` | `eq:B-def`, `lem:block-sign` (§4.2) | algebraic reindex + `tanh` monotonicity |
| `C_schur_of_kernel` | `eq:C-beta`, `lem:beta-order`, `prop:C-schur` (§2,§3,§5) | beta-binomial / stochastic order |

## Verification

`#print axioms` (module `AxiomCheck`):

- `Snj_nonneg`, `three_R_closed`, `sum_weighted_nonneg` →
  `[propext, Classical.choice, Quot.sound]` (no `sorry`, no project axioms).
- `Jm_pos` → `+ Jm_bernstein`.
- `Jmw_nonneg` → `+ Jm_bernstein, block_certificate`.
- `turan_coeff_nonneg` → `+ Jm_bernstein, block_certificate, C_schur_of_kernel`.

The combinatorial identities (`eq:P-coeff`, `eq:S-table`, `eq:S-R`) are
cross-checked symbolically in `../scripts/verify_kernel.py`, and `thm:main` /
`prop:C-schur` in `../scripts/verify_theorem.py`.
