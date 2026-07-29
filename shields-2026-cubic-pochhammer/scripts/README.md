# Computational supplement

Verification scripts for *Coefficientwise log-concavity of the cubic
multiple-Pochhammer series*.  The proof in the paper is elementary and
self-contained; these scripts are an independent regression harness.  Every
script re-derives the closed forms it checks from the defining objects — the
series

    F_f(mu; x) = Σ_{n≥1} f_n (mu)_{3n} / (3n-1)! x^n,

the coefficient convolution C_{m,f}(u,v), and the residue kernel G_{m,w} — so
the identities are pinned to their definitions rather than transcribed.
Symbolic work uses SymPy; numerical work uses mpmath at arbitrary precision (no
floating-point arithmetic in the verification loops); combinatorial identities
use exact integer or rational arithmetic.

Where the paper states a hypothesis, a threshold, or a congruence, the harness
also shows it is **load-bearing**, by crossing the boundary and exhibiting the
failure.

Reference environment: Python 3.12, SymPy 1.14.0, mpmath 1.3.0.

```bash
python -m pip install -r requirements.txt
./run_all.sh
```

## Scripts by section

| Script | Paper section | Content |
| --- | --- | --- |
| `verify_beta_binomial.py` | §2 | Symmetry and center-monotonicity of the paired weights `w_k = f_k f_{m-k}` from log-concavity, via the cross-product `f_{a+1}f_b ≥ f_a f_{b+1}`; the coefficient convolution `C_{m,f}` and its vanishing at `u=0`; the Pochhammer/beta-binomial weight identity (eq. 2.3); the endpoint identity `j(N-j)C(N,j)=N(N-1)C(N-2,j-1)`; that the beta-binomial pmf is a law (Chu–Vandermonde); eq. (2.3) as an assembled equation, with `J(N-J)` making the endpoint weights irrelevant; the mixture identity `C = (u+v)_N/N! · N(N-1) · E G_{m,w}(P)` (eqs. 2.4–2.5) as a single symbolic identity; the `p ↔ 1-p` symmetry of `G_{m,w}`. |
| `verify_monotonicity_lemmas.py` | §3 | Lemma 3.1 (one-sign-change weighting) with its pivot bound, its `c=0` branch, and its **strict clause** — the form the strict half of Theorem 4.1 consumes — each of whose three added hypotheses is shown load-bearing by a counterexample; the sign-change count *and* its direction stress-tested. Lemma 3.2 (symmetric beta imbalance ordering): the closed-form density of `Q_d = P_d(1-P_d)`, monotonicity of `ℓ(q)` and of `cosh(d₂ℓ)/cosh(d₁ℓ)`, the single crossing of `g_{d₁}-g_{d₂}` on a log-refined grid (the crossing can sit at `q ≈ 2·10⁻⁵`, so the grid has to reach that scale — itself asserted), the proof's integrand nonnegative *throughout* `(0,1/4)`, and `E H(P_{d₁}) ≥ E H(P_{d₂})` (eq. 3.1). |
| `verify_kernel.py` | §4 | The `t`-substitution of `G_m` with `0≤p≤1/2 ⇔ 0≤t≤1` and the derivative identity (eqs. 4.2–4.3); the projective transform `P_m` (eqs. 4.4–4.5); the coefficient formula (eq. 4.6), the two binomial identities, `S_{n,j}` (eq. 4.7), the root-of-unity counts by three routes (table, trigonometry, and the `ω`-filter in exact `Z[ω]`) plus the ℂ-free Pascal recurrence, the moments, the R-expansion (eq. 4.9), and the six-case table (eq. 4.8); the exponential bounds (eqs. 4.10–4.11), their failure one step below range, and that both are **attained** at `m=3` (`S_{7,6}=S_{7,7}=0`); nonnegativity of every `S_{n,j}` and that the congruence `n+1 ≡ 2,5 (mod 6)` is **load-bearing** — without it `S_{n,j}` goes negative (first `S_{5,6}=-30`, `S_{6,6}=-15`); the Bernstein reconstruction of `J_m`, `J_m>0` and `G_m` strictly increasing; the weighted blocks `B_{m,k}` (eqs. 4.14–4.15, with the centre block's `m/2` derived from eq. (4.13)), the hyperbolic form (eq. 4.16), the single sign change with `B_k≤0 ⇒ B_{k-1}<0` (Lemma 4.3), Theorem 4.1, that eq. (4.1)'s ordering is load-bearing (decreasing weights drive `J_{m,w}<0`) and strictly weaker than log-concavity of the weights (monotone non-log-concave witnesses still satisfy Theorem 4.1, while every weight set from a log-concave `f` satisfies eq. (4.1)), the `B_{m,k}` domain guard, and the scope edges (`G_{m,w}` decreases on `[1/2,1]`; `J_1=0`, so `m≥2` is needed for strictness). |
| `verify_theorem.py` | §5, §1 | Eq. (5.1) by direct convolution of the two products; the shared parameter sum, ordered deviations `d₁ ≤ d₂`, and the symmetry `C_{m,f}(u,v)=C_{m,f}(v,u)` the absolute value needs; the vanishing of degrees 0 and 1 and of the Turánian at `α=0` or `β=0`; §1's hypothesis (nonnegative, interval support, log-concave), the `n≥1` versus `n≥0` indexing equivalence, and `f_{n+1}/f_n` nonincreasing (hence `R>0`); Proposition 5.1 (Schur-concavity of the convolution, strict) with its excluded boundary `d=s/2` recorded separately; Theorem 1.1 (coefficientwise nonnegativity) and Corollary 5.2 (strict classification, both directions, and its `μ=0` branch in the form the proof uses) on random rational log-concave sequences and on the extremal cases (geometric `f`, single-point support); the §1 triplication identity `F_f = 3x (d/dx) ₃F₂` for `f_n≡1`; Corollary 5.3 (the Stirling ratio with a fitted `O(1/n)` rate including the exact case `μ=1`, the shared radius of convergence for constant and geometric `f`, continuity in `μ`, and midpoint-hence-full concavity of `μ ↦ log F_f(μ;x)`). |
| `verify_remarks.py` | §6 | The control quantity `G_m(p) = p(1-p) P{Bin(3m-2,p) ≡ 2 (mod 3)}`; log-concavity as the load-bearing hypothesis for the weight monotonicity (the implication is one-directional at fixed `m`, with a witness); the general-`r` kernel `= p(1-p) P{Bin(rm-2,p) ≡ r-1 (mod r)}` for `r=2,3,4`, no other residue class, and its weighted analogue with symbolic `w_k`; that positivity is not termwise in the monomial basis (`J_m` has negative monomial coefficients while every Bernstein coefficient is `≥0`); the failure of the Bernstein certificate at `r=4` — the lifted array is nonnegative for `r=3` but the first obstruction for `r=4` sits at index `j=8` (first at `m=3`), with `J^{(3)}_m>0` on `(0,1)` for `2≤m≤12` by exact root count while `J^{(4)}_3` has an interior sign change; and the explicit `r=4` counterexample for `f_n=1` (`m=3`, `α=β=1`), whose exact factorization puts the threshold at `μ=16` — zero there, negative for every real `μ>16`, `-87679680` at the smallest integer witness `μ=17` — reproducing Karp–Zhang's Remark 5 by three independent routes while the `r=3` Turánian stays `≥0`. |
| `check_kernel_stdlib.py` | §4.1, Lemma 4.2 | Dependency-free integer audit (standard library only, no float) of the positivity certificate `S_{n,j} ≥ 0`, eqs. (4.6)–(4.9), the `δ` branch bounds, and the load-bearing congruence, over a wide range of `m`. Run `python3 check_kernel_stdlib.py [MAX_M]` (default 120). Scope: the certificate and eqs. (4.6)–(4.9); `J_m` itself, the link back to `P_m` through eqs. (4.4)–(4.5), and eqs. (4.10)–(4.11) are in `verify_kernel.py`. |

Each script prints `PASS` lines and ends with `ALL PASS`; any broken identity
raises `AssertionError` and stops the script with a nonzero exit code.
`./run_all.sh` runs all six in dependency order and exits nonzero on the first
failure.

Bibliographic pinpoint checks against the published reference PDFs, and a
mutation tester that confirms each assertion above can fail, are archived under
`../stale/stale-scripts/`; they need dependencies beyond `requirements.txt` and
are not part of `run_all.sh`.
