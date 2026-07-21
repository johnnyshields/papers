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

Reference environment: Python 3.12, SymPy 1.14.0, mpmath 1.3.0.

```bash
python -m pip install -r requirements.txt
./run_all.sh
```

## Scripts by section

| Script | Paper section | Content |
| --- | --- | --- |
| `verify_beta_binomial.py` | §2 | Symmetry and center-monotonicity of the paired weights `w_r = f_r f_{m-r}` from log-concavity; the coefficient convolution `C_{m,f}` and its vanishing at `u=0`; the Pochhammer/beta-binomial weight identity (eq. 2.3); the endpoint identity `j(N-j)C(N,j)=N(N-1)C(N-2,j-1)`; the mixture identity `C = (u+v)_N/N! · N(N-1) · E G_{m,w}(P)` (eqs. 2.4–2.5) as a single symbolic identity; the `p ↔ 1-p` symmetry of `G_{m,w}`. |
| `verify_monotonicity_lemmas.py` | §3 | Lemma 3.1 (one-sign-change weighting) with its pivot bound and a two-sign-change failure showing the hypothesis is sharp; Lemma 3.2 (symmetric beta imbalance ordering): the closed-form density of `Q_d = P_d(1-P_d)`, monotonicity of `ℓ(q)` and of `cosh(d₂ℓ)/cosh(d₁ℓ)`, the single crossing of `g_{d₁}-g_{d₂}` (likelihood-ratio order), and `E H(P_{d₁}) ≥ E H(P_{d₂})` (eq. 3.1). |
| `verify_kernel.py` | §4 | The `t`-substitution of `G_m` and the derivative identity (eqs. 4.2–4.3); the projective transform `P_m` (eqs. 4.4–4.5); the coefficient formula (eq. 4.6), the two binomial identities, `S_{n,j}` (eq. 4.7), the root-of-unity counts and moments, the R-expansion (eq. 4.9), and the six-case table (eq. 4.8); the exponential bounds (eqs. 4.10–4.11); nonnegativity of every `S_{n,j}`, the Bernstein reconstruction of `J_m`, `J_m>0` and `G_m` strictly increasing; the weighted blocks `B_{m,r}` (eqs. 4.14–4.15), the hyperbolic form (eq. 4.16), the single sign change (Lemma 4.3), and Theorem 4.1. |
| `verify_theorem.py` | §5 | Eq. (5.1) by direct convolution of the two products; the shared parameter sum and ordered deviations `d₁ ≤ d₂`; Proposition 5.1 (Schur-concavity of the convolution, strict); Theorem 1.1 (coefficientwise nonnegativity) and Corollary 5.2 (strict classification) on random rational log-concave sequences; Corollary 5.3 (the Stirling ratio and its `(3n)^μ/Γ(μ)` asymptotic, the shared radius of convergence, and midpoint-hence-full concavity of `μ ↦ log F_f(μ;x)`). |
| `verify_remarks.py` | §6 | The control quantity `G_m(p) = p(1-p) P{Bin(3m-2,p) ≡ 2 (mod 3)}`; log-concavity as the single load-bearing hypothesis for the weight monotonicity; the general-`r` kernel `= p(1-p) P{Bin(rm-2,p) ≡ r-1 (mod r)}` for `r=2,3,4`; the failure of the Bernstein certificate at `r=4` — the lifted coefficient array is nonnegative for `r=3` but the first obstruction for `r=4` sits at index `j=8` (first at `m=3`), matching `J^{(3)}_m>0` for all `m` while `J^{(4)}_3` dips negative; and the explicit `r=4` counterexample for `f_n=1` (`m=3`, `μ=17`, `α=β=1`, coefficient `<0`; `μ=16` still `≥0`), reproducing Karp–Zhang's Remark 3.7 by two independent routes while the `r=3` Turánian stays `≥0`. |
| `check_kernel_stdlib.py` | §4 | Dependency-free integer audit (standard library only) of the positivity certificate `S_{n,j} ≥ 0` and eqs. (4.6)–(4.9) over a wide range of `m`. Run `python3 check_kernel_stdlib.py [MAX_M]` (default 120). |

Each script prints `PASS` lines and ends with `ALL PASS`; any broken identity
raises `AssertionError` and stops the script with a nonzero exit code.
