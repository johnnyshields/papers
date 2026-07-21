# Lean 4 formalization — Sharp coefficientwise positivity for a matrix Turán determinant of ₀F₁

Formalizes the core of `../shields-2026-turan-bessel.tex` against Mathlib
(`leanprover/lean4:v4.30.0-rc2`, namespace `TuranBessel`).  `lake build` is green
with **one** `sorry` and a small, fully localized set of bridge axioms, all
documented below.

## Build

```
lake exe cache get   # fetch the pinned Mathlib build cache (once)
lake build
```

## What is proven (unconditionally)

The **central theorem of the paper** and its sharpness are proven with no `sorry`
and no project-specific axioms — `#print axioms` reports only Lean/Mathlib's
`[propext, Classical.choice, Quot.sound]`:

| Result | Paper | Lean |
|---|---|---|
| Sharp coefficientwise positivity, `Δ_n(a)>0`, `κ=1` | `thm:coefficientwise` | `Main.coefficientwise_positivity` |
| Threshold sharp: `κ<1` fails / `κ≥1` deformation | `thm:coefficientwise`, `prop:bessel-sharpness`, `eq:MD01-kappa` | `Threshold.MDkappa_neg_exists` / `MDkappa_ge_pos` |
| Gram positive-definiteness of stable coeffs | `thm:gram` | `Gram.Nmat_pd_two`, `Gram.Nmat_pd_one` |
| Degree-two `Q_*` decomposition, `Δ_2>0` | `lem:Delta2-positive`, `eq:Qstar-decomp` | `Degree.Dcoeff_two_pos` |
| Negative-order failure `Δ_2(a)<0` on `-2<a<-1` | `prop:negative-coeff-failure` | `NegativeOrder.Dcoeff_two_neg` |
| Wedge/MD positivity | `lem:MD-positive` | `MatrixMD.MD_nonneg`, `MD_pos_of_psd_pd` |
| Trigamma bounds (both sharp, trapezoidal) | `lem:trigamma-bounds`, `eq:trig-lower`, `eq:trig-upper-half` | `Trigamma.trigamma_gt_inv_sharp`, `trigamma_lt_upper` |
| ℓ² Cauchy–Schwarz | (Gram argument) | `Trigamma.tsum_mul_sq_le` |

Trigamma `ψ₁` is **built from scratch** (`∑(y+n)⁻²`) because Mathlib has no
polygamma. The algebraic identities are cross-checked in `../scripts` (sympy).

## Module map

Paper sections (of `../shields-2026-turan-bessel.tex`): 2 `sec:main`, 3
`sec:bessel-reduction`, 4 `sec:coefficients`, 5 `sec:conditional`, 6 `sec:gram`,
7 `sec:determinant`, 8 `sec:bessel-consequences`.  Each module header names the
section(s) it formalizes.

```
MatrixMD     — §7      2×2 symmetric matrices, MD, wedge positivity (lem:MD-positive)
Trigamma     — §6      ψ₁ from series: summability (incl. continuation), bounds, CS
Coefficients — §4,§5   closed-form matrices N_m (α_m,β_m,c_m), reduced weights s_m
Gram         — §6      slack identity, CS+cross-sum ⇒ N_m ≻ 0 (thm:gram)
Degree       — §7      Δ_1>0 (MD01), Q_* identity Dcoeff_two_eq, Δ_2>0, MD(N_1,N_m)≥0
Main         — §7      coefficientwise_positivity (thm:coefficientwise §2, κ=1)
Threshold    — §7,§2   κ<1 fails (eq:MD01-kappa; completes the iff)
NegativeOrder— §8      Δ_2<0 on -2<a<-1 (prop:negative-coeff-failure, lem:continuation)
Bridge       — §2,§3,§4 external inputs as documented axioms + derived corollaries
stale/       — archived helpers unused by any proof (not in the build target)
```

---

# Known limitations, axioms, and how to remove them

Nothing below weakens the proven core: `coefficientwise_positivity` and the
sharpness results do **not** transitively use any of these (verified by
`#print axioms`). They isolate exactly the paper results that require machinery
Mathlib does not yet have.

## L1. One `sorry` — the pointwise Bessel inequality `thm:bessel`

`Bridge.bessel_schur_ineq`:
`(1+P_ν(z))² < G_ν(z)(H_ν(z)+4/ψ₁(ν+1))` for `ν>-1`, `z>0`.

**Why it is unproven.** The statement is phrased with the opaque Bessel
functionals `besselG/P/H`. The paper derives it from
`D_{a-1}(2√λ)=4Δ(a,λ)/(ψ₁(a)Z⁴)` and the **pointwise** positivity `Δ(a,λ)>0`
(`λ>0`). We prove the *coefficientwise* positivity `Δ_n>0`; converting that to a
pointwise value is a real-analysis step, and the Bessel objects themselves are
not defined.

**What would remove it.**
1. Modified Bessel functions `I_ν, K_ν` in Mathlib (see L3) — the hardest part.
2. Define `Z`, `A`, `B`, `C` (see L2) and prove `eq:I-Z`, `eq:D-Delta`.
3. Assemble the strictly-positive Maclaurin series `Σ_{n≥1} Δ_n(a) λⁿ > 0` into
   the pointwise value: needs a coefficient growth bound giving summability of
   `Δ_n(a) λⁿ` (routine given the analytic `Z`, but not yet in place). This third
   step alone, given L2/L3, is small.

The matrix corollary `cor:bessel-matrix` (`Bridge.bessel_schur_matrix_pd`) is
*derived* from `bessel_schur_ineq` plus one extra axiom `besselG_pos`
(`G_ν(z)>0`, order log-convexity of `I_ν`), so it inherits the same `sorry`.

`prop:bessel-sharpness` has two halves: the **deformation** half (`D_ν^{(κ)}>0`
for all `ν>-1,z>0` iff `κ≥1`) is proven at coefficient level in `Threshold`; the
**boundary-correction** half (`4/ψ₁(ν+1)` is the least admissible `R`) is a `z↓0`
limit of `G_ν,H_ν,P_ν` and is Bessel-dependent (L3).

## L2. Coefficient-formula bridge — `turanDetCoeff`, `turanDetCoeff_eq`

These assert that the *genuine* Maclaurin coefficient `[λⁿ] det 𝒯(a,λ)` equals
`turanCoeffFactor(a) · Dcoeff a n`.  The factor `turanCoeffFactor(a) =
ψ₁(a)/(2Γ(a)⁴)` is a definition (`Real.Gamma`) with proven positivity
`turanCoeffFactor_pos`; the axioms are `turanDetCoeff` (the analytic coefficient)
and the identity `turanDetCoeff_eq`.
`Dcoeff` (proven positive) is the combinatorial mixed-determinant sum built from
the closed-form matrices `N_m`.

**Why they are axioms.** Discharging `turanDetCoeff_eq` = proving `eq:Delta-n-MD`
= re-deriving §3–§5 analytically, which needs three things absent from Mathlib:
- **`lem:convolution`** — the asymmetric reciprocal-gamma convolution, i.e. the
  Gauss ₂F₁ / Chu–Vandermonde theorem *for real parameters*. Mathlib has the
  binomial Vandermonde (`Nat.add_choose`) but not the real-Γ (terminating ₂F₁)
  form.
- **The reciprocal-gamma series `Z` and its calculus** — `Z(a,λ)=Σ λ^k/(k!Γ(a+k))`
  and `A,B,C_κ` as its `a`- and Euler-derivatives.
- **Polygamma** — parameter differentiation of `1/Γ(a+k)` produces `ψ_j(a+k)`;
  Mathlib has only `digamma = logDeriv Γ`, no higher polygamma. (We built `ψ₁`
  ourselves but not the general family.)

**What would remove them.**
1. Formalize `lem:convolution` (a finite identity; provable by induction / the
   terminating ₂F₁ evaluated at 1, on top of `Real.Gamma`, `Real.Gamma_add_one`).
2. Define `Z` and its `A,B,C`; port the polygamma coefficient formulas
   (`thm:coefficients`, `α_m=ψ₁(a+m)`, etc.).
3. `turanCoeffFactor` is a `Real.Gamma` definition with proven positivity, so only
   `turanDetCoeff` and its identity `turanDetCoeff_eq` need the analytic layer.

Estimated effort: several hundred lines plus the polygamma and real-₂F₁
prerequisites. Once done, `turanDetCoeff_pos` (already derived here) becomes an
ordinary theorem.

## L3. Bessel dictionary — `besselG`, `besselP`, `besselH`, `besselSchurCoeff`, `besselSchurCoeff_eq`, `besselG_pos`

Introduce the modified Bessel `I_ν` and the curvature functionals `G_ν,P_ν,H_ν`
(`eq:Gnu`–`eq:Hnu`), and assert their small-argument coefficients are positive
multiples of the determinant coefficients (`eq:I-Z`, `eq:D-Delta`).

**Why they are axioms.** Mathlib has **no** modified Bessel functions at all, nor
their derivatives with respect to the order (DLMF §10.38). Every Bessel-side
object in the paper is therefore undefined in Mathlib.

**What would remove them.** A standalone special-functions contribution:
`I_ν, K_ν` (series definitions, holomorphy, the connection formula `eq:I-connection`),
and order-derivative asymptotics. This is the single largest gap and the one least
likely to be short. Given it, `besselSchurCoeff_pos` (already derived here from
`turanDetCoeff_pos`) and then `bessel_schur_ineq` follow.

The paper's supporting negative-order Bessel lemmas — `lem:continuation` (analytic
continuation, needs the `Z`-calculus of L2), `lem:pole-order-estimates` and
`prop:pole-limit-failure` (order derivatives of `I_ν, K_ν` at negative integers),
and `prop:small-z` (small-`z` expansion of `D_ν`) — all sit behind this same gap.
Their purely-algebraic consequence `prop:negative-coeff-failure` **is** proven
(`NegativeOrder.Dcoeff_two_neg`), by continuing the trigamma series to `-2<a<-1`
and reusing the `Q_*` identity.

## L4. Deliberately out of scope

- **Explicit `Γ`-form of `cor:Delta-lower`** (`Δ_1(a)>λ/(a⁴Γ(a)⁴)`): a Γ-free
  lower bound on `MD(N_0,N_1)` is immediate from the sharp trigamma bound already
  proven; only the literal `Γ`-normalized constant needs `Real.Gamma`.
- **§5 «Probabilistic interpretation: the finite conditional law»
  (`sec:conditional`)**: interprets the coefficient weights via Bessel-law
  variables; an interpretation that does not reprove positivity, so not formalized.
- **§9 `sec:context` and the §11 appendix «Confluent minors of the modified
  Bessel kernel» (`app:confluent`, `prop:tp-confluent`)**: a comparison with the
  strict-total-positivity results for the kernel `I_s(x)`; context only, and
  Bessel-kernel-dependent, so out of scope (L3).

## Axiom summary

| Axiom | Kind | Blocking Mathlib gap |
|---|---|---|
| `turanDetCoeff`, `turanDetCoeff_eq` | coefficient bridge (L2) | real-parameter Gauss ₂F₁; polygamma; `Z`-calculus |
| `besselG/P/H`, `besselSchurCoeff`, `_eq`, `besselG_pos` | Bessel dictionary (L3) | modified Bessel functions + order derivatives |
| `bessel_schur_ineq` (`sorry`, L1) | pointwise inequality | L3 + positive-series assembly |

## Verification

`#print axioms coefficientwise_positivity` = `[propext, Classical.choice,
Quot.sound]` — no `sorry`, no L1–L3 axioms. The same holds for the sharpness
results (`MDkappa_neg_exists`, `Dcoeff_two_neg`) and the analytic lemmas
(`trigamma_gt_inv_sharp`, `tsum_mul_sq_le`). Algebraic identities (slack, `Q_*`,
cross-sum) are checked symbolically in `../scripts`.
