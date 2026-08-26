#!/usr/bin/env python3
r"""Mutation test: confirm this harness's assertions can actually fail.

An assertion that cannot fail is not coverage, and nothing else in the tree
establishes that these can.  Each mutation below breaks one thing some check is
supposed to catch; this script copies the paper directory to a temporary
sandbox, applies the mutation there, runs the ONE affected check in that
sandbox, and requires a nonzero exit.  A mutation that still passes is a
SURVIVOR -- a vacuous assertion -- and this script then exits nonzero.

Two kinds of target.  A `scripts/...` mutation edits an assertion or the value
it rests on; a `paper` mutation edits `../shields-2026-cubic-pochhammer.tex`,
which is how the guards that read the manuscript -- the figure's inlined
coordinates and its axis and caption literals, and the cross-reference guard --
are exercised.

Everything happens under a temporary directory: nothing here writes inside the
paper directory, and the sandbox carries the `.tex` and `.aux` beside its copy
of `scripts/` so the manuscript-reading guards resolve as they normally do.

Only the named check runs, not the whole script, which is what makes this
affordable as the last step of `run_all.sh`.
"""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAPER_DIR = HERE.parent
PAPER = 'shields-2026-cubic-pochhammer.tex'

# (label, target, check, find, replace).  `target` is a file under scripts/, or
# the string 'paper'; `check` is `module:function`, the one check that must fail.
MUTATIONS = [
    # --- section `sec:reduction`: the beta-binomial reduction ------------------------------
    ("`lem:central-products` converse: drop interval support from the conclusion",
     "verify_beta_binomial.py", "verify_beta_binomial:check_central_products_converse",
     "assert hyp == (logconcave(f) and interval_support(f)), tup",
     "assert hyp == logconcave(f), tup"),
    ("`lem:central-products` converse: drop log-concavity from the conclusion",
     "verify_beta_binomial.py", "verify_beta_binomial:check_central_products_converse",
     "assert hyp == (logconcave(f) and interval_support(f)), tup",
     "assert hyp == interval_support(f), tup"),
    ("`eq:C-def`: claim C_{m,w}(u,1) vanishes",
     "verify_beta_binomial.py", "verify_beta_binomial:check_C_vanishes",
     "assert sp.simplify(C_def(m, w, u, sp.Integer(0))) == 0, m",
     "assert sp.simplify(C_def(m, w, u, sp.Integer(1))) == 0, m"),
    ("`eq:G-weighted`: a typo in G_weighted's binomial must break `eq:C-beta`",
     "verify_beta_binomial.py", "verify_beta_binomial:check_mixture_identity",
     "w[r] * comb(3 * m - 2, 3 * r - 1) * p ** (3 * r)",
     "w[r] * comb(3 * m - 2, 3 * r) * p ** (3 * r)"),
    ("Chu-Vandermonde: perturb the right side",
     "verify_beta_binomial.py", "verify_beta_binomial:check_beta_binomial_is_a_law",
     "assert sp.simplify(sp.expand(mass - sp.rf(u + v, N))) == 0, m",
     "assert sp.simplify(sp.expand(mass - sp.rf(u + v, N + 1))) == 0, m"),
    # --- section `sec:reduction` again: the beta-moment route of check_beta_moment_fold -----
    ("beta-moment shift: shift the Pochhammer length by one",
     "check_beta_moment_fold.py", "check_beta_moment_fold:check_bmom_shift",
     "            lhs = B(a + j, b + k) * sp.rf(a + b, j + k)",
     "            lhs = B(a + j, b + k) * sp.rf(a + b, j + k + 1)"),
    ("`eq:C-beta` cleared: perturb the factorial in the closed form",
     "check_beta_moment_fold.py",
     "check_beta_moment_fold:check_star_identity_quadrature",
     "            rhs = mp.mpf(factorial(3 * m - 2)) * Bmom(u, v) * Cmw(m, w, u, v)",
     "            rhs = mp.mpf(factorial(3 * m - 1)) * Bmom(u, v) * Cmw(m, w, u, v)"),
    ("`eq:C-beta` exactly: a typo in the binomial of the term-by-term beta sum",
     "check_beta_moment_fold.py", "check_beta_moment_fold:check_star_identity_exact",
     "        lhs = sum(ws[r - 1] * sp.binomial(3 * m - 2, 3 * r - 1)",
     "        lhs = sum(ws[r - 1] * sp.binomial(3 * m - 2, 3 * r)"),
    ("the fold: compare the folded half against the left half alone",
     "check_beta_moment_fold.py", "check_beta_moment_fold:check_fold",
     "            lhs = full_quad(a, b, H)",
     "            lhs = left_quad(a, b, H)"),
    ("the fold's symmetry hypothesis: run the boundary probe on symmetric weights",
     "check_beta_moment_fold.py", "check_beta_moment_fold:check_fold_needs_symmetry",
     "    for m, w in ASYM:", "    for m, w in SYM:"),
    ("the folded kernel: drop the -1 from the (p(1-p)) exponent",
     "check_beta_moment_fold.py", "check_beta_moment_fold:check_foldker_cosh",
     "                rhs = 2 * (p * (1 - p)) ** (s / 2 - 1) * mp.cosh(d * logit(p))",
     "                rhs = 2 * (p * (1 - p)) ** (s / 2) * mp.cosh(d * logit(p))"),
    ("the cosh grid: collapse it so every instance is an equality",
     "check_beta_moment_fold.py", "check_beta_moment_fold:check_cosh_cross",
     "    grid = [R(0, 1), R(1, 10), R(1, 2), R(1, 1), R(7, 3), R(5, 1)]",
     "    grid = [R(0, 1)]"),
    ("single crossing: exchange the two imbalances, reversing the sign pattern",
     "check_beta_moment_fold.py", "check_beta_moment_fold:check_single_crossing",
     "            g = lambda p: Z1 * foldKer(s, d2, p) - Z2 * foldKer(s, d1, p)",
     "            g = lambda p: Z1 * foldKer(s, d1, p) - Z2 * foldKer(s, d2, p)"),
    ("end to end: lengthen the Pochhammer in the beta-moment quotient",
     "check_beta_moment_fold.py", "check_beta_moment_fold:check_end_to_end",
     "                viaint = (poch(s, 3 * m) / mp.mpf(factorial(3 * m - 2))",
     "                viaint = (poch(s, 3 * m + 1) / mp.mpf(factorial(3 * m - 2))"),
    # --- `lem:weighting` and `lem:beta-order` ------------------------------------
    ("cone equivalence: the wrong step weight cannot recover a tail",
     "verify_monotonicity_lemmas.py", "verify_monotonicity_lemmas:check_cone_equivalence",
     "        step = [Fraction(0)] * sig + [Fraction(1)] * (L - sig)",
     "        step = [Fraction(1)] * L"),
    ("strict cone clause: drop the 'nonzero w' hypothesis",
     "verify_monotonicity_lemmas.py", "verify_monotonicity_lemmas:check_cone_equivalence",
     "                if any(x > 0 for x in w):",
     "                if True:"),
    ("one-sign-change corollary: claim the nonstrict boundary is strict",
     "verify_monotonicity_lemmas.py",
     "verify_monotonicity_lemmas:check_one_sign_change_gives_positive_tails",
     "    assert all(x >= 0 for x in tails(flat)) and not all(x > 0 for x in tails(flat))",
     "    assert all(x > 0 for x in tails(flat))"),
    ("weight hypothesis: perturb the w=(5,1) witness value",
     "verify_monotonicity_lemmas.py",
     "verify_monotonicity_lemmas:check_weighting_needs_nondecreasing_nonnegative_weights",
     "    assert wsum == Fraction(-39, 10) < 0, wsum",
     "    assert wsum == Fraction(-39, 11) < 0, wsum"),
    ("cosh ratio: claim it rises in ell when d_1 > d_2",
     "verify_monotonicity_lemmas.py", "verify_monotonicity_lemmas:check_cosh_ratio_monotone",
     '                   (mp.mpf(0), mp.mpf("2.2"))]:',
     '                   (mp.mpf(3), mp.mpf("2.2"))]:'),
    ("`eq:beta-order`: claim a DEcreasing symmetric H obeys it",
     "verify_monotonicity_lemmas.py",
     "verify_monotonicity_lemmas:check_beta_order_hypotheses_on_H",
     '        assert rev < -mp.mpf("1e-10"), (ss, a, b, rev)',
     '        assert rev > mp.mpf("1e-10"), (ss, a, b, rev)'),
    ("gap restriction: narrow the sweep to gaps the cited comparison already reaches",
     "verify_monotonicity_lemmas.py",
     "verify_monotonicity_lemmas:check_cases_reach_past_the_gap_restriction",
     '    (mp.mpf("0.6"), mp.mpf("0.05"), mp.mpf("0.28")),    # 0.1, 0.56: outside, both',
     '    (mp.mpf("0.6"), mp.mpf("0.55"), mp.mpf("1.28")),'),
    ("LR crossing: drop the log-refined part of the grid",
     "verify_monotonicity_lemmas.py",
     "verify_monotonicity_lemmas:check_likelihood_ratio_single_crossing",
     "    log_part = [mp.mpf(10) ** (-mp.mpf(i) / 4) for i in range(4, 45)]",
     "    log_part = []"),
    # --- section `sec:kernel`: the residue kernel ---------------------------------------
    ("`thm:kernel` tails: build them from the head instead of the tail",
     "verify_kernel.py", "verify_kernel:check_central_window_tails",
     "            for val in reversed(blocks):",
     "            for val in blocks:"),
    ("`thm:kernel` tails: narrow the grid away from the delicate small-t corner",
     "verify_kernel.py", "verify_kernel:check_central_window_tails",
     "    grid = [Fraction(i, 48) for i in range(1, 48)]",
     "    grid = [Fraction(i, 4) for i in range(1, 4)]"),
    ("`eq:w-monotone` symmetry: perturb the symmetrized value at the same (m,t)",
     "verify_kernel.py", "verify_kernel:check_weight_symmetry_is_load_bearing",
     "assert Jw_unpaired(m, {1: Fraction(1), 2: Fraction(1)}, tv) == Fraction(12096, 15625)",
     "assert Jw_unpaired(m, {1: Fraction(1), 2: Fraction(1)}, tv) == Fraction(12096, 15624)"),
    ("`lem:bernstein`: perturb the closed value of b_2",
     "verify_kernel.py", "verify_kernel:check_bernstein_reconstruction",
     "assert Fraction(S_sum(n, 2), 3 * (n + 1)) == Fraction(n - 1, n + 1), m",
     "assert Fraction(S_sum(n, 2), 3 * (n + 1)) == Fraction(n - 2, n + 1), m"),
    ("`eq:w-monotone` symmetry: perturb the J_{3,(1,0)}(3/5) witness",
     "verify_kernel.py", "verify_kernel:check_weight_symmetry_is_load_bearing",
     "    assert Jw_unpaired(m, w, tv) == Fraction(-189, 125), Jw_unpaired(m, w, tv)",
     "    assert Jw_unpaired(m, w, tv) == Fraction(-189, 124), Jw_unpaired(m, w, tv)"),
    ("scope edges: claim G_{m,w} also rises on [1/2,1]",
     "verify_kernel.py", "verify_kernel:check_kernel_scope_edges",
     'assert b < a, ("not DEcreasing on [1/2,1] -- scope claim is empty", m)',
     'assert b > a, ("not DEcreasing on [1/2,1] -- scope claim is empty", m)'),
    ("the load-bearing congruence: claim the failures sit at 2, 5 (mod 6)",
     "verify_kernel.py", "verify_kernel:check_congruence_is_load_bearing",
     "assert sorted({(n + 1) % 6 for n, _, _ in negatives}) == [0, 1]",
     "assert sorted({(n + 1) % 6 for n, _, _ in negatives}) == [2, 5]"),
    ("`eq:B-center`: use the naive m instead of m/2 in the center block",
     "verify_kernel.py", "verify_kernel:check_block_decomposition",
     "center = comb(n, 3 * m // 2 - 1) * sp.Rational(m, 2)",
     "center = comb(n, 3 * m // 2 - 1) * sp.Integer(m)"),
    ("the stdlib audit: claim S_{n,j} stays nonnegative without the congruence",
     "check_kernel_stdlib.py", "check_kernel_stdlib:check_congruence_is_load_bearing",
     'assert negatives, "S_{n,j} should go negative once the congruence is dropped"',
     'assert not negatives, "S_{n,j} should go negative once the congruence is dropped"'),
    # --- section `sec:cubic-proof` and `sec:consequences` -----------------------------------------------------
    ("`cor:C-schur`: claim the endpoint value sits ABOVE the interior",
     "verify_theorem.py", "verify_theorem:check_schur_boundary",
     "                assert endpoint < interior, (m, s, endpoint, interior)",
     "                assert endpoint > interior, (m, s, endpoint, interior)"),
    ("`cor:strict`: shift the finite-support degree range by one",
     "verify_theorem.py", "verify_theorem:check_cor_strict_support_descriptions",
     "        assert pos == [m for m in range(2 * a, 2 * b + 1) if m <= deg], (a, b, pos)",
     "        assert pos == [m for m in range(2 * a, 2 * b + 2) if m <= deg], (a, b, pos)"),
    ("`cor:ordinary`: tighten the majorant past what is true",
     "verify_theorem.py", "verify_theorem:check_local_uniform_convergence_in_mu",
     "                assert coeff_ratio(mu, n) <= bound_c * npow, (M, mu, n)",
     "                assert coeff_ratio(mu, n) <= bound_c * npow / 10 ** 6, (M, mu, n)"),
    ("`cor:ordinary`: demand f_{n+1}/f_n INcrease on the support",
     "verify_theorem.py", "verify_theorem:check_hypothesis_and_ratio_monotonicity",
     'assert b <= a, ("ratio not nonincreasing", f)',
     'assert b >= a, ("ratio not nonincreasing", f)'),
    ("`cor:ordinary`: push y outside the radius of convergence",
     "check_proof_steps.py", "check_proof_steps:check_weierstrass_majorant_summable",
     "        y = R * mp.mpf(9) / 10",
     "        y = R * mp.mpf(11) / 10"),
    ("`cor:ordinary`: run the finite-support sweep on a geometric f",
     "check_proof_steps.py", "check_proof_steps:check_radius_positive_both_supports",
     "        got = partials(finite_support, x, cutoffs)",
     "        got = partials(geometric, x, cutoffs)"),
    # --- the structural results ----------------------------------------------
    ("`prop:kernel-exact`: claim the limit of the beta moments is G(p) + p",
     "check_structural.py", "check_structural:check_kernel_reduction_exact",
     "        assert sp.simplify(sp.expand(lim - G)) == 0, (name, lim)",
     "        assert sp.simplify(sp.expand(lim - G - p)) == 0, (name, lim)"),
    ("`prop:kernel-exact`: flip the direction of the equivalence",
     "check_structural.py", "check_structural:check_kernel_exact_equivalence",
     "            assert not rises, (m, ws, rises[:1])",
     "            assert rises, (m, ws, rises[:1])"),
    ("`prop:kernel-exact`: perturb the leading-coefficient route to the limit",
     "check_structural.py", "check_structural:check_kernel_reduction_exact",
     "        by_leading = sp.expand(pn.LC() / pd.LC())",
     "        by_leading = sp.expand(pn.LC() / pd.LC()) + p"),
    ("`cor:differential`: perturb kappa_{m,s}",
     "check_structural.py", "check_structural:check_differential_covariance_identity",
     "    return poch(s, 3 * m) / sp.factorial(3 * m) * 3 * m * (3 * m - 1)",
     "    return poch(s, 3 * m) / sp.factorial(3 * m) * 3 * m * (3 * m + 1)"),
    ("`cor:differential`: name the logarithm as the obstruction, not the power",
     "check_differential_domination.py",
     "check_differential_domination:check_cosh_is_a_power",
     "        vals = [cosh(d * ell(mpf(10) ** (-e))) * mpf(10) ** (-e * d)",
     "        vals = [cosh(d * ell(mpf(10) ** (-e))) * log(1 / mpf(10) ** (-e))"),
    ("`cor:differential`: invert the far-endpoint majorant, losing q -> 1/4",
     "check_differential_domination.py",
     "check_differential_domination:check_uniform_domination",
     "                        lambda q: (1 - 4 * q) ** mpf('-0.5'))",
     "                        lambda q: (1 - 4 * q) ** mpf('0.5'))"),
    ("`cor:differential`: drop the compactness, taking d0 all the way to mu",
     "check_differential_domination.py",
     "check_differential_domination:check_uniform_domination",
     "    for mu, d0 in ((mpf(1), mpf('0.6')), (mpf('2.5'), mpf('2.0')),",
     "    for mu, d0 in ((mpf(1), mpf('1.0')), (mpf('2.5'), mpf('2.0')),"),
    ("`eq:fixed-sum`: perturb the beta moment's denominator",
     "check_fixed_sum_schur.py", "check_fixed_sum_schur:check_fixed_sum_kappa_and_folding",
     "        EGhat = sum(c * poch(u, j) * poch(v, j) / poch(u + v, 2 * j)",
     "        EGhat = sum(c * poch(u, j) * poch(v, j) / poch(u + v, 2 * j + 1)"),
    # --- `cor:differential`, the finite algebraic route ------------------------
    ("`-Phi''(0)` identity: drop the second half of `V_k`",
     "check_differential_coefficients.py",
     "check_differential_coefficients:check_uTV_identity",
     "V = [S(m_, 3 * k) + S(m_, 3 * (m - k)) for k in ks]",
     "V = [S(m_, 3 * k) for k in ks]"),
    ("pairwise failure: compare `k = 1` with itself instead of `l = m-1`",
     "check_differential_coefficients.py",
     "check_differential_coefficients:check_not_pairwise",
     "i, j = ks.index(1), ks.index(m - 1)",
     "i, j = ks.index(1), ks.index(1)"),
    ("asymptotic slack: claim `3/mu^2` instead of `2/mu^2`",
     "check_differential_coefficients.py",
     "check_differential_coefficients:check_tightness",
     "target = mp.mpf(2) / m_ ** 2",
     "target = mp.mpf(3) / m_ ** 2"),
    ("the reversal: keep the `j = 0` term instead of dropping it",
     "check_differential_coefficients.py",
     "check_differential_coefficients:check_split_reverses",
     "Vp = [Vk - 2 / m_ ** 2 for Vk in V]",
     "Vp = [Vk for Vk in V]"),
    ("Pochhammer Wronskian: sum the partial products, not their squares",
     "check_differential_coefficients.py",
     "check_differential_coefficients:check_poch_wronskian",
     "rhs += term ** 2",
     "rhs += term"),

    ("the tau collapse: shift the gap block by one index",
     "check_differential_coefficients.py",
     "check_differential_coefficients:check_tau_form",
     "return S(m_, n) - e2(m_, n, 3 * m - n)",
     "return S(m_, n) - e2(m_, n + 1, 3 * m - n)"),

    ("the Abel reduction: sum the tail from `j+1` instead of `j`",
     "check_differential_coefficients.py",
     "check_differential_coefficients:check_abel_reduction",
     "for k in range(j, m - j + 1)])\n                 for j in range(1, m // 2 + 1)]",
     "for k in range(j + 1, m - j + 1)])\n                 for j in range(1, m // 2 + 1)]"),

    # --- section `sec:threshold` and the r=4 obstruction -----------------------------------
    ("`cor:multiplicity`: perturb the constant the critical factor collapses to at r=3",
     "verify_multiplicity.py", "verify_multiplicity:check_multiplicity_classification",
     "    assert sp.Poly(3 * (4 * 3 - (3 - 3) * mu), mu).all_coeffs() == [36]",
     "    assert sp.Poly(3 * (4 * 3 - (3 - 3) * mu), mu).all_coeffs() == [35]"),
    ("`prop:multiplicity-threshold` minimality: demand every coefficient exceed 1",
     "verify_multiplicity.py", "verify_multiplicity:check_minimality_over_the_whole_cone",
     "        assert cs and all(c > 0 for c in cs), (N, min(cs))",
     "        assert cs and all(c > 1 for c in cs), (N, min(cs))"),
    ("not termwise: claim J_m has no negative monomial coefficient",
     "verify_multiplicity.py", "verify_multiplicity:check_not_termwise_obvious",
     'assert negs, ("expected negative monomial coefficients", m)',
     'assert not negs, ("expected negative monomial coefficients", m)'),
    ("a_8 < 0 for all m >= 3: make one factor of Q negative at m = 3",
     "check_r4_obstruction.py",
     "check_r4_obstruction:check_Q_positive_for_all_m_at_least_three",
     "    factors = [m - 2, m - 1, 2*m - 3, 2*m - 1, 4*m - 7, 4*m - 5, 4*m - 3]",
     "    factors = [m - 4, m - 1, 2*m - 3, 2*m - 1, 4*m - 7, 4*m - 5, 4*m - 3]"),
    ("Q > 0: perturb a coefficient of the expanded Q(3+s)",
     "check_r4_obstruction.py",
     "check_r4_obstruction:check_Q_positive_for_all_m_at_least_three",
     "    assert expanded == [256, 3136, 16240, 46060, 77224, 76489, 41415, 9450], expanded",
     "    assert expanded == [256, 3136, 16240, 46060, 77224, 76489, 41415, 9451], expanded"),
    ("the absorption threshold: shift the quadratic to m = 6",
     "check_r4_obstruction.py", "check_r4_obstruction:check_absorption_threshold",
     "    shifted = sp.Poly(sp.expand(quad_sym.subs(m, 7 + u)), u)",
     "    shifted = sp.Poly(sp.expand(quad_sym.subs(m, 6 + u)), u)"),
    ("the a_9 <= 0 branch: evaluate the group near zero instead of far out",
     "check_r4_obstruction.py", "check_r4_obstruction:check_group_nonneg_pointwise",
     "            xi = sp.Rational(10 ** 6)",
     "            xi = sp.Rational(1, 10 ** 6)"),
    # --- the guards that read the manuscript ---------------------------------
    ("the figure: change one digit of one inlined coordinate",
     "paper", "make_figure_multiplicity:check_inlined_coordinates",
     "(0.0020833333,0.00013831019)", "(0.0020833333,0.00013831018)"),
    ("the figure: change one curve's style so its block goes unmatched",
     "paper", "make_figure_multiplicity:check_inlined_coordinates",
     "blue!65!black, line width=0.9pt", "blue!65!black, line width=0.8pt"),
    ("the figure: lower the axis ceiling below the plotted data",
     "paper", "make_figure_multiplicity:check_no_clipping",
     "ymax=1.24", "ymax=1.19"),
    ("the figure: change a marker literal",
     "paper", "make_figure_multiplicity:check_marker_literals",
     "(0.2324081,1.0659009)", "(0.2324082,1.0659009)"),
    ("the caption: change an overshoot percentage",
     "paper", "make_figure_multiplicity:check_shapes",
     r"6.59\%", r"6.60\%"),
    ("the artwork builder: disable one curve with a leading comment",
     "paper", "render_figures:main",
     r"\addplot[red!75!black, dotted", "%" + r"\addplot[red!75!black, dotted"),
    ("the artwork builder: add a figure float it is not configured to render",
     "paper", "render_figures:main",
     r"\end{figure}", r"\end{figure}" + "\n" + r"\begin{figure}\end{figure}"),
    ("the cross-reference guard: rename a label the scripts cite",
     "paper", "check_paper_crossrefs:main",
     # the replacement is assembled rather than written out, so this file does
     # not itself carry a label reference the guard would (correctly) reject
     r"\label{lem:bernstein}", r"\label{lem:bernstein" + "-renamed}"),
]

RUNNER = """import sys
mod, fn = sys.argv[1].split(':')
m = __import__(mod)
getattr(m, fn)()
"""


def run_one(label, target, check, find, repl):
    """Apply one mutation in a fresh sandbox and return (killed, why)."""
    with tempfile.TemporaryDirectory() as td:
        root = Path(td) / 'paper'
        (root / 'scripts').mkdir(parents=True)
        for name in os.listdir(HERE):
            src = HERE / name
            if src.is_file() and (name.endswith('.py') or name.endswith('.md')):
                shutil.copy2(src, root / 'scripts' / name)
        for name in (PAPER, PAPER.replace('.tex', '.aux')):
            if (PAPER_DIR / name).exists():
                shutil.copy2(PAPER_DIR / name, root / name)
        edited = root / PAPER if target == 'paper' else root / 'scripts' / target
        if not edited.exists():
            return False, f"target {target} missing from the sandbox"
        text = edited.read_text(encoding='utf-8')
        if text.count(find) != 1:
            return False, f"find-string occurs {text.count(find)} times in {target}"
        edited.write_text(text.replace(find, repl), encoding='utf-8')
        (root / 'scripts' / '_run_one_check.py').write_text(RUNNER, encoding='utf-8')
        proc = subprocess.run([sys.executable, '_run_one_check.py', check],
                              cwd=root / 'scripts', capture_output=True,
                              text=True, timeout=1800)
        if proc.returncode == 0:
            return False, "SURVIVED -- the assertion cannot fail"
        return True, ""


def main() -> int:
    survivors, killed = [], 0
    for label, target, check, find, repl in MUTATIONS:
        ok, why = run_one(label, target, check, find, repl)
        if ok:
            killed += 1
        else:
            survivors.append((label, target, why))
            print(f"  !! {label} [{target}] -> {why}")
    print(f"{killed}/{len(MUTATIONS)} mutations killed")
    if survivors:
        print("SURVIVORS (vacuous, unreachable, or stale mutation targets):")
        for label, target, why in survivors:
            print(f"  - [{target}] {label}: {why}")
        return 1
    print("PASS  every one of the harness's mutated assertions failed as it should")
    print("ALL PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
