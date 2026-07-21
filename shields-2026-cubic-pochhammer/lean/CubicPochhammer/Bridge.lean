/-
# Beta-binomial reduction bridge (§2, §3, §5)

Formalizes the coefficient convolution `C_{m,f}(u,v)` (`eq:C-def`) of
`shields-2026-cubic-pochhammer.tex` and the analytic reduction that turns
the proven kernel monotonicity (`Kernel.Jmw_nonneg`) into Schur-concavity of
`C_{m,f}` (`prop:C-schur`).

`C_{m,f}(u,v) = ∑_{r=1}^{m-1} f_r f_{m-r} (u)_{3r}(v)_{3(m-r)} /
              ((3r-1)!(3(m-r)-1)!)`   (`eq:C-def`)

is the degree-`m` coefficient of `F_f(u;x)F_f(v;x)`.

The bridge `C_schur_of_kernel` states `prop:C-schur`: at fixed parameter sum,
smaller imbalance gives the larger value of `C_{m,f}`.  Its proof in the paper is
the beta-binomial representation `eq:C-beta` (`C_{m,f} = Λ(s)·𝔼 G_{m,w}(P)`,
`P ∼ Beta(u,v)`) followed by the likelihood-ratio order of `lem:beta-order` — the
measure-theoretic content Mathlib does not readily support.  It is stated to
**consume** the proven kernel monotonicity as an explicit hypothesis `hker`, so
the only bridged content is `eq:C-beta` + `lem:beta-order`.

Uses the documented bridge `C_schur_of_kernel` and, transitively, the §4 bridges.
-/
import CubicPochhammer.Kernel

open scoped BigOperators

namespace CubicPochhammer

/-- The Pochhammer symbol `(u)_k = u(u+1)⋯(u+k-1)` for real `u`. -/
noncomputable def poch (u : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (u + (i : ℝ))

/-- The degree-`m` coefficient of `F_f(u;x) F_f(v;x)` (`eq:C-def`):
`C_{m,f}(u,v) = ∑_{r=1}^{m-1} f_r f_{m-r} (u)_{3r}(v)_{3(m-r)} /
              ((3r-1)!(3(m-r)-1)!)`. -/
noncomputable def Cmf (f : ℕ → ℝ) (m : ℕ) (u v : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (m - 1),
    f r * f (m - r) * (poch u (3 * r) * poch v (3 * (m - r)))
      / ((Nat.factorial (3 * r - 1) : ℝ) * (Nat.factorial (3 * (m - r) - 1) : ℝ))

/-- **Bridge — Schur-concavity of the coefficient convolution** (`prop:C-schur`,
via `eq:C-beta` + `lem:beta-order`).  For nonnegative `f` whose symmetric weights
`w_r = f_r f_{m-r}` give a nondecreasing (hence monotone kernel `hker`)
configuration, `C_{m,f}` is Schur-concave: at fixed parameter sum, a smaller
imbalance yields the larger value.

The hypothesis `hker` is exactly the proven `Kernel.Jmw_nonneg`; the axiom
encapsulates only the beta-binomial representation and the likelihood-ratio /
stochastic order of `lem:beta-order`. -/
axiom C_schur_of_kernel (f : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hfnn : ∀ r, 0 ≤ f r)
    (hker : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ Jmw m (fun r => f r * f (m - r)) t)
    (u1 v1 u2 v2 : ℝ)
    (hu1 : 0 < u1) (hv1 : 0 < v1) (hu2 : 0 < u2) (hv2 : 0 < v2)
    (hsum : u1 + v1 = u2 + v2) (himb : |u1 - v1| ≤ |u2 - v2|) :
    Cmf f m u2 v2 ≤ Cmf f m u1 v1

end CubicPochhammer
