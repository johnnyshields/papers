/-
# The weighted cubic residue kernel: `J_{m,w}(t) ≥ 0`

Formalizes `shields-2026-cubic-pochhammer.tex`, §4 «The cubic residue
kernel» (`sec:kernel`), `thm:kernel` (weighted cubic residue monotonicity) at
the level of its analytic content, the derivative numerator

  `J_{m,w}(t) = ∑_{k=1}^{m-1} w_k C(3m-2,3k-1) t^{3k-1} (k - (m-k) t)`   (`eq:Jw-def`),

which is `≥ 0` on `(0,1)` whenever the symmetric weights increase toward the
centre.  By `eq:J-weighted` this is exactly the statement that `G_{m,w}` is
nondecreasing on `[0,1/2]`.

The proof pairs the terms `k ↔ m-k` into blocks `B_{m,k}` (`eq:B-def`); the
block sequence has a single sign change (`lem:block-sign`) and sums to `J_m > 0`
(`Bernstein.Jm_pos`, proven).  The **proven** one-sign-change weighting principle
`sum_weighted_nonneg` (`Weighting.lean`) then carries positivity through the
nondecreasing weights.

The pairing decomposition (`eq:B-def`, algebraic reindexing) and the single
sign change (`lem:block-sign`, a `tanh` monotonicity: `d ↦ d·tanh(3dx/2)` is
increasing) are the §4.2 content packaged in the documented bridge
`block_certificate`.  Everything transferring them to the weighted kernel —
the weighting principle and the constant-weight positivity `J_m > 0` — is proven.

Sorry-free.  Uses `block_certificate` (§4.2) and, transitively, `Jm_bernstein`.
-/
import CubicPochhammer.Bernstein
import CubicPochhammer.Weighting

open scoped BigOperators

namespace CubicPochhammer

/-- The `k`-th summand of `J_m` (`eq:J-r`), `n = 3m-2`. -/
noncomputable def Aterm (m r : ℕ) (t : ℝ) : ℝ :=
  (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * t ^ (3 * r - 1) * ((r : ℝ) - ((m : ℝ) - (r : ℝ)) * t)

/-- `J_m` is the constant-weight sum of `Aterm` (definitional agreement with
`Bernstein.Jm`). -/
theorem Jm_eq_sum_Aterm (m : ℕ) (t : ℝ) :
    Jm m t = ∑ r ∈ Finset.Icc 1 (m - 1), Aterm m r t := rfl

/-- The weighted cubic residue kernel's derivative numerator `J_{m,w}`
(`eq:Jw-def`). -/
noncomputable def Jmw (m : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (m - 1), w r * Aterm m r t

/-- The paired block `B_{m,k} = A_k + A_{m-k}` (`eq:B-def`); at the centre
`r = m-r` the partner term is dropped so the block is the single central term
`eq:B-center`. -/
noncomputable def Bblock (m r : ℕ) (t : ℝ) : ℝ :=
  Aterm m r t + (if r = m - r then 0 else Aterm m (m - r) t)

/-- **Bridge — block decomposition and single sign change** (`eq:B-def`,
`lem:block-sign`).  Pairing `r ↔ m-r` rewrites both `J_{m,w}` and `J_m` over the
blocks `B_{m,k}`, `1 ≤ k ≤ ⌊m/2⌋`, and that block sequence has at most one sign
change, from nonpositive to nonnegative.  The pairing is an algebraic
reindexing; the sign change is the `tanh` monotonicity of `lem:block-sign`.  Both
are §4.2 content; the weighting transfer below is proven.  The pairing is valid
only for symmetric weights `w_k = w_{m-k}` (hypothesis `hsym`), which is the
setting of `thm:kernel`; without it the block sum weights `A_{m-k}` by `w_k`
rather than `w_{m-k}`, so the identity fails. -/
axiom block_certificate (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (w : ℕ → ℝ)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) :
    (∑ r ∈ Finset.Icc 1 (m - 1), w r * Aterm m r t
       = ∑ k ∈ Finset.range (m / 2), w (k + 1) * Bblock m (k + 1) t)
    ∧ (∑ k ∈ Finset.range (m / 2), Bblock m (k + 1) t = Jm m t)
    ∧ ((∃ q, q < m / 2
          ∧ (∀ k, k ≤ q → Bblock m (k + 1) t ≤ 0)
          ∧ (∀ k, q < k → k < m / 2 → 0 ≤ Bblock m (k + 1) t))
       ∨ (∀ k, k < m / 2 → 0 ≤ Bblock m (k + 1) t))

/-- **Weighted cubic residue monotonicity** (`thm:kernel`, analytic content):
for symmetric weights nondecreasing toward the centre, `J_{m,w}(t) ≥ 0` on
`(0,1)`; equivalently (`eq:J-weighted`) `G_{m,w}` is nondecreasing on `[0,1/2]`.

The one-sign-change weighting principle `sum_weighted_nonneg` transfers the
constant-weight positivity `∑ B_{m,k} = J_m > 0` through the nondecreasing
weights. -/
theorem Jmw_nonneg (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hwnn : ∀ i, 1 ≤ i → i ≤ m / 2 → 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ Jmw m w t := by
  obtain ⟨hrepr, hsum, hsign⟩ := block_certificate m hm t ht0 ht1 w hsym
  unfold Jmw
  rw [hrepr]
  have hsum_pos : 0 ≤ ∑ k ∈ Finset.range (m / 2), Bblock m (k + 1) t := by
    rw [hsum]; exact (Jm_pos m hm t ht0 ht1).le
  rcases hsign with ⟨q, hq, hle, hge⟩ | hall
  · exact sum_weighted_nonneg (fun k => w (k + 1)) (fun k => Bblock m (k + 1) t) (m / 2)
      (fun i j hij hjn => hwmono (i + 1) (j + 1) (by omega) (by omega) (by omega))
      (fun k hk => hwnn (k + 1) (by omega) (by omega))
      q hq hle (fun k hqk hkn => hge k hqk hkn) hsum_pos
  · refine Finset.sum_nonneg fun k hk => ?_
    have hk' : k < m / 2 := Finset.mem_range.mp hk
    exact mul_nonneg (hwnn (k + 1) (by omega) (by omega)) (hall k hk')

end CubicPochhammer
