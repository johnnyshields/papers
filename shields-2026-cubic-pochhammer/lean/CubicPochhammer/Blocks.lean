/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Bernstein
import CubicPochhammer.Weighting

/-!
# The paired blocks `B_{m,k}` and their single sign change

Formalizes `shields-2026-cubic-pochhammer.tex`,
`subsec:insertion-monotone-weights` «Insertion of monotone weights», inside
`sec:kernel` «The cubic residue kernel»: `eq:B-def`–`eq:B-center`,
`eq:H-hyperbolic` and `lem:block-sign`.

The summands of `J_m` (`eq:J-k`) are paired `k ↔ m-k` into blocks

  `B_{m,k}(t) = A_{m,k}(t) + A_{m,m-k}(t)`   (`eq:B-def`),

the partner term being dropped at the center `k = m-k` (`eq:B-center`).  Two
things are proven here: the pairing is a reindexing, so the block sum reproduces
`J_{m,w}` for symmetric weights and `J_m` for constant ones; and the block
sequence `B_{m,1},…,B_{m,⌊m/2⌋}` has at most one sign change, from nonpositive
to nonnegative (`lem:block-sign`).

The sign change is **rational**, not hyperbolic.  The first line of
`eq:H-hyperbolic` factors the block as

  `B_{m,k}(t) = C(3m-2,3k-1) · t^{3k-1} · H(m,d;t)/2`,
  `H(m,d;t) = m(1-t)(1+t^{3d}) - d(1+t)(1-t^{3d})`,   `d = m-2k`,

and the paper's `d ↦ d·tanh(3dz/2)` monotonicity is, before the substitution
`t = e^{-z}`, the statement that `d ↦ d(1-t^{3d})/(1+t^{3d})` is nondecreasing —
a product of two nonnegative nondecreasing factors of `d`.  No transcendental
substrate is needed: `Real.tanh` never appears.

Sorry-free, no project axioms.

## Main definitions

* `aterm` --- the `k`-th summand of `J_m` (`eq:J-k`).
* `bblock` --- the paired block `B_{m,k} = A_k + A_{m-k}` (`eq:B-def`), the
  partner term dropped at the center (`eq:B-center`).
* `hgap` --- `H(m,d;t)` of `eq:H-hyperbolic`, the block stripped of its positive
  factor and read as a function of the gap `d = m-2k`.

## Main statements

* `sum_blocks_eq_jm`, `sum_weighted_aterm_eq_blocks` --- the pairing is a
  reindexing, so the block sum reproduces `J_{m,w}` for symmetric weights and
  `J_m` for constant ones.  The reindexing itself is
  `Weighting.sum_weighted_eq_pairs`, which sees no multiplicity.
* `bblock_eq_hgap` --- the factorization `B_{m,k} = C(3m-2,3k-1) t^{3k-1} H/2`.
* `mono_ratio`, `hgap_bracket_nonpos_of_le`, `hgap_nonpos_of_le` ---
  `d ↦ d(1-t^{3d})/(1+t^{3d})` is nondecreasing, so the bracket's sign is
  monotone in the gap.  The first two are stated at free exponents and free of
  the multiplicity, and `Multiplicity/OrderTwo` reads them at `r = 2`.
* `hgap_one_bracket_pos` --- the paper's `tanh(3y) < 3 tanh y`, as the
  polynomial inequality `m(1+t³) > 1+2t+2t²+t³` for `m ≥ 3`.
* `block_sign_change` --- `lem:block-sign`: `B_{m,1},…,B_{m,⌊m/2⌋}` changes sign
  at most once, from nonpositive to nonnegative.  The bookkeeping — a maximal
  nonpositive index, and downward closure below it — is
  `Weighting.sign_change_of_stepDown`; what is proved here is the propagation
  step and the positivity of the last block.

## References

* `shields-2026-cubic-pochhammer.tex`, `subsec:insertion-monotone-weights`
  «Insertion of monotone weights», inside `sec:kernel` «The cubic residue
  kernel»: `lem:block-sign`, `eq:B-def`, `eq:B-center`, `eq:H-hyperbolic`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-- The `r`-th summand of `J_m` (`eq:J-k`), `n = 3m-2`. -/
noncomputable def aterm (m r : ℕ) (t : ℝ) : ℝ :=
  (Nat.choose (3 * m - 2) (3 * r - 1) : ℝ) * t ^ (3 * r - 1) * ((r : ℝ) - ((m : ℝ) - (r : ℝ)) * t)

/-- `J_m` is the constant-weight sum of `aterm` (definitional agreement with
`Bernstein.jm`). -/
theorem jm_eq_sum_aterm (m : ℕ) (t : ℝ) :
    jm m t = ∑ r ∈ Finset.Icc 1 (m - 1), aterm m r t := rfl

/-- The paired block `B_{m,k} = A_k + A_{m-k}` (`eq:B-def`); at the center
`r = m-r` the partner term is dropped so the block is the single central term
`eq:B-center`. -/
noncomputable def bblock (m r : ℕ) (t : ℝ) : ℝ :=
  aterm m r t + (if r = m - r then 0 else aterm m (m - r) t)

/-! ### The pairing is a reindexing -/

/-- The two binomial coefficients in a block coincide: with `n = rm-2`,
`n - (rk-1) = r(m-k)-1`.  Stated at every multiplicity, since the identity is
the residue bookkeeping and nothing else — `Multiplicity/OrderTwo` reads it at
`r = 2`. -/
theorem choose_block_symm {r m k : ℕ} (hr : 1 ≤ r) (hk1 : 1 ≤ k) (hk2 : k ≤ m - 1) :
    Nat.choose (r * m - 2) (r * k - 1) = Nat.choose (r * m - 2) (r * (m - k) - 1) := by
  have hm : 2 ≤ m := by omega
  have hsplit : r * k + r * (m - k) = r * m := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' (by omega : k ≤ m)]
  have hrk : 1 ≤ r * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hrmk : 1 ≤ r * (m - k) := Nat.one_le_iff_ne_zero.mpr (by
    have : 0 < m - k := by omega
    positivity)
  rw [show r * (m - k) - 1 = (r * m - 2) - (r * k - 1) from by omega,
    Nat.choose_symm (by omega)]

/-- **The pairing identity** (`eq:B-def`).  For weights symmetric under
`k ↔ m-k`, the weighted sum over `Icc 1 (m-1)` collapses onto the blocks.
Symmetry is what makes this valid: without it the block sum would weight
`A_{m-k}` by `w_k` rather than `w_{m-k}`.

The reindexing itself sees no multiplicity, so it is
`Weighting.sum_weighted_eq_pairs`; here it is read at the terms `aterm`, whose
pairing is `bblock` by definition. -/
theorem sum_weighted_aterm_eq_blocks (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) (t : ℝ) :
    ∑ r ∈ Finset.Icc 1 (m - 1), w r * aterm m r t
      = ∑ k ∈ Finset.range (m / 2), w (k + 1) * bblock m (k + 1) t :=
  sum_weighted_eq_pairs w (fun r => aterm m r t) hm hsym

/-- The block sum reproduces `J_m` (`eq:B-def` at constant weights). -/
theorem sum_blocks_eq_jm {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    ∑ k ∈ Finset.range (m / 2), bblock m (k + 1) t = jm m t := by
  have h := sum_weighted_aterm_eq_blocks (fun _ => (1 : ℝ)) hm (fun _ _ _ => rfl) t
  simp only [one_mul] at h
  rw [jm_eq_sum_aterm, h]

/-! ### The single sign change -/

/-- `H(m,d;t)` (`eq:H-hyperbolic`, first line): the block stripped of its
positive factor, as a function of the gap `d = m-2k`. -/
noncomputable def hgap (m d : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) * (1 - t) * (1 + t ^ (3 * d)) - (d : ℝ) * (1 + t) * (1 - t ^ (3 * d))

/-- **The center block is positive** (`eq:B-center`).  At `2k = m` the partner
term is dropped and the block is `C·t^{3k-1}·k(1-t)`. -/
theorem bblock_center_pos {m k : ℕ} (hk1 : 1 ≤ k) (hcen : 2 * k = m) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : 0 < bblock m k t := by
  have hmk : m - k = k := by omega
  have hcast : ((m : ℝ) - (k : ℝ)) = (k : ℝ) := by
    have hm2 : (m : ℝ) = 2 * (k : ℝ) := by
      rw [← hcen]; push_cast; ring
    rw [hm2]; ring
  unfold bblock aterm
  rw [if_pos hmk.symm, add_zero, hcast,
    show (k : ℝ) - (k : ℝ) * t = (k : ℝ) * (1 - t) by ring]
  have hC : (0 : ℝ) < (Nat.choose (3 * m - 2) (3 * k - 1) : ℝ) := by
    have : 0 < Nat.choose (3 * m - 2) (3 * k - 1) := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  exact mul_pos (mul_pos hC (pow_pos ht0 _)) (mul_pos hk (by linarith))

/-- **The block closed form** (`eq:H-hyperbolic`, first line).  Off the center,
`B_{m,k} = C(3m-2,3k-1)·t^{3k-1}·H(m,m-2k;t)/2`.  The two binomials coincide by
`choose_block_symm`, and the partner power factors as `t^{3k-1}·t^{3d}`. -/
theorem bblock_eq_hgap {m k : ℕ} (hk1 : 1 ≤ k) (hcen : 2 * k < m) (t : ℝ) :
    bblock m k t
      = (Nat.choose (3 * m - 2) (3 * k - 1) : ℝ) * t ^ (3 * k - 1)
          * hgap m (m - 2 * k) t / 2 := by
  have hmk : ¬ (k = m - k) := by omega
  have hpow : 3 * (m - k) - 1 = (3 * k - 1) + 3 * (m - 2 * k) := by omega
  have hCsym : Nat.choose (3 * m - 2) (3 * (m - k) - 1)
      = Nat.choose (3 * m - 2) (3 * k - 1) :=
    (choose_block_symm (r := 3) (m := m) (k := k) (by norm_num) hk1 (by omega)).symm
  have hck : (((m - k : ℕ)) : ℝ) = (m : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by omega)
  have hcd : (((m - 2 * k : ℕ)) : ℝ) = (m : ℝ) - 2 * (k : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  unfold bblock aterm hgap
  rw [if_neg hmk, hCsym, hpow, pow_add, hck, hcd]
  ring

/-- The monotonicity behind `lem:block-sign`, before the substitution
`t = e^{-z}`: for `a ≤ b`, `p ≤ q` and `0 < t < 1`,

  `a(1-t^p)(1+t^q) ≤ b(1-t^q)(1+t^p)`,

which is `a(1-t^p)/(1+t^p) ≤ b(1-t^q)/(1+t^q)` cleared of denominators.  Each of
the two grouped factors on the left is nonnegative and bounded by its
counterpart on the right.

The exponents are free of the index, so the same lemma serves every
multiplicity: at `r` the caller takes `p = ra`, `q = rb`. -/
theorem mono_ratio {a b p q : ℕ} (hab : a ≤ b) (hpq : p ≤ q) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    (a : ℝ) * (1 - t ^ p) * (1 + t ^ q) ≤ (b : ℝ) * (1 - t ^ q) * (1 + t ^ p) := by
  have hba : t ^ q ≤ t ^ p := pow_le_pow_of_le_one ht0.le ht1.le hpq
  have ha1 : t ^ p ≤ 1 := pow_le_one₀ ht0.le ht1.le
  have hb1 : t ^ q ≤ 1 := pow_le_one₀ ht0.le ht1.le
  have hapos : (0 : ℝ) < t ^ p := pow_pos ht0 _
  have hbpos : (0 : ℝ) < t ^ q := pow_pos ht0 _
  have hac : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hann : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hnum : (a : ℝ) * (1 - t ^ p) ≤ (b : ℝ) * (1 - t ^ q) :=
    mul_le_mul hac (by linarith) (by linarith) (by linarith)
  have hden : (1 : ℝ) + t ^ q ≤ 1 + t ^ p := by linarith
  exact mul_le_mul hnum hden (by linarith) (by nlinarith)

/-- **The bracket of `eq:H-hyperbolic` is nonpositive at every larger gap**, on
the unfolded form so that it serves every multiplicity.  Multiply the hypothesis
by `1+t^q > 0`, chain through `mono_ratio`, and cancel `1+t^p > 0`. -/
theorem hgap_bracket_nonpos_of_le {m a b p q : ℕ} (hab : a ≤ b) (hpq : p ≤ q)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h : (m : ℝ) * (1 - t) * (1 + t ^ p) - (a : ℝ) * (1 + t) * (1 - t ^ p) ≤ 0) :
    (m : ℝ) * (1 - t) * (1 + t ^ q) - (b : ℝ) * (1 + t) * (1 - t ^ q) ≤ 0 := by
  have hA : (0 : ℝ) < 1 + t ^ p := by positivity
  have hB : (0 : ℝ) < 1 + t ^ q := by positivity
  have hS : (0 : ℝ) < 1 + t := by linarith
  have hkey := mono_ratio hab hpq ht0 ht1
  have hgapA : (m : ℝ) * (1 - t) * (1 + t ^ p) ≤ (a : ℝ) * (1 + t) * (1 - t ^ p) := by linarith
  have hgapA_mulB : ((m : ℝ) * (1 - t) * (1 + t ^ p)) * (1 + t ^ q)
      ≤ ((a : ℝ) * (1 + t) * (1 - t ^ p)) * (1 + t ^ q) :=
    mul_le_mul_of_nonneg_right hgapA hB.le
  have hratio_mulS : ((a : ℝ) * (1 - t ^ p) * (1 + t ^ q)) * (1 + t)
      ≤ ((b : ℝ) * (1 - t ^ q) * (1 + t ^ p)) * (1 + t) :=
    mul_le_mul_of_nonneg_right hkey hS.le
  have hgapB_mulA : ((m : ℝ) * (1 - t) * (1 + t ^ q)) * (1 + t ^ p)
      ≤ ((b : ℝ) * (1 + t) * (1 - t ^ q)) * (1 + t ^ p) := by
    nlinarith [hgapA_mulB, hratio_mulS]
  have hgapB : (m : ℝ) * (1 - t) * (1 + t ^ q) ≤ (b : ℝ) * (1 + t) * (1 - t ^ q) :=
    le_of_mul_le_mul_right hgapB_mulA hA
  linarith

/-- **`H` is nonpositive at every larger gap** (`lem:block-sign`), which is
`hgap_bracket_nonpos_of_le` read at the exponents `3a`, `3b`. -/
theorem hgap_nonpos_of_le {m a b : ℕ} (hab : a ≤ b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h : hgap m a t ≤ 0) : hgap m b t ≤ 0 := by
  unfold hgap at h ⊢
  exact hgap_bracket_nonpos_of_le hab (by omega) ht0 ht1 h

/-- **Downward propagation of nonpositivity** (`lem:block-sign`).  If a block is
nonpositive, so is its predecessor: decreasing `k` by one raises the gap
`d = m-2k` by two, and `hgap_nonpos_of_le` makes the bracket of
`eq:H-hyperbolic` only more negative. -/
theorem bblock_nonpos_of_succ {m k : ℕ} (hk1 : 1 ≤ k) (hsucc : k + 1 ≤ m / 2) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : bblock m (k + 1) t ≤ 0) :
    bblock m k t ≤ 0 := by
  -- `k+1` cannot be the center: the center block is positive
  have hcen : 2 * (k + 1) < m := by
    rcases lt_or_eq_of_le (show 2 * (k + 1) ≤ m by omega) with h' | h'
    · exact h'
    · exact absurd h (not_le.mpr (bblock_center_pos (by omega) h' ht0 ht1))
  have hk : 2 * k < m := by omega
  have hCs : (0 : ℝ) < (Nat.choose (3 * m - 2) (3 * (k + 1) - 1) : ℝ) := by
    have : 0 < Nat.choose (3 * m - 2) (3 * (k + 1) - 1) := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hCk : (0 : ℝ) < (Nat.choose (3 * m - 2) (3 * k - 1) : ℝ) := by
    have : 0 < Nat.choose (3 * m - 2) (3 * k - 1) := Nat.choose_pos (by omega)
    exact_mod_cast this
  rw [bblock_eq_hgap (m := m) (k := k + 1) (by omega) hcen t] at h
  have hH1 : hgap m (m - 2 * (k + 1)) t ≤ 0 := by
    by_contra! hpos
    have hp : (0 : ℝ) < t ^ (3 * (k + 1) - 1) := pow_pos ht0 _
    have : (0 : ℝ) < (Nat.choose (3 * m - 2) (3 * (k + 1) - 1) : ℝ)
        * t ^ (3 * (k + 1) - 1) * hgap m (m - 2 * (k + 1)) t / 2 :=
      div_pos (mul_pos (mul_pos hCs hp) hpos) two_pos
    linarith
  have hH0 : hgap m (m - 2 * k) t ≤ 0 :=
    hgap_nonpos_of_le (by omega) ht0 ht1 hH1
  rw [bblock_eq_hgap (m := m) (k := k) hk1 hk t]
  have hnp : (Nat.choose (3 * m - 2) (3 * k - 1) : ℝ) * t ^ (3 * k - 1)
      * hgap m (m - 2 * k) t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (by positivity) hH0
  linarith

/-- **The gap-one bracket is positive**: for `m ≥ 3` and `0 < t < 1`,

  `m(1+t³) > 1 + 2t + 2t² + t³`.

This is the paper's `tanh(3y) < 3 tanh y` with the transcendental removed.  The
right-hand side is `(1+t)(1+t+t²)`, so the claim is `m(1+t³) > (1+t)(1+t+t²)`,
and it follows from `1 + t³ > t + t²` on `(0,1)` — the elementary
`(1-t)²(1+t) > 0` — together with `m ≥ 3`. -/
theorem hgap_one_bracket_pos {m : ℕ} (hm : 3 ≤ m) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < (m : ℝ) * (1 + t ^ 3) - (1 + 2 * t + 2 * t ^ 2 + t ^ 3) := by
  have hmc : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsubt : (0 : ℝ) < 1 - t := by linarith
  have hcube : (0 : ℝ) < 1 + t ^ 3 := by positivity
  have hbase : (0 : ℝ) < 1 + t ^ 3 - t - t ^ 2 := by
    nlinarith [mul_pos (mul_pos hsubt hsubt) (show (0 : ℝ) < 1 + t by linarith)]
  nlinarith [hbase, mul_le_mul_of_nonneg_right hmc hcube.le]

/-- **The final block is positive** (`lem:block-sign`, last clause).  For even
`m` the top block `k = m/2` is the center (`eq:B-center`); for odd `m` it has
gap `d = 1`, where

  `H(m,1;t) = (1-t)·[m(1+t³) - (1+2t+2t²+t³)] > 0`   for `m ≥ 3`,

since `1+t³ > t+t²` on `(0,1)` — the elementary `(1-t)(1-t²) > 0`.  This is the
paper's `tanh(3y) < 3 tanh y`, again without the transcendental. -/
theorem bblock_top_pos {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < bblock m (m / 2) t := by
  have hk1 : 1 ≤ m / 2 := by omega
  rcases Nat.even_or_odd m with he | ho
  · -- even `m`: the top block is the center block
    obtain ⟨j, hj⟩ := he
    exact bblock_center_pos hk1 (by omega) ht0 ht1
  · -- odd `m`: gap one, and `m ≥ 3`
    obtain ⟨j, hj⟩ := ho
    have hm3 : 3 ≤ m := by omega
    have hcen : 2 * (m / 2) < m := by omega
    have hcenterGap : m - 2 * (m / 2) = 1 := by omega
    have hC : (0 : ℝ) < (Nat.choose (3 * m - 2) (3 * (m / 2) - 1) : ℝ) := by
      have : 0 < Nat.choose (3 * m - 2) (3 * (m / 2) - 1) := Nat.choose_pos (by omega)
      exact_mod_cast this
    rw [bblock_eq_hgap hk1 hcen t, hcenterGap]
    have hsubt : (0 : ℝ) < 1 - t := by linarith
    have hkey := hgap_one_bracket_pos hm3 ht0 ht1
    have hH : 0 < hgap m 1 t := by
      unfold hgap
      norm_num
      nlinarith [mul_pos hsubt hkey]
    exact div_pos (mul_pos (mul_pos hC (pow_pos ht0 _)) hH) two_pos

/-- **`lem:block-sign`** in the form the weighting principle consumes: the block
sequence `B_{m,1},…,B_{m,⌊m/2⌋}` is nonpositive up to some index and nonnegative
after it, or nonnegative throughout.

The pivot is the largest index carrying a nonpositive block.  Below it every
block is nonpositive by `bblock_nonpos_of_succ`; above it none is, by
maximality.  The pivot block `B_{m,q+1}` is never the final one: that block is
positive (`bblock_top_pos`), which is why the first disjunct carries
`q + 1 < ⌊m/2⌋` rather than `q < ⌊m/2⌋`. -/
theorem block_sign_change {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∃ q, q + 1 < m / 2
        ∧ (∀ k, k ≤ q → bblock m (k + 1) t ≤ 0)
        ∧ (∀ k, q < k → k < m / 2 → 0 ≤ bblock m (k + 1) t))
      ∨ (∀ k, k < m / 2 → 0 ≤ bblock m (k + 1) t) := by
  have hL : 1 ≤ m / 2 := by omega
  refine sign_change_of_stepDown (B := fun k => bblock m (k + 1) t)
    (fun j hj h => bblock_nonpos_of_succ (by omega) (by omega) ht0 ht1 h) hL ?_
  dsimp only
  rw [show m / 2 - 1 + 1 = m / 2 from by omega]
  exact bblock_top_pos hm ht0 ht1

end CubicPochhammer
