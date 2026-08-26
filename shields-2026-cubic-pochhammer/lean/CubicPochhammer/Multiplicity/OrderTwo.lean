/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Multiplicity.GeneralOrder
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Multiplicity two: the derivative numerator and the kernel

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp
multiplicity threshold», the `r = 2` half of `prop:multiplicity-threshold`:
`thm:kernel` re-proved at multiplicity two, up to monotonicity of the kernel
on `[0,1/2]`.

`sec:kernel` proves `thm:kernel` at `r = 3`, where the certificate sum
`eq:S-def` needs the period-6 residue table of `ResidueSums` and a six-way case
split (`Snj.snj_nonneg`).  At `r = 2` the residue class is `k` odd, the class
sums are `2^{j-1}` with no correction term, and the derivative numerator has a
closed form — so no Bernstein certificate is needed and positivity follows from
Bernoulli's inequality.  Everything downstream of the numerator then repeats
the cubic argument with `3` replaced by `2`.

## Main definitions

* `oddPow`, `evenPow`, `oddPowW` --- the odd and even parts of `(1+t)^n` and
  the index-weighted odd part, which is what the `r = 2` numerator is built from.
* `aterm2`, `jm2` --- the summand and the constant-weight derivative numerator,
  the `r = 2` analogues of `Blocks.aterm` and `Bernstein.jm`.
* `bblock2`, `hgap2` --- the paired block of `eq:B-def` and its bracket, at
  multiplicity two.
* `jmw2`, `gmw2`, `gmwNum2` --- the weighted numerator, the kernel, and the
  kernel's numerator after the projective substitution `p = t/(1+t)`.

## Main statements

* `jm2_closed`, `jm2_pos` --- the closed form of the constant-weight numerator,
  and its positivity on `(0,1)`; this is where the `r = 2` route is shorter
  than the cubic one.
* `sign_change_of_stepDown` --- the single sign change, for an abstract
  sequence: downward propagation plus a positive last entry.
* `jmw2_nonneg` --- the weighted numerator is nonnegative for symmetric weights
  increasing toward the center.
* `gmw2_monotoneOn` --- `thm:kernel` at `r = 2`.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp multiplicity
  threshold», and `sec:kernel` «The cubic residue kernel» for the statements
  this module re-proves at `r = 2`: `thm:kernel`, `eq:B-def`,
  `eq:H-hyperbolic`, `eq:G-weighted`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-! ### The quadratic multiplicity `r = 2`: the constant-weight numerator

`sec:kernel` proves `thm:kernel` at `r = 3`, where the certificate sum
`eq:S-def` needs the period-6 residue table of `ResidueSums` and a six-way case
split (`Snj.snj_nonneg`).  At `r = 2` the residue class is `k` odd, the
class sums are `2^{j-1}` with no correction term, and the derivative numerator
has a closed form — so the Bernstein certificate is not needed at all and
positivity follows from Bernoulli's inequality.
-/

/-- The odd part of `(1+t)^n`. -/
noncomputable def oddPow (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1), (Nat.choose n i : ℝ) * t ^ i

/-- The even part of `(1+t)^n`. -/
noncomputable def evenPow (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 0), (Nat.choose n i : ℝ) * t ^ i

/-- The index-weighted odd part, `∑_{i odd} i C(n,i) tⁱ`. -/
noncomputable def oddPowW (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
    (Nat.choose n i : ℝ) * (i : ℝ) * t ^ i

theorem binom_expand (n : ℕ) (t : ℝ) :
    (1 + t) ^ n = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * t ^ i := by
  rw [add_comm, add_pow]
  exact Finset.sum_congr rfl fun i _ => by rw [one_pow]; ring

theorem binom_expand_neg (n : ℕ) (t : ℝ) :
    (1 - t) ^ n = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * (-t) ^ i := by
  rw [show (1 : ℝ) - t = -t + 1 from by ring, add_pow]
  exact Finset.sum_congr rfl fun i _ => by rw [one_pow]; ring

/-- `2 ∑_{i odd} C(n,i) tⁱ = (1+t)ⁿ - (1-t)ⁿ`. -/
theorem oddPow_closed (n : ℕ) (t : ℝ) : 2 * oddPow n t = (1 + t) ^ n - (1 - t) ^ n := by
  rw [binom_expand, binom_expand_neg, ← Finset.sum_sub_distrib, oddPow, Finset.sum_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.even_or_odd i with he | ho
  · have heven : i % 2 = 0 := Nat.even_iff.mp he
    rw [if_neg (by omega : ¬ i % 2 = 1), he.neg_pow]
    ring
  · rw [if_pos (Nat.odd_iff.mp ho), ho.neg_pow]
    ring

/-- `2 ∑_{i even} C(n,i) tⁱ = (1+t)ⁿ + (1-t)ⁿ`. -/
theorem evenPow_closed (n : ℕ) (t : ℝ) : 2 * evenPow n t = (1 + t) ^ n + (1 - t) ^ n := by
  rw [binom_expand, binom_expand_neg, ← Finset.sum_add_distrib, evenPow, Finset.sum_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.even_or_odd i with he | ho
  · rw [if_pos (Nat.even_iff.mp he), he.neg_pow]
    ring
  · have hodd : i % 2 = 1 := Nat.odd_iff.mp ho
    rw [if_neg (by omega : ¬ i % 2 = 0), ho.neg_pow]
    ring

/-- `∑_{i odd} i C(n,i) tⁱ = n t ∑_{l even} C(n-1,l) tˡ`, by `i C(n,i) = n C(n-1,i-1)`
and the parity flip in the shift. -/
theorem oddPowW_eq (N : ℕ) (t : ℝ) :
    oddPowW (N + 1) t = ((N : ℝ) + 1) * t * evenPow N t := by
  rw [oddPowW, evenPow, Finset.mul_sum]
  refine Finset.sum_nbij' (fun i => i - 1) (fun l => l + 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_range] at h1
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro l hl
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hl
    rw [Finset.mem_range] at h1
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_range] at h1
    dsimp only; omega
  · intro l hl
    dsimp only; omega
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_range] at h1
    dsimp only
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
    have hch : (Nat.choose (N + 1) (l + 1) : ℝ) * ((l : ℝ) + 1)
        = ((N : ℝ) + 1) * (Nat.choose N l : ℝ) := by
      have h' : ((N + 1) * Nat.choose N l : ℕ) = (Nat.choose (N + 1) (l + 1) * (l + 1) : ℕ) :=
        Nat.add_one_mul_choose_eq N l
      have := congrArg (fun x : ℕ => (x : ℝ)) h'
      push_cast at this
      linarith
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    linear_combination (t ^ l * t) * hch

/-- The `k`-th summand of the `r = 2` derivative numerator, `n = 2m-2`; the
`r = 2` analogue of `Blocks.aterm`. -/
noncomputable def aterm2 (m k : ℕ) (t : ℝ) : ℝ :=
  (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ) * t ^ (2 * k - 1)
    * ((k : ℝ) - ((m : ℝ) - (k : ℝ)) * t)

/-- The constant-weight `r = 2` derivative numerator, the analogue of
`Bernstein.jm`. -/
noncomputable def jm2 (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 (m - 1), aterm2 m k t

/-- Reindexing `J^{(2)}_m` by `ν = 2k-1`: with `n = 2m-2`, the summand becomes
`C(n,ν)tᵛ((ν+1) - (n+1-ν)t)`, which splits into the two odd-part sums. -/
theorem jm2_eq_odd (M : ℕ) (t : ℝ) :
    2 * jm2 (M + 2) t
      = oddPowW (2 * M + 2) t * (1 + t) + oddPow (2 * M + 2) t * (1 - (2 * (M : ℝ) + 3) * t) := by
  rw [jm2, Finset.mul_sum, oddPowW, oddPow, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  have hidx : 2 * (M + 2) - 2 = 2 * M + 2 := by omega
  refine Finset.sum_nbij' (fun k => 2 * k - 1) (fun ν => (ν + 1) / 2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro ν hν
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hν
    rw [Finset.mem_range] at h1
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    dsimp only; omega
  · intro ν hν
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hν
    rw [Finset.mem_range] at h1
    dsimp only; omega
  · intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    dsimp only
    rw [aterm2, hidx]
    have hc : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc]
    push_cast
    ring

/-- **The closed form of the `r = 2` constant-weight numerator.**  With
`m = M+2` and `n = 2M+2`,

  `4 J^{(2)}_m(t) = (1-t)(1+t)ⁿ - (1-t)^{n-1}(1 - (2n+2)t + t²)`.

The two odd-part sums recombine: the `(1+t)^{n-1}` coefficient is
`nt(1+t) + (1+t)(1-(n+1)t) = (1+t)(1-t)`, and the `(1-t)^{n-1}` coefficient is
`nt(1+t) - (1-t)(1-(n+1)t) = -(1-(2n+2)t+t²)`. -/
theorem jm2_closed (M : ℕ) (t : ℝ) :
    4 * jm2 (M + 2) t
      = (1 - t) * (1 + t) ^ (2 * M + 2)
        - (1 - t) ^ (2 * M + 1) * (1 - (4 * (M : ℝ) + 6) * t + t ^ 2) := by
  have hJ := jm2_eq_odd M t
  have hW : oddPowW (2 * M + 2) t = (2 * (M : ℝ) + 2) * t * evenPow (2 * M + 1) t := by
    have h := oddPowW_eq (2 * M + 1) t
    rw [show 2 * M + 1 + 1 = 2 * M + 2 from by omega] at h
    rw [h]
    push_cast
    ring
  have hE := evenPow_closed (2 * M + 1) t
  have hO := oddPow_closed (2 * M + 2) t
  have hp1 : (1 + t) ^ (2 * M + 2) = (1 + t) ^ (2 * M + 1) * (1 + t) := by rw [pow_succ]
  have hp2 : (1 - t) ^ (2 * M + 2) = (1 - t) ^ (2 * M + 1) * (1 - t) := by rw [pow_succ]
  rw [hW] at hJ
  rw [hp1, hp2] at hO
  rw [hp1]
  linear_combination 2 * hJ + (t * (2 * (M : ℝ) + 2) * (1 + t)) * hE
    + (1 - (2 * (M : ℝ) + 3) * t) * hO

/-- **`lem:bernstein` at `r = 2`**: the constant-weight numerator is strictly
positive on `(0,1)` for every `m ≥ 2`.

Two branches on the sign of `Q(t) = 1 - (2n+2)t + t²`.  Where `Q < 0` the
subtracted term is nonpositive.  Where `Q ≥ 0`, `(1-t)^{n-1} ≤ 1-t` and
Bernoulli's `(1+t)ⁿ ≥ 1 + nt > Q` close it.  No Bernstein certificate and no
residue table are involved, which is what separates `r = 2` from the critical
`r = 3`. -/
theorem jm2_pos (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : 0 < jm2 m t := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 2 := ⟨m - 2, by omega⟩
  have hsubt : (0 : ℝ) < 1 - t := by linarith
  have hclosed := jm2_closed M t
  set Qd : ℝ := 1 - (4 * (M : ℝ) + 6) * t + t ^ 2 with hQ
  have hbig : (0 : ℝ) < (1 - t) * (1 + t) ^ (2 * M + 2) := by positivity
  rcases le_or_gt 0 Qd with hq | hq
  · have hpow : (1 - t) ^ (2 * M + 1) ≤ 1 - t := by
      calc (1 - t) ^ (2 * M + 1) ≤ (1 - t) ^ 1 :=
            pow_le_pow_of_le_one hsubt.le (by linarith) (by omega)
        _ = 1 - t := pow_one _
    have hstep : (1 - t) ^ (2 * M + 1) * Qd ≤ (1 - t) * Qd :=
      mul_le_mul_of_nonneg_right hpow hq
    have hbern : (1 : ℝ) + (2 * (M : ℝ) + 2) * t ≤ (1 + t) ^ (2 * M + 2) := by
      have h := one_add_mul_le_pow (a := t) (by linarith) (2 * M + 2)
      push_cast at h
      linarith
    have hlt : Qd < (1 + t) ^ (2 * M + 2) := by
      have hqb : Qd < 1 + (2 * (M : ℝ) + 2) * t := by
        rw [hQ]; nlinarith [sq_nonneg t]
      linarith
    have : (1 - t) * Qd < (1 - t) * (1 + t) ^ (2 * M + 2) :=
      mul_lt_mul_of_pos_left hlt hsubt
    linarith
  · have hnp : (1 - t) ^ (2 * M + 1) * Qd ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hsubt.le _) hq.le
    linarith

/-! ### The quadratic multiplicity `r = 2`: monotone weights

`sec:kernel`'s passage from constant weights to the monotone-weight cone
(`eq:B-def`, `lem:block-sign`, `lem:weighting`) is structural: the pairing and
the single sign change use only that the two binomials in a block coincide and
that the gap `d = m-2k` grows as `k` decreases.  None of that sees the
multiplicity, so none of it is restated here.  The pairing is
`Weighting.sum_weighted_eq_pairs`, the sign change
`Weighting.sign_change_of_stepDown`, the weighting principle
`Weighting.sum_weighted_nonneg`, and the two facts behind the gap monotonicity
`Blocks.choose_block_symm` and `Blocks.hgap_bracket_nonpos_of_le`, all read at
`r = 2`.  What is `r = 2`'s own is below: the blocks `bblock2`, the bracket
`hgap2`, and the closed form of the constant-weight numerator.
-/

/-! ### The `r = 2` blocks -/

/-- The paired `r = 2` block, `eq:B-def` at multiplicity two. -/
noncomputable def bblock2 (m k : ℕ) (t : ℝ) : ℝ :=
  aterm2 m k t + (if k = m - k then 0 else aterm2 m (m - k) t)

/-- The `r = 2` block stripped of its positive factor, as a function of the gap
`d = m-2k`; `eq:H-hyperbolic` with `t^{3d}` replaced by `t^{2d}`. -/
noncomputable def hgap2 (m d : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) * (1 - t) * (1 + t ^ (2 * d)) - (d : ℝ) * (1 + t) * (1 - t ^ (2 * d))

theorem bblock2_center_pos {m k : ℕ} (hk1 : 1 ≤ k) (hcen : 2 * k = m) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : 0 < bblock2 m k t := by
  have hmk : m - k = k := by omega
  have hcast : ((m : ℝ) - (k : ℝ)) = (k : ℝ) := by
    have hm2 : (m : ℝ) = 2 * (k : ℝ) := by rw [← hcen]; push_cast; ring
    rw [hm2]; ring
  unfold bblock2 aterm2
  rw [if_pos hmk.symm, add_zero, hcast,
    show (k : ℝ) - (k : ℝ) * t = (k : ℝ) * (1 - t) by ring]
  have hC : (0 : ℝ) < (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ) := by
    have : 0 < Nat.choose (2 * m - 2) (2 * k - 1) := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  exact mul_pos (mul_pos hC (pow_pos ht0 _)) (mul_pos hk (by linarith))

theorem bblock2_eq_hgap2 {m k : ℕ} (hk1 : 1 ≤ k) (hcen : 2 * k < m) (t : ℝ) :
    bblock2 m k t
      = (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ) * t ^ (2 * k - 1)
          * hgap2 m (m - 2 * k) t / 2 := by
  have hmk : ¬ (k = m - k) := by omega
  have hpow : 2 * (m - k) - 1 = (2 * k - 1) + 2 * (m - 2 * k) := by omega
  have hCsym : Nat.choose (2 * m - 2) (2 * (m - k) - 1)
      = Nat.choose (2 * m - 2) (2 * k - 1) :=
    (choose_block_symm (r := 2) (m := m) (k := k) (by norm_num) hk1 (by omega)).symm
  have hck : (((m - k : ℕ)) : ℝ) = (m : ℝ) - (k : ℝ) := Nat.cast_sub (by omega)
  have hcd : (((m - 2 * k : ℕ)) : ℝ) = (m : ℝ) - 2 * (k : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  unfold bblock2 aterm2 hgap2
  rw [if_neg hmk, hCsym, hpow, pow_add, hck, hcd]
  ring

/-- **`H₂` is nonpositive at every larger gap** (`lem:block-sign` at `r = 2`),
which is `Blocks.hgap_bracket_nonpos_of_le` read at the exponents `2a`, `2b`. -/
theorem hgap2_nonpos_of_le {m a b : ℕ} (hab : a ≤ b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h : hgap2 m a t ≤ 0) : hgap2 m b t ≤ 0 := by
  unfold hgap2 at h ⊢
  exact hgap_bracket_nonpos_of_le hab (by omega) ht0 ht1 h

theorem bblock2_nonpos_of_succ {m k : ℕ} (hk1 : 1 ≤ k) (hsucc : k + 1 ≤ m / 2) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (h : bblock2 m (k + 1) t ≤ 0) :
    bblock2 m k t ≤ 0 := by
  have hcen : 2 * (k + 1) < m := by
    rcases lt_or_eq_of_le (show 2 * (k + 1) ≤ m by omega) with h' | h'
    · exact h'
    · exact absurd h (not_le.mpr (bblock2_center_pos (by omega) h' ht0 ht1))
  have hk : 2 * k < m := by omega
  have hCs : (0 : ℝ) < (Nat.choose (2 * m - 2) (2 * (k + 1) - 1) : ℝ) := by
    have : 0 < Nat.choose (2 * m - 2) (2 * (k + 1) - 1) := Nat.choose_pos (by omega)
    exact_mod_cast this
  rw [bblock2_eq_hgap2 (m := m) (k := k + 1) (by omega) hcen t] at h
  have hH1 : hgap2 m (m - 2 * (k + 1)) t ≤ 0 := by
    by_contra! hpos
    have hp : (0 : ℝ) < t ^ (2 * (k + 1) - 1) := pow_pos ht0 _
    have : (0 : ℝ) < (Nat.choose (2 * m - 2) (2 * (k + 1) - 1) : ℝ)
        * t ^ (2 * (k + 1) - 1) * hgap2 m (m - 2 * (k + 1)) t / 2 :=
      div_pos (mul_pos (mul_pos hCs hp) hpos) two_pos
    linarith
  have hH0 : hgap2 m (m - 2 * k) t ≤ 0 := hgap2_nonpos_of_le (by omega) ht0 ht1 hH1
  rw [bblock2_eq_hgap2 (m := m) (k := k) hk1 hk t]
  have hnp : (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ) * t ^ (2 * k - 1)
      * hgap2 m (m - 2 * k) t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hH0
  linarith

/-- **The final `r = 2` block is positive.**  For even `m` it is the center
block; for odd `m` the gap is one, where
`H₂(m,1;t) = (1-t)[m(1+t²) - (1+t)²]` and `m(1+t²) - (1+t)² ≥ (1-t)² > 0`
already at `m = 2`. -/
theorem bblock2_top_pos {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < bblock2 m (m / 2) t := by
  have hk1 : 1 ≤ m / 2 := by omega
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨j, hj⟩ := he
    exact bblock2_center_pos hk1 (by omega) ht0 ht1
  · obtain ⟨j, hj⟩ := ho
    have hm3 : 3 ≤ m := by omega
    have hcen : 2 * (m / 2) < m := by omega
    have hcenterGap : m - 2 * (m / 2) = 1 := by omega
    have hC : (0 : ℝ) < (Nat.choose (2 * m - 2) (2 * (m / 2) - 1) : ℝ) := by
      have : 0 < Nat.choose (2 * m - 2) (2 * (m / 2) - 1) := Nat.choose_pos (by omega)
      exact_mod_cast this
    rw [bblock2_eq_hgap2 hk1 hcen t, hcenterGap]
    have hmc : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hsubt : (0 : ℝ) < 1 - t := by linarith
    have hsq : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have hkey : (0 : ℝ) < (m : ℝ) * (1 + t ^ 2) - (1 + t) ^ 2 := by
      nlinarith [sq_nonneg (1 - t), mul_le_mul_of_nonneg_right hmc hsq.le]
    have hH : 0 < hgap2 m 1 t := by
      unfold hgap2
      norm_num
      nlinarith [mul_pos hsubt hkey]
    exact div_pos (mul_pos (mul_pos hC (pow_pos ht0 _)) hH) two_pos

theorem sum_blocks2_eq_jm2 {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    ∑ k ∈ Finset.range (m / 2), bblock2 m (k + 1) t = jm2 m t := by
  have h := sum_weighted_eq_pairs (fun _ => (1 : ℝ)) (fun k => aterm2 m k t) hm
    (fun _ _ _ => rfl)
  simp only [one_mul] at h
  rw [jm2, h]
  rfl

section WeightedOrderTwo

variable (m : ℕ)

/-- The weighted `r = 2` derivative numerator. -/
noncomputable def jmw2 (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (m - 1), w k * aterm2 m k t

/-- **`thm:kernel` at `r = 2`, analytic content**: for symmetric weights
nondecreasing toward the center, `J^{(2)}_{m,w}(t) ≥ 0` on `(0,1)`.  Same three
steps as at `r = 3`: pair, find the single sign change, and transfer the
constant-weight positivity `jm2_pos` through the weights. -/
theorem jmw2_nonneg (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hwnn : ∀ i, 1 ≤ i → i ≤ m / 2 → 0 ≤ w i)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r))
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ jmw2 m w t := by
  have hpair := sum_weighted_eq_pairs w (fun k => aterm2 m k t) hm hsym
  have hblk : ∀ k, w (k + 1) * (aterm2 m (k + 1) t
      + (if k + 1 = m - (k + 1) then 0 else aterm2 m (m - (k + 1)) t))
      = w (k + 1) * bblock2 m (k + 1) t := fun k => rfl
  rw [jmw2, hpair, Finset.sum_congr rfl (fun k _ => hblk k)]
  have hsum_pos : 0 ≤ ∑ k ∈ Finset.range (m / 2), bblock2 m (k + 1) t := by
    rw [sum_blocks2_eq_jm2 hm]
    exact (jm2_pos m hm t ht0 ht1).le
  have hdown : ∀ j, j + 2 ≤ m / 2 → bblock2 m (j + 1 + 1) t ≤ 0 → bblock2 m (j + 1) t ≤ 0 :=
    fun j hj h => bblock2_nonpos_of_succ (by omega) (by omega) ht0 ht1 h
  have htop : 0 < bblock2 m (m / 2 - 1 + 1) t := by
    rw [show m / 2 - 1 + 1 = m / 2 from by omega]
    exact bblock2_top_pos hm ht0 ht1
  rcases sign_change_of_stepDown (B := fun k => bblock2 m (k + 1) t) hdown (by omega) htop with
    ⟨q, hq, hle, hge⟩ | hall
  · exact sum_weighted_nonneg (fun k => w (k + 1)) (fun k => bblock2 m (k + 1) t) (m / 2)
      (fun i j hij hjn => hwmono (i + 1) (j + 1) (by omega) (by omega) (by omega))
      (fun k hk => hwnn (k + 1) (by omega) (by omega))
      q (by omega) hle (fun k hqk hkn => hge k hqk hkn) hsum_pos
  · refine Finset.sum_nonneg fun k hk => ?_
    have hk' : k < m / 2 := Finset.mem_range.mp hk
    exact mul_nonneg (hwnn (k + 1) (by omega) (by omega)) (hall k hk')

/-! ### The `r = 2` kernel, and its monotonicity on `[0,1/2]` -/

/-- The `r = 2` residue kernel, `eq:G-weighted` at multiplicity two. -/
noncomputable def gmw2 (w : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (m - 1),
    w k * (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ) * p ^ (2 * k) * (1 - p) ^ (2 * (m - k))

/-- The numerator of `G^{(2)}_{m,w}` after the projective substitution `p = t/(1+t)`. -/
noncomputable def gmwNum2 (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (m - 1), w k * (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ) * t ^ (2 * k)

theorem gmw2_symm (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hsym : ∀ k, 1 ≤ k → k ≤ m - 1 → w k = w (m - k)) (p : ℝ) :
    gmw2 m w (1 - p) = gmw2 m w p := by
  unfold gmw2
  refine Finset.sum_nbij' (fun k => m - k) (fun k => m - k) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    simp only [Finset.mem_Icc]; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    simp only [Finset.mem_Icc]; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only
    have hback : m - (m - a) = a := by omega
    have hchoose : Nat.choose (2 * m - 2) (2 * (m - a) - 1)
        = Nat.choose (2 * m - 2) (2 * a - 1) := by
      have hle : 2 * a - 1 ≤ 2 * m - 2 := by omega
      have hsub : 2 * m - 2 - (2 * a - 1) = 2 * (m - a) - 1 := by omega
      rw [← hsub, Nat.choose_symm hle]
    rw [hback, hchoose, ← hsym a h1 h2, sub_sub_cancel]
    ring

theorem continuous_gmw2 (w : ℕ → ℝ) : Continuous (gmw2 m w) := by
  unfold gmw2; fun_prop

theorem gmw2_proj (w : ℕ → ℝ) {t : ℝ} (ht : 1 + t ≠ 0) :
    gmw2 m w (t / (1 + t)) = gmwNum2 m w t / (1 + t) ^ (2 * m) := by
  unfold gmw2 gmwNum2
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hexp : 2 * m = 2 * k + 2 * (m - k) := by omega
  have hproj : (1 : ℝ) - t / (1 + t) = 1 / (1 + t) := by field_simp; ring
  rw [hproj, hexp, pow_add, div_pow, div_pow, one_pow]
  field_simp

theorem hasDerivAt_gmwNum2 (w : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (gmwNum2 m w)
      (∑ k ∈ Finset.Icc 1 (m - 1), w k * (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ)
        * (((2 * k : ℕ) : ℝ) * t ^ (2 * k - 1))) t := by
  unfold gmwNum2
  refine HasDerivAt.fun_sum fun k _ => ?_
  simpa [mul_assoc] using (hasDerivAt_pow (2 * k) t).const_mul
    (w k * (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ))

/-- `(1+t)·G'_{num} - 2m·G_{num} = 2 J^{(2)}_{m,w}(t)`: termwise, `t^{2k}`
factors as `t^{2k-1}·t` and `2k(1+t) - 2mt = 2(k - (m-k)t)`. -/
theorem gmwNum2_deriv_key (w : ℕ → ℝ) (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 (m - 1), w k * (Nat.choose (2 * m - 2) (2 * k - 1) : ℝ)
        * (((2 * k : ℕ) : ℝ) * t ^ (2 * k - 1))) * (1 + t)
      - ((2 * m : ℕ) : ℝ) * gmwNum2 m w t
      = 2 * jmw2 m w t := by
  unfold gmwNum2 jmw2
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hp : t ^ (2 * k) = t ^ (2 * k - 1) * t := by
    rw [← pow_succ]; congr 1; omega
  unfold aterm2
  push_cast
  rw [hp]
  ring

theorem hasDerivAt_gmw2_proj (hm : 1 ≤ m) (w : ℕ → ℝ) {t : ℝ} (ht : 1 + t ≠ 0) :
    HasDerivAt (fun t : ℝ => gmw2 m w (t / (1 + t)))
      (2 * jmw2 m w t / (1 + t) ^ (2 * m + 1)) t := by
  obtain ⟨K, hK⟩ : ∃ K, 2 * m = K + 1 := ⟨2 * m - 1, by omega⟩
  have hcont : ContinuousAt (fun s : ℝ => 1 + s) t := by fun_prop
  have hnb : ∀ᶠ s in nhds t, 1 + s ≠ 0 := hcont.eventually_ne ht
  have hden : HasDerivAt (fun s : ℝ => (1 + s) ^ (2 * m))
      (((2 * m : ℕ) : ℝ) * (1 + t) ^ (2 * m - 1)) t := by
    simpa using HasDerivAt.fun_pow ((hasDerivAt_id t).const_add 1) (2 * m)
  have hdiv := (hasDerivAt_gmwNum2 m w t).div hden (pow_ne_zero _ ht)
  refine HasDerivAt.congr_of_eventuallyEq ?_ (hnb.mono fun s hs => gmw2_proj m w hs)
  convert hdiv using 1
  have hkey := gmwNum2_deriv_key m w t
  rw [hK] at hkey ⊢
  simp only [Nat.add_sub_cancel]
  rw [div_eq_div_iff (pow_ne_zero _ ht) (pow_ne_zero _ (pow_ne_zero _ ht))]
  linear_combination (-((1 + t) ^ K * (1 + t) ^ (K + 2))) * hkey

/-- **`thm:kernel` at `r = 2`, as the paper states it**: for symmetric weights
nondecreasing toward the center, `G^{(2)}_{m,w}` is nondecreasing on `[0,1/2]`. -/
theorem gmw2_monotoneOn (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hwmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m / 2 → w i ≤ w j)
    (hwnn : ∀ i, 1 ≤ i → i ≤ m / 2 → 0 ≤ w i)
    (hsym : ∀ k, 1 ≤ k → k ≤ m - 1 → w k = w (m - k)) :
    MonotoneOn (gmw2 m w) (Set.Icc 0 (1 / 2)) :=
  monotoneOn_of_proj_deriv_nonneg
    (fun x hx => hasDerivAt_gmw2_proj m (by omega) w (by linarith))
    (fun x hx0 hx1 => div_nonneg (by linarith [jmw2_nonneg m hm w hwmono hwnn hsym x hx0 hx1])
      (pow_nonneg (by linarith) _))

end WeightedOrderTwo

end CubicPochhammer
