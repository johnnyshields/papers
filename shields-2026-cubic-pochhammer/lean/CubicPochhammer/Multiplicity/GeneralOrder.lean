/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Main

/-!
# The coefficient convolution at a general multiplicity

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp
multiplicity threshold», `eq:general-r` and `eq:r-degree-three`.

The general-multiplicity series `F_{f,r}(μ;x) = ∑_{n≥1} f_n (μ)_{rn}/(rn-1)! xⁿ`
enters `prop:multiplicity-threshold` only through its degree-`m` product
coefficient, so that coefficient is what is defined here, together with the
structural identities every later multiplicity argument runs on and the exact
degree-three Turánian coefficient of the two-term sequence.

The factor `r-3` the paper's two displays share is visible here as the
`μ`-coefficient of the quadratic remainder in `pochDegreeThree_identity`: after
extracting `(μ+2)_{r-2}`, `(μ+2)_{2r-2}` and `(μ+1)` from all six products,
what is left is `2(μ+1)(μ+r)(μ+2r) - μ(μ+2r)(μ+2r+1) - μ(μ+r)(μ+r+1)
= r(4r - (r-3)μ)`.

## Main definitions

* `cmwr`, `cmfr` --- the degree-`m` coefficient of `F_{f,r}(u;x) F_{f,r}(v;x)`,
  carried with an arbitrary weight family and at the weights `w_k = f_k f_{m-k}`
  of `eq:w-from-f`.  `cmwr_three` and `cmfr_three` identify them with
  `Bridge.cmw` and `Bridge.cmf` at `r = 3`.
* `twoTerm` --- the two-term sequence `f₁ = f₂ = 1`, `f_n = 0` for `n ≥ 3`, the
  witness the threshold is exhibited on.

## Main statements

* `pochDegreeThree_identity` --- the polynomial identity behind the closed form,
  with the Pochhammer factorizations carried out.
* `twoTerm_degreeThree` --- `eq:r-degree-three`: the degree-three Turánian
  coefficient of `twoTerm`.
* `twoTerm_degreeThree_neg_iff` --- where it turns negative, for `r ≥ 4`.
* `degreeTwo_nonneg`, `onePoint_nonneg` --- minimality in degree and in support
  size: neither can produce a counterexample at any `r`.
* `cmwr_nonneg`, `cmwr_right_zero`, `cmwr_symm` --- the three structural
  identities of `cmwr`, the boundary cases of every Schur argument below.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp multiplicity
  threshold»: `prop:multiplicity-threshold`, `eq:general-r`,
  `eq:r-degree-three`, `eq:w-from-f`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-! ### Pochhammer shifts -/

/-- `(u)_{k+1} = (u)_k (u+k)`. -/
theorem poch_succ (u : ℝ) (k : ℕ) : poch u (k + 1) = poch u k * (u + (k : ℝ)) := by
  unfold poch; rw [Finset.prod_range_succ]

/-- `(u)_{k+1} = u (u+1)_k`. -/
theorem poch_succ' (u : ℝ) (k : ℕ) : poch u (k + 1) = u * poch (u + 1) k := by
  unfold poch
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one]
  rw [mul_comm]
  congr 1
  · norm_num
  · exact Finset.prod_congr rfl fun i _ => by ring

/-! ### `eq:r-degree-three` -/

/-- The Pochhammer identity behind `eq:r-degree-three`, at `r = n+2`.  All six
products carry `(μ+2)_n`, `(μ+2)_{2n+2}` and `(μ+1)`; what is left is a
quadratic in `μ` whose value is `r(4r-(r-3)μ)`. -/
theorem pochDegreeThree_identity (n : ℕ) (μ : ℝ) :
    2 * poch (μ + 1) (n + 2) * poch (μ + 1) (2 * n + 4)
      - poch μ (n + 2) * poch (μ + 2) (2 * n + 4)
      - poch μ (2 * n + 4) * poch (μ + 2) (n + 2)
    = ((n : ℝ) + 2) * (4 * ((n : ℝ) + 2) - ((n : ℝ) - 1) * μ)
        * (poch (μ + 2) n * ((μ + 1) * poch (μ + 2) (2 * n + 2))) := by
  have e1 : poch (μ + 1) (n + 2)
      = (μ + 1) * ((μ + 2 + (n : ℝ)) * poch (μ + 2) n) := by
    rw [poch_succ' (μ + 1) (n + 1), poch_succ (μ + 1 + 1) n]
    ring_nf
  have e2 : poch μ (n + 2) = μ * ((μ + 1) * poch (μ + 2) n) := by
    rw [poch_succ' μ (n + 1), poch_succ' (μ + 1) n]
    ring_nf
  have e3 : poch (μ + 2) (n + 2)
      = poch (μ + 2) n * ((μ + 2 + (n : ℝ)) * (μ + 3 + (n : ℝ))) := by
    rw [poch_succ (μ + 2) (n + 1), poch_succ (μ + 2) n]
    push_cast
    ring
  have e4 : poch (μ + 1) (2 * n + 4)
      = (μ + 1) * (poch (μ + 2) (2 * n + 2) * (μ + 4 + 2 * (n : ℝ))) := by
    have h : 2 * n + 4 = (2 * n + 3) + 1 := by omega
    rw [h, poch_succ' (μ + 1) (2 * n + 3),
      show 2 * n + 3 = (2 * n + 2) + 1 from by omega, poch_succ (μ + 1 + 1) (2 * n + 2)]
    push_cast
    ring_nf
  have e5 : poch μ (2 * n + 4) = μ * ((μ + 1) * poch (μ + 2) (2 * n + 2)) := by
    have h : 2 * n + 4 = ((2 * n + 2) + 1) + 1 := by omega
    rw [h, poch_succ' μ ((2 * n + 2) + 1), poch_succ' (μ + 1) (2 * n + 2)]
    ring_nf
  have e6 : poch (μ + 2) (2 * n + 4)
      = poch (μ + 2) (2 * n + 2) * ((μ + 4 + 2 * (n : ℝ)) * (μ + 5 + 2 * (n : ℝ))) := by
    have h : 2 * n + 4 = ((2 * n + 2) + 1) + 1 := by omega
    rw [h, poch_succ (μ + 2) ((2 * n + 2) + 1), poch_succ (μ + 2) (2 * n + 2)]
    push_cast
    ring
  rw [e1, e2, e3, e4, e5, e6]
  ring

/-! ### The degree-`m` coefficient at general multiplicity -/

/-- The degree-`m` coefficient of `F_{f,r}(u;x) F_{f,r}(v;x)` of `eq:general-r`,
carried with an arbitrary weight family: the `r`-generalization of `Bridge.cmw`.

  `C^{(r)}_{m,w}(u,v) = ∑_{k=1}^{m-1} w_k (u)_{rk}(v)_{r(m-k)} /
                        ((rk-1)!(r(m-k)-1)!)`. -/
noncomputable def cmwr (r : ℕ) (w : ℕ → ℝ) (m : ℕ) (u v : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (m - 1),
    w k * (poch u (r * k) * poch v (r * (m - k)))
      / ((Nat.factorial (r * k - 1) : ℝ) * (Nat.factorial (r * (m - k) - 1) : ℝ))

/-- `cmwr` at the weights `w_k = f_k f_{m-k}` of `eq:w-from-f`. -/
noncomputable def cmfr (r : ℕ) (f : ℕ → ℝ) (m : ℕ) (u v : ℝ) : ℝ :=
  cmwr r (fun k => f k * f (m - k)) m u v

/-- At `r = 3` the general coefficient is the cubic one the rest of the tree
uses. -/
theorem cmwr_three (w : ℕ → ℝ) (m : ℕ) (u v : ℝ) : cmwr 3 w m u v = cmw w m u v := rfl

/-- At `r = 3` the general coefficient is the cubic one the rest of the tree
uses. -/
theorem cmfr_three (f : ℕ → ℝ) (m : ℕ) (u v : ℝ) : cmfr 3 f m u v = cmf f m u v := rfl

/-! ### The two-term sequence of `eq:r-degree-three` -/

/-- The two-term sequence `f₁ = f₂ = 1`, `f_n = 0` for `n ≥ 3`. -/
def twoTerm : ℕ → ℝ := fun k => if k = 1 ∨ k = 2 then 1 else 0

@[simp] theorem twoTerm_one : twoTerm 1 = 1 := by simp [twoTerm]

@[simp] theorem twoTerm_two : twoTerm 2 = 1 := by simp [twoTerm]

theorem twoTerm_nonneg (k : ℕ) : 0 ≤ twoTerm k := by
  unfold twoTerm; split <;> norm_num

theorem twoTerm_eq_zero {k : ℕ} (hk : 3 ≤ k) : twoTerm k = 0 := by
  unfold twoTerm
  rw [if_neg]
  omega

/-- The degree-three product coefficient of the two-term sequence. -/
theorem cmfr_twoTerm_three (r : ℕ) (u v : ℝ) :
    cmfr r twoTerm 3 u v
      = (poch u r * poch v (2 * r) + poch u (2 * r) * poch v r)
          / ((Nat.factorial (r - 1) : ℝ) * (Nat.factorial (2 * r - 1) : ℝ)) := by
  have hIcc : Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) := by decide
  rw [cmfr, cmwr, hIcc, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  norm_num [mul_comm r 2]
  ring

/-- **`eq:r-degree-three`**: for the two-term sequence `f₁ = f₂ = 1`,
`f_n = 0` for `n ≥ 3`, and every integer `r ≥ 2`,

  `[x³](F_{f,r}(μ+1;x)² - F_{f,r}(μ;x)F_{f,r}(μ+2;x))
     = r(4r-(r-3)μ)(μ+2)_{r-2}(μ+1)_{2r-1} / ((r-1)!(2r-1)!)`. -/
theorem twoTerm_degreeThree {r : ℕ} (hr : 2 ≤ r) (μ : ℝ) :
    cmfr r twoTerm 3 (μ + 1) (μ + 1) - cmfr r twoTerm 3 μ (μ + 2)
      = (r : ℝ) * (4 * (r : ℝ) - ((r : ℝ) - 3) * μ)
          * poch (μ + 2) (r - 2) * poch (μ + 1) (2 * r - 1)
          / ((Nat.factorial (r - 1) : ℝ) * (Nat.factorial (2 * r - 1) : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  rw [cmfr_twoTerm_three, cmfr_twoTerm_three]
  simp only [show n + 2 - 2 = n from by omega, show 2 * (n + 2) = 2 * n + 4 from by omega,
    show 2 * n + 4 - 1 = 2 * n + 3 from by omega, show n + 2 - 1 = n + 1 from by omega]
  rw [div_sub_div_same]
  congr 1
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by omega, poch_succ' (μ + 1) (2 * n + 2),
    show μ + 1 + 1 = μ + 2 from by ring]
  push_cast
  linear_combination pochDegreeThree_identity n μ

/-! ### The threshold `μ > 4r/(r-3)` -/

/-- **The threshold of `prop:multiplicity-threshold`**: for `r ≥ 4` the
degree-three coefficient of `eq:r-degree-three` is negative exactly when
`μ > 4r/(r-3)`. -/
theorem twoTerm_degreeThree_neg_iff {r : ℕ} (hr : 4 ≤ r) {μ : ℝ} (hμ : 0 ≤ μ) :
    cmfr r twoTerm 3 (μ + 1) (μ + 1) - cmfr r twoTerm 3 μ (μ + 2) < 0
      ↔ 4 * (r : ℝ) / ((r : ℝ) - 3) < μ := by
  have hr3 : (3 : ℝ) < (r : ℝ) := by
    have : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hP1 : 0 < poch (μ + 2) (r - 2) := poch_pos (by linarith) _
  have hP2 : 0 < poch (μ + 1) (2 * r - 1) := poch_pos (by linarith) _
  have hf1 : (0 : ℝ) < (Nat.factorial (r - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf2 : (0 : ℝ) < (Nat.factorial (2 * r - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [twoTerm_degreeThree (by omega) μ]
  rw [div_neg_iff]
  constructor
  · intro h
    rcases h with ⟨_, hDneg⟩ | ⟨hnum, _⟩
    · nlinarith [hf1, hf2]
    · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (r : ℝ) - 3)]
      by_contra hcon
      have hrem_nn : 0 ≤ 4 * (r : ℝ) - ((r : ℝ) - 3) * μ := by nlinarith
      have hscaled : 0 ≤ (r : ℝ) * (4 * (r : ℝ) - ((r : ℝ) - 3) * μ)
          * poch (μ + 2) (r - 2) * poch (μ + 1) (2 * r - 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg hrpos.le hrem_nn) hP1.le) hP2.le
      linarith
  · intro h
    right
    refine ⟨?_, mul_pos hf1 hf2⟩
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (r : ℝ) - 3)] at h
    have hrem_neg : 4 * (r : ℝ) - ((r : ℝ) - 3) * μ < 0 := by nlinarith
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hrpos hrem_neg) hP1) hP2

/-! ### Minimality in degree and in support size -/

/-- **The Pochhammer Turánian, termwise**: `(μ)_N (μ+α+β)_N ≤ (μ+α)_N (μ+β)_N`
for `μ, α, β ≥ 0`.  Factor by factor the gap is exactly `αβ`, since
`(t+α)(t+β) - t(t+α+β) = αβ`. -/
theorem poch_turan (N : ℕ) {μ α β : ℝ} (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    poch μ N * poch (μ + α + β) N ≤ poch (μ + α) N * poch (μ + β) N := by
  unfold poch
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    exact mul_nonneg (by linarith) (by linarith)
  · have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hcross : (μ + α + (i : ℝ)) * (μ + β + (i : ℝ))
        - (μ + (i : ℝ)) * (μ + α + β + (i : ℝ)) = α * β := by ring
    have := mul_nonneg hα hβ
    linarith

/-- **Degree two is nonnegative for every `r`** (`prop:multiplicity-threshold`,
minimality in degree): the degree-two Turánian coefficient is `f₁²/((r-1)!)²`
times the Pochhammer Turánian at `N = r`. -/
theorem degreeTwo_nonneg (r : ℕ) (f : ℕ → ℝ) {μ α β : ℝ}
    (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ cmfr r f 2 (μ + α) (μ + β) - cmfr r f 2 μ (μ + α + β) := by
  have hIcc : Finset.Icc 1 (2 - 1) = ({1} : Finset ℕ) := by decide
  have hexp : ∀ u v : ℝ, cmfr r f 2 u v
      = (f 1 * f 1) * (poch u r * poch v r)
          / ((Nat.factorial (r - 1) : ℝ) * (Nat.factorial (r - 1) : ℝ)) := by
    intro u v
    rw [cmfr, cmwr, hIcc, Finset.sum_singleton]
    norm_num
  rw [hexp, hexp, sub_nonneg, div_le_div_iff_of_pos_right (by
    have hfac_pos : (0 : ℝ) < (Nat.factorial (r - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity)]
  exact mul_le_mul_of_nonneg_left (poch_turan r hμ hα hβ) (mul_self_nonneg (f 1))

/-- **No one-point-support sequence gives a negative coefficient**
(`prop:multiplicity-threshold`, minimality in support size).  A sequence
supported at `{a}` has one active product degree, `m = 2a`, where the two
Pochhammer arguments coincide and `poch_turan` applies termwise; every other
degree contributes zero on both sides. -/
theorem onePoint_nonneg (r a m : ℕ) (f : ℕ → ℝ) (hfnn : ∀ k, 0 ≤ f k)
    (hsupp : ∀ k, k ≠ a → f k = 0) {μ α β : ℝ}
    (hμ : 0 ≤ μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ cmfr r f m (μ + α) (μ + β) - cmfr r f m μ (μ + α + β) := by
  rw [sub_nonneg, cmfr, cmfr, cmwr, cmwr]
  refine Finset.sum_le_sum fun k _ => ?_
  have hden : (0 : ℝ) <
      (Nat.factorial (r * k - 1) : ℝ) * (Nat.factorial (r * (m - k) - 1) : ℝ) := by
    have hfacL : (0 : ℝ) < (Nat.factorial (r * k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfacR : (0 : ℝ) < (Nat.factorial (r * (m - k) - 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    positivity
  rw [div_le_div_iff_of_pos_right hden]
  by_cases hk : k = a
  · by_cases hmk : m - k = a
    · -- the active degree: both Pochhammer orders are `r*a`
      have horder : r * (m - k) = r * k := by rw [hmk, hk]
      rw [horder]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hfnn k) (hfnn (m - k)))
      exact poch_turan (r * k) hμ hα hβ
    · rw [hsupp (m - k) hmk, mul_zero, zero_mul, zero_mul]
  · rw [hsupp k hk, zero_mul, zero_mul, zero_mul]

/-! ### The general-`r` coefficient convolution: the three structural identities -/

theorem cmwr_nonneg (r : ℕ) (w : ℕ → ℝ) (m : ℕ) (hwnn : ∀ i, 0 ≤ w i) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ cmwr r w m u v := by
  refine Finset.sum_nonneg fun k _ => div_nonneg ?_ ?_
  · exact mul_nonneg (hwnn k) (mul_nonneg (poch_nonneg hu _) (poch_nonneg hv _))
  · positivity

theorem cmwr_right_zero (r : ℕ) (hr : 1 ≤ r) (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) (u : ℝ) :
    cmwr r w m u 0 = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  rw [poch_zero_eq_zero (show 1 ≤ r * (m - k) by
    have : 1 ≤ m - k := by omega
    exact Nat.one_le_iff_ne_zero.mpr (by positivity))]
  ring

theorem cmwr_symm (r : ℕ) (w : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hsym : ∀ k, 1 ≤ k → k ≤ m - 1 → w k = w (m - k)) (u v : ℝ) :
    cmwr r w m u v = cmwr r w m v u := by
  unfold cmwr
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
    rw [hback, hsym a h1 h2]
    ring

end CubicPochhammer
