/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTGeometryBranch
import ForgacsTran.PencilIndex

/-!
# The minimum-modulus gap at the constructed branch

`FTGeometryBranch.ft_geometry_at_branch` carries `hmin` — that at each angle of
the viewing arc the principal pair are the only zeros of the pencil in the closed
disk of radius `τ(θ)` — as a hypothesis with no producer.  This module builds it
from `Forgacs2017RationalDenominator` Props. 1--2, reducing it to the one
paragraph of their proof that is genuinely separate: the location of the argument
of a hypothetical inner zero.

The chain is: an inner zero `w` is `‖w‖e^{-iφ}` after conjugating into the lower
half plane; the imaginary part of the root equation quantizes the angle sum at
`(‖w‖, φ)`, producing a branch index `l < n` with `∑_k θ_k(‖w‖; φ) = rφ + lπ` and
fixing the parity of `n - l - 1` from the sign of `z`; `ftTau_eq_of` then reads
`‖w‖` as the branch radius `τ(φ; l)` and `ftBranch_ftArcPoint_eq_ftBranchZ` reads
`z` as `z(φ; l)`; and `ftProp1_closing_principal` forces `φ = θ`, whence
`‖w‖ = τ(θ)` and `w` is one of the pair.

## Main statements

* `exists_ftAngleSum_index_of_root` — the quantization.  A zero of the pencil at a
  real spectral parameter, written in polar form on the lower half of the viewing
  cone, has its angle sum equal to `rφ + lπ` for a natural `l < n`, with
  `0 < (-1)^{n+l+1} z`.  This is `Forgacs2017RationalDenominator`'s "Eqs. (6),
  (7), and (8) imply that for some `0 ≤ l < n` …", with the range of `l` and the
  parity of `n - l - 1` derived rather than asserted.
* `ftTau_principal_le` — `τ(θ; n-1) ≤ τ(θ; l)` for `l ≤ n - 1`, their Remark 4.
* `ftProp1_closing_principal` — the closing step of their Prop. 1, squeezed on the
  principal branch rather than on the intermediate index, which is what removes
  every hypothesis about the index-`l` branch away from `φ`.
* `ft_minModulus_at_branch` — `thm:FT-geometry`'s `hmin` for the constructed
  branch, on the whole admissible class `2 ≤ n`, `1 ≤ r`, with the cone condition
  as its only hypothesis.
* `ft_minModulus_at_branch_of_le_two_mul` — the same with a redundant `n ≤ 2r`,
  kept so that consumers written against the earlier index-conditioned form still
  elaborate.
* `not_ftBranchAt_of_le`, `not_arc_wide_of_two_mul_lt` — the range condition of
  their Lemma 2 read as a refutation.  These are why the closing squeeze runs on
  the principal branch: they exhibit an angle of the viewing arc at which the
  intermediate index carries no branch at all, so the paper's own squeeze has
  nothing to be continuous along.
* `ft_geometry_at_branch_of_cone`, `ft_geometry_at_branch_unbounded_of_cone` —
  `ft_geometry_at_branch` with `hmin` discharged.

## Implementation notes

Two hypotheses remain, and each is a precise statement rather than a gap:

* `hcone` is the two paragraphs of their Prop. 1 that place the argument of an
  inner zero — "We first argue that `t* ∉ ℝ`", which runs on their Lemmas 5 and
  6 and the first positive critical point `t_a`, and "We next claim that the
  argument `θ^{t*}` of `t*` lies in `(0, π/r)`", which runs on the containment
  `t* ∈ C₁ ∩ C₂` and the angle bound.  `FTMinModulus.Propositions` carries the
  pieces of the second — `norm_sub_le_of_prod_le` is the `C₂` containment and
  `sin_numerator_nonneg` the angle bound — and `strictMonoOn_negDivPow` the
  pieces of the first; what neither has is the interval `(a,b)` of `eq:ab-def`,
  whose right endpoint is the tree's other open binder.  Nothing else in the
  argument needs `C₂`: the containment `‖w‖ ≤ τ` alone supplies `τ(φ; l) ≤ τ`.
There is no second hypothesis about the branch.  An earlier form of this module
carried one — that the intermediate index admits a branch across the whole viewing
arc, which is what `FTBranchZMono.ftProp1_angle_eq` demands — and it is false:
clauses (i) and (ii) of their Lemma 2 are incompatible once `rψ + lπ ≤ nψ`, so the
index-`l` branch lives only on `(0, min(π/r, lπ/(n-r)))`, and
`not_arc_wide_of_two_mul_lt` names an angle of the arc outside it whenever
`2r < n`.  `ftProp1_closing_principal` removes the condition rather than weakening
it, by squeezing along the principal branch, which `ftBranchAt_of_arc_principal`
supplies across the arc with no hypothesis at all.  Neither `ftProp1_closing` nor
`ftBranchZ_strictMonoOn` needed restating.

Sorry-free.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `thm:FT-geometry`,
  `eq:principal-pair`.
* `Forgacs2017RationalDenominator`, Propositions 1 and 2, Lemma 2 and Remark 4.

## Tags

minimum modulus, principal pair, branch index, Forgacs-Tran
-/

namespace ForgacsTran

open Real Set Polynomial

/-! ### Polar form on the lower half plane -/

/-- `τ e^{-iθ}` is nonzero. -/
theorem ftArcPoint_ne_zero {σ φ : ℝ} (hσ : σ ≠ 0) : ftArcPoint σ φ ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hσ) (Complex.exp_ne_zero _)

/-- Every complex number is `‖w‖e^{-iφ}` at `φ = -arg w`. -/
theorem eq_ftArcPoint_neg_arg (w : ℂ) : w = ftArcPoint ‖w‖ (-Complex.arg w) := by
  rw [ftArcPoint, show (-((-Complex.arg w : ℝ) : ℂ)) = ((Complex.arg w : ℝ) : ℂ) by
    push_cast; ring]
  exact (Complex.norm_mul_exp_arg_mul_I w).symm

/-- Its conjugate is `‖w‖e^{-iφ}` at `φ = arg w`. -/
theorem conj_eq_ftArcPoint_arg (w : ℂ) :
    (starRingEnd ℂ) w = ftArcPoint ‖w‖ (Complex.arg w) := by
  conv_lhs => rw [eq_ftArcPoint_neg_arg w]
  rw [ftArcPoint, ftArcPoint, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    map_neg, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- The lower branch point is the conjugate of `eq:principal-pair`'s `t_+`. -/
theorem ftArcPoint_eq_conj_ftPrincipal {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) :
    ftArcPoint (ftTau a r l θ) θ = (starRingEnd ℂ) (ftPrincipal (ftTau a r l) θ) := by
  rw [ftPrincipal, ftArcPoint, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-! ### The quantization of the angle sum -/

/-- **`Forgacs2017RationalDenominator` Prop. 1, the branch index.**  A zero
`σ e^{-iφ}` of the pencil at a real spectral parameter `z`, with `φ` in the
viewing arc, has `∑_k θ_k(σ; φ) = rφ + lπ` for a natural `l < n`, and the sign of
`z` is `(-1)^{n-l-1}`.  Their proof reads this off Eqs. (6)--(8); here it is the
imaginary part of the root equation, with clause (i) of their Lemma 2 —
`φ < θ_k < π` — supplying both bounds on `l`.

The lower bound `1 ≤ l` needs `r ≤ n`: at `n < r` the index `l = 0` is genuinely
available, which is also the case in which their Lemma 2 needs no range
condition. -/
theorem exists_ftAngleSum_index_of_root {n r : ℕ} {a : Fin n → ℝ} {c σ φ z : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hσ : 0 < σ)
    (hφ0 : 0 < φ) (hφr : φ < π / r)
    (hroot : (ftDen (ftRootPoly c a) r ((z : ℝ) : ℂ)).eval (ftArcPoint σ φ) = 0) :
    ∃ l : ℕ, l < n ∧ (1 ≤ l ∨ n < r) ∧ ftAngleSum a σ φ = r * φ + l * π ∧
      0 < (-1 : ℝ) ^ (n + l + 1) * z := by
  have hπ := pi_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrφ : (r : ℝ) * φ < π := by rw [lt_div_iff₀ hr0] at hφr; linarith
  have hφπ : φ ∈ Ioo 0 π := ⟨hφ0, by nlinarith⟩
  have hmem : ∀ k, ftAngle (a k) σ φ ∈ Ioo φ π := fun k => ftAngle_mem_Ioo (ha k) hσ hφπ
  have hratio : ∀ k, a k * Real.sin (ftAngle (a k) σ φ)
      = σ * Real.sin (ftAngle (a k) σ φ - φ) := fun _ => ftAngle_spec hσ.ne' hφπ
  set S : ℝ := ftAngleSum a σ φ with hS
  set K : ℝ := ∏ k, ftChord (a k) φ (ftAngle (a k) σ φ) with hKdef
  have hK : 0 < K := Finset.prod_pos fun k _ => ftChord_pos (ha k) hφπ (hmem k)
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  -- clause (i) bounds the angle sum on both sides
  have hSlo : (n : ℝ) * φ < S := by
    have : (∑ _k : Fin n, φ) < ∑ k, ftAngle (a k) σ φ :=
      Finset.sum_lt_sum_of_nonempty hne fun k _ => (hmem k).1
    simpa [hS, ftAngleSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hShi : S < (n : ℝ) * π := by
    have : (∑ k, ftAngle (a k) σ φ) < ∑ _k : Fin n, π :=
      Finset.sum_lt_sum_of_nonempty hne fun k _ => (hmem k).2
    simpa [hS, ftAngleSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  -- the root equation in polar form
  have hprod : ∏ k, ((a k : ℂ) - ftArcPoint σ φ)
      = (((-1) ^ n * K : ℝ) : ℂ) * Complex.exp (-((S : ℝ) : ℂ) * Complex.I) := by
    simpa [hS, hKdef, ftAngleSum] using prod_sub_ftArcPoint hφπ hmem hratio
  have hpow : (ftArcPoint σ φ) ^ r
      = ((σ ^ r : ℝ) : ℂ) * Complex.exp (-(((r : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
    rw [ftArcPoint, mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have heq : (((c * ((-1) ^ n * K) : ℝ)) : ℂ) * Complex.exp (-((S : ℝ) : ℂ) * Complex.I)
      + ((z * σ ^ r : ℝ) : ℂ) * Complex.exp (-(((r : ℝ) * φ : ℝ) : ℂ) * Complex.I) = 0 := by
    rw [ftDen_eval, eval_ftRootPoly, hprod, hpow] at hroot
    push_cast at hroot ⊢
    linear_combination hroot
  -- the real and imaginary parts, as two real equations
  have hri : ((c * ((-1 : ℝ) ^ n * K) * Real.cos S + z * σ ^ r * Real.cos ((r : ℝ) * φ) : ℝ) : ℂ)
      + ((-(c * ((-1 : ℝ) ^ n * K) * Real.sin S) - z * σ ^ r * Real.sin ((r : ℝ) * φ) : ℝ) : ℂ)
        * Complex.I = 0 := by
    rw [exp_neg_ofReal_mul_I, exp_neg_ofReal_mul_I] at heq
    push_cast at heq ⊢
    linear_combination heq
  have hre : c * ((-1 : ℝ) ^ n * K) * Real.cos S + z * σ ^ r * Real.cos ((r : ℝ) * φ) = 0 := by
    have h := congrArg Complex.re hri
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re, mul_zero, zero_mul, sub_zero,
      add_zero] at h
    linarith
  have him : -(c * ((-1 : ℝ) ^ n * K) * Real.sin S) - z * σ ^ r * Real.sin ((r : ℝ) * φ) = 0 := by
    have h := congrArg Complex.im hri
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im, mul_zero, mul_one, add_zero,
      zero_add] at h
    linarith
  have hcA : c * ((-1 : ℝ) ^ n * K) ≠ 0 := by
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow]; positivity
    · rw [ho.neg_one_pow]; nlinarith
  have hsin : Real.sin (S - (r : ℝ) * φ) = 0 := by
    have hkey : (c * ((-1 : ℝ) ^ n * K)) * Real.sin (S - (r : ℝ) * φ) = 0 := by
      rw [Real.sin_sub]
      linear_combination (-(Real.cos ((r : ℝ) * φ))) * him + (-(Real.sin ((r : ℝ) * φ))) * hre
    exact (mul_eq_zero.1 hkey).resolve_left hcA
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 hsin
  -- clause (i) bounds the index on both sides
  have hrφ0 : (0 : ℝ) < (r : ℝ) * φ := mul_pos hr0 hφ0
  have hnφ : (0 : ℝ) ≤ (n : ℝ) * φ := by positivity
  have hm0 : 0 ≤ m := by
    have h1 : (-1 : ℝ) * π < (m : ℝ) * π := by rw [hm]; linarith
    have h2 : (-1 : ℤ) < m := by exact_mod_cast lt_of_mul_lt_mul_right h1 hπ.le
    omega
  have hmn : m < (n : ℤ) := by
    have h1 : (m : ℝ) * π < (n : ℝ) * π := by rw [hm]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right h1 hπ.le
  have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (Int.toNat_of_nonneg hm0)
  set l : ℕ := m.toNat with hldef
  have hSl : S = (l : ℝ) * π + (r : ℝ) * φ := by rw [hcast]; linarith
  refine ⟨l, by omega, ?_, by rw [hSl]; ring, ?_⟩
  · -- `l = 0` survives only below the degenerate range, where `n < r`
    rcases lt_or_ge n r with h | h
    · exact Or.inr h
    · left
      have hrn : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      have h1 : (0 : ℝ) * π < (m : ℝ) * π := by
        rw [hm]; nlinarith [hSlo, mul_nonneg (sub_nonneg.2 hrn) hφ0.le]
      have h2 : (0 : ℤ) < m := by exact_mod_cast lt_of_mul_lt_mul_right h1 hπ.le
      omega
  · -- the sign of `z`, from the imaginary part once the exponentials are matched
    have hsφ : 0 < Real.sin ((r : ℝ) * φ) := Real.sin_pos_of_pos_of_lt_pi hrφ0 hrφ
    have hsinS : Real.sin S = (-1 : ℝ) ^ l * Real.sin ((r : ℝ) * φ) := by
      rw [hSl, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
      ring
    rw [hsinS] at him
    have hfin : ((-1 : ℝ) ^ l * (-1 : ℝ) ^ n) * (c * K) + z * σ ^ r = 0 := by
      refine (mul_eq_zero.1 (show Real.sin ((r : ℝ) * φ)
          * (((-1 : ℝ) ^ l * (-1 : ℝ) ^ n) * (c * K) + z * σ ^ r) = 0 by
        linear_combination -him)).resolve_left hsφ.ne'
    have hσr : (0 : ℝ) < σ ^ r := pow_pos hσ r
    have hcK : (0 : ℝ) < c * K := mul_pos hc hK
    rcases Nat.even_or_odd (n + l) with he | ho
    · have h1 : (-1 : ℝ) ^ l * (-1 : ℝ) ^ n = 1 := by
        rw [← pow_add, show l + n = n + l by ring]; exact he.neg_one_pow
      have h2 : (-1 : ℝ) ^ (n + l + 1) = -1 := by
        rw [pow_succ, he.neg_one_pow]; ring
      rw [h1, one_mul] at hfin
      rw [h2]
      nlinarith [hfin]
    · have h1 : (-1 : ℝ) ^ l * (-1 : ℝ) ^ n = -1 := by
        rw [← pow_add, show l + n = n + l by ring]; exact ho.neg_one_pow
      have h2 : (-1 : ℝ) ^ (n + l + 1) = 1 := by
        rw [pow_succ, ho.neg_one_pow]; ring
      rw [h1] at hfin
      rw [h2]
      nlinarith [hfin]

/-! ### The two branch radii at one angle -/

/-- **`Forgacs2017RationalDenominator` Remark 4.**  The angle sum decreases in the
radius, so a smaller branch index carries a larger radius: `τ(θ; n-1) ≤ τ(θ; l)`
for every `l ≤ n - 1` whose branch exists at `θ`. -/
theorem ftTau_principal_le {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hl : l ≤ n - 1) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hbl : FTBranchAt a r l θ)
    (hbp : FTBranchAt a r (n - 1) θ) :
    ftTau a r (n - 1) θ ≤ ftTau a r l θ := by
  by_contra hcon
  push Not at hcon
  have hlt := ftAngleSum_lt hn ha hθ (ftTau_pos hbl) hcon
  rw [ftAngleSum_ftTau hbl, ftAngleSum_ftTau hbp] at hlt
  have h1 : ((n - 1 : ℕ) : ℝ) * π < (l : ℝ) * π := by linarith
  have h2 : (n - 1 : ℕ) < l := by exact_mod_cast lt_of_mul_lt_mul_right h1 pi_pos.le
  omega

/-! ### The closing squeeze, run on the principal branch -/

/-- **The closing step of `Forgacs2017RationalDenominator` Prop. 1.**  With the
inner zero placed on the index-`l` branch at angle `φ`, its angle is `θ`.

**Differs from the paper's route.**  Their squeeze runs on the *intermediate*
index: `τ(θ*;l) ≤ τ ≤ τ(θ;l)`, and continuity of `τ(·;l)` then supplies an angle
`θ̃` between `θ*` and `θ` with `τ(θ̃;l) = τ`.  That needs the index-`l` branch to
exist at `θ` as well as at `θ*`, and it need not: the index-`l` branch lives only
on `(0, min(π/r, lπ/(n-r)))`, and `not_arc_wide_of_two_mul_lt` exhibits an angle
of the viewing arc outside it whenever `2r < n`.

The squeeze here runs on the *principal* index instead, in the other direction:
`τ(φ;n-1) ≤ σ ≤ τ(θ;n-1)`, where the left inequality is `ftTau_principal_le` at
`φ` — the one angle where the index-`l` branch is known to exist — and the right
is the containment `‖w‖ ≤ τ`.  Continuity of `τ(·;n-1)`, which holds across the
whole arc by `ftBranchAt_of_arc_principal`, supplies `ψ` between `φ` and `θ` with
`τ(ψ;n-1) = σ`.  Both branch values then read as the chord product at the *same*
radius `σ`, and the two strict monotonicities close it exactly as theirs do.
Nothing is assumed about the index-`l` branch away from `φ`, so the index
condition disappears rather than being weakened. -/
theorem ftProp1_closing_principal {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hpar : Even (n + l + 1)) (hl : l ≤ n - 1)
    {θ φ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) (hφ : φ ∈ Ioo 0 (π / r))
    (hbl : FTBranchAt a r l φ)
    (hle : ftTau a r l φ ≤ ftTau a r (n - 1) θ)
    (hzeq : ftBranchZ a c r l φ = ftBranchZ a c r (n - 1) θ) :
    φ = θ := by
  have hbp : ∀ ψ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) ψ :=
    fun ψ hψ => ftBranchAt_of_arc_principal hn ha hr hnr hψ
  have hparp : Even (n + (n - 1) + 1) := even_add_pred_add_one hn
  have hφπ : φ ∈ Ioo 0 π := ftArc_subset hr hφ
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  set σ : ℝ := ftTau a r l φ with hσdef
  have hσ0 : 0 < σ := ftTau_pos hbl
  have hσr : (0 : ℝ) < σ ^ r := by positivity
  -- the principal radius at `φ` is below `σ`, and at `θ` above it
  have hlo : ftTau a r (n - 1) φ ≤ σ := ftTau_principal_le hn ha hl hφπ hbl (hbp φ hφ)
  have huIcc : uIcc φ θ ⊆ Ioo 0 (π / r) := (Set.ordConnected_Ioo).uIcc_subset hφ hθ
  have hcont : ContinuousOn (ftTau a r (n - 1)) (uIcc φ θ) := fun x hx =>
    (continuousAt_ftTau hn ha hr (huIcc hx) hbp).continuousWithinAt
  obtain ⟨ψ, hψ, hψτ⟩ := intermediate_value_uIcc hcont
    (by rw [Set.mem_uIcc]; exact Or.inl ⟨hlo, hle⟩)
  have hψarc : ψ ∈ Ioo 0 (π / r) := huIcc hψ
  have hψπ : ψ ∈ Ioo 0 π := ftArc_subset hr hψarc
  -- both branch values are the chord product at the radius `σ`
  have hZψ : ftBranchZ a c r (n - 1) ψ = c * ftChordProd a σ ψ / σ ^ r :=
    ftBranchZ_eq_chordProd ha hparp hψπ (hbp ψ hψarc) hψτ
  have hZφ : ftBranchZ a c r l φ = c * ftChordProd a σ φ / σ ^ r :=
    ftBranchZ_eq_chordProd ha hpar hφπ hbl rfl
  have hZθ : ftBranchZ a c r (n - 1) θ = c * ftChordProd a σ φ / σ ^ r := by
    rw [← hzeq, hZφ]
  have hFmono : StrictMonoOn (fun x => c * ftChordProd a σ x / σ ^ r) (Ioo 0 π) := by
    intro x hx y hy hxy
    have hlt := (ftChordProd_strictMonoOn hn ha hσ0) hx hy hxy
    change c * ftChordProd a σ x / σ ^ r < c * ftChordProd a σ y / σ ^ r
    rw [div_lt_div_iff_of_pos_right hσr]
    exact mul_lt_mul_of_pos_left hlt hc
  have hE1 : ∀ x ∈ Ioo (0 : ℝ) π, ∀ y ∈ Ioo (0 : ℝ) π,
      (c * ftChordProd a σ x / σ ^ r < c * ftChordProd a σ y / σ ^ r ↔ x < y) :=
    fun x hx y hy => hFmono.lt_iff_lt hx hy
  have hE2 : ∀ x ∈ Ioo (0 : ℝ) (π / r), ∀ y ∈ Ioo (0 : ℝ) (π / r),
      (ftBranchZ a c r (n - 1) x < ftBranchZ a c r (n - 1) y ↔ x < y) :=
    fun x hx y hy => (ftBranchZ_strictMonoOn hn ha hc hr hparp hbp).lt_iff_lt hx hy
  have hlow : ψ < φ ↔ ψ < θ := by
    rw [← hE1 ψ hψπ φ hφπ, ← hZψ, ← hZθ, hE2 ψ hψarc θ hθ]
  have hhiw : φ < ψ ↔ θ < ψ := by
    rw [← hE1 φ hφπ ψ hψπ, ← hZψ, ← hZθ, hE2 θ hθ ψ hψarc]
  rcases lt_trichotomy φ θ with hlt | heq | hgt
  · rw [uIcc_of_le hlt.le] at hψ
    have hψθ : ψ = θ := by
      by_contra hne
      exact absurd (hlow.2 (lt_of_le_of_ne hψ.2 hne)) (not_lt.2 hψ.1)
    exact absurd (hhiw.1 (by rw [hψθ]; exact hlt)) (by rw [hψθ]; exact lt_irrefl θ)
  · exact heq
  · rw [uIcc_comm, uIcc_of_le hgt.le] at hψ
    have hψθ : ψ = θ := by
      by_contra hne
      exact absurd (hhiw.2 (lt_of_le_of_ne hψ.1 (Ne.symm hne))) (not_lt.2 hψ.2)
    exact absurd (hlow.1 (by rw [hψθ]; exact hgt)) (by rw [hψθ]; exact lt_irrefl θ)

/-- **No branch at an index the range condition excludes.**  Clause (i) of
`Forgacs2017RationalDenominator` Lemma 2 forces `∑_k θ_k > nψ`, so a prescribed
sum `rψ + lπ` at most `nψ` is unreachable.  This is
`FTBranchExistence.not_exists_ftAngleSystem_of_le` read on `FTBranchAt`. -/
theorem not_ftBranchAt_of_le {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) (hle : (r : ℝ) * ψ + l * π ≤ n * ψ) :
    ¬ FTBranchAt a r l ψ := by
  rintro ⟨τ, hτ, hsum⟩
  exact not_exists_ftAngleSystem_of_le hn hle
    ⟨fun k => ftAngle (a k) τ ψ, fun k => (ftAngle_mem_Ioo (ha k) hτ hψ).1, hsum⟩

/-- **`hidx` is refuted off `n ≤ 2r`.**  At `2r < n` the index `l = 1` admits no
branch at `ψ = π/(n-r)`, which lies inside the viewing arc exactly because
`r < n - r`.  So the hypothesis `ft_minModulus_at_branch` carries is not merely
unproved outside `ftBranchAt_arc_of_le_two_mul`'s range — it is false there, and
that range is sharp.  `ftProp1_closing_principal` is what a general proof uses
instead: it squeezes along the principal branch, which exists across the whole
arc, so no angle outside `(0, min(π/r, lπ/(n-r)))` is ever visited. -/
theorem not_arc_wide_of_two_mul_lt {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (h2 : 2 * r < n) :
    ¬ (∀ l : ℕ, l < n → 1 ≤ l → ∀ ψ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r l ψ) := by
  intro hcon
  have hπ := pi_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrn : (2 : ℝ) * r < n := by exact_mod_cast h2
  have hd : (0 : ℝ) < (n : ℝ) - r := by linarith
  have hd1 : (1 : ℝ) < (n : ℝ) - r := by linarith
  have hψ0 : 0 < π / ((n : ℝ) - r) := div_pos hπ hd
  have hψπ : π / ((n : ℝ) - r) < π := by rw [div_lt_iff₀ hd]; nlinarith
  have hψr : π / ((n : ℝ) - r) < π / r :=
    div_lt_div_of_pos_left hπ hr0 (by linarith)
  have hmul : ((n : ℝ) - r) * (π / ((n : ℝ) - r)) = π := by field_simp
  refine not_ftBranchAt_of_le hn ha ⟨hψ0, hψπ⟩ ?_
    (hcon 1 (by omega) le_rfl _ ⟨hψ0, hψr⟩)
  push_cast
  nlinarith [hmul]

/-- The intermediate index is arc-wide solvable whenever `n ≤ 2r`, which is what
`ftBranchAt_of_arc_range` needs at `l = 1` and hence at every `l ≥ 1`.  With
`not_arc_wide_of_two_mul_lt` this makes `n ≤ 2r` exactly the range on which the
paper's own closing squeeze has a branch to be continuous along. -/
theorem ftBranchAt_arc_of_le_two_mul {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (h2 : n ≤ 2 * r) :
    ∀ l : ℕ, l < n → 1 ≤ l → ∀ ψ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r l ψ := by
  intro l hl hl1
  refine ftBranchAt_of_arc_range hn ha hr hl ?_ (Or.inl hl1)
  calc n ≤ 2 * r := h2
    _ ≤ (l + 1) * r := Nat.mul_le_mul_right r (by omega)

/-! ### `hmin` at the constructed branch -/

/-- **`thm:FT-geometry`'s `hmin` for the constructed branch**, and so
`Forgacs2017RationalDenominator` Props. 1--2 on the admissible class: at each
angle of the viewing arc the principal pair are the only zeros of the pencil in
the closed disk of radius `τ(θ)`.

`hcone` is their two paragraphs placing the argument of an inner zero, and it is
the only hypothesis: everything else is discharged here — the conjugation into the
lower half plane, the quantization of the angle sum, the identification of `‖w‖`
with `τ(φ; l)` and of `z` with `z(φ; l)`, the containment, and the closing squeeze
of their Prop. 1 through `ftProp1_closing_principal`. -/
theorem ft_minModulus_at_branch_of_or {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hcone : FTArgumentCone (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))) :
    FTMinModulusGap (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) := by
  intro θ hθ w hw hne hne'
  by_contra hcon
  push Not at hcon
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hbp : FTBranchAt a r (n - 1) θ := ftBranchAt_of_arc_principal hn ha hr hnr hθ
  have hparp : Even (n + (n - 1) + 1) := even_add_pred_add_one hn
  have hzpos : 0 < ftBranchZ a c r (n - 1) θ := ftBranchZ_pos ha hc hparp hθπ hbp
  have hargw := hcone θ hθ w hw hcon
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hargw
    simp at hargw
  have hσ : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  -- conjugate into the lower half plane; the excluded pair is conjugation-stable
  obtain ⟨v, hv, hvroot, hvarc⟩ : ∃ v : ℂ, (v = w ∨ v = (starRingEnd ℂ) w) ∧
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval v = 0 ∧
      v = ftArcPoint ‖w‖ |Complex.arg w| := by
    rcases lt_or_ge (Complex.arg w) 0 with h | h
    · exact ⟨w, Or.inl rfl, hw, by rw [abs_of_neg h]; exact eq_ftArcPoint_neg_arg w⟩
    · exact ⟨(starRingEnd ℂ) w, Or.inr rfl,
        ftDen_eval_conj_eq_zero (hasRealCoeffs_ftRootPoly c a) hw,
        by rw [abs_of_nonneg h]; exact conj_eq_ftArcPoint_arg w⟩
  rw [hvarc] at hvroot
  -- the quantization
  obtain ⟨l, hl, -, hsum, hsign⟩ :=
    exists_ftAngleSum_index_of_root hn ha hc hr hσ hargw.1 hargw.2 hvroot
  have hφarc : |Complex.arg w| ∈ Ioo (0 : ℝ) (π / r) := hargw
  have hφπ : |Complex.arg w| ∈ Ioo 0 π := ftArc_subset hr hφarc
  have hpar : Even (n + l + 1) := by
    rcases Nat.even_or_odd (n + l + 1) with he | ho
    · exact he
    · rw [ho.neg_one_pow] at hsign; nlinarith
  -- the branch at index `l` carries the inner zero
  have hbat : FTBranchAt a r l (|Complex.arg w|) := ⟨‖w‖, hσ, hsum⟩
  have hτl : ‖w‖ = ftTau a r l (|Complex.arg w|) := ftTau_eq_of hn ha hφπ hσ hsum
  -- and the same spectral parameter
  have hzeq : ftBranchZ a c r l (|Complex.arg w|) = ftBranchZ a c r (n - 1) θ := by
    have hkey := ftBranch_ftArcPoint_eq_ftBranchZ (a := a) (r := r) (l := l) c ha hφπ hbat
    have hbr := (ftDen_eq_zero_iff_ftBranch (Q := ftRootPoly c a) (r := r)
      (z := ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ))
      (t := ftArcPoint ‖w‖ (|Complex.arg w|)) (ftArcPoint_ne_zero hσ.ne')).1 hvroot
    rw [hτl] at hbr
    simp only [ftBranch, eval_ftRootPoly] at hbr
    rw [hkey] at hbr
    exact (Complex.ofReal_inj.1 hbr).symm
  -- the two containments, and the closing squeeze
  have hlo : ftTau a r l (|Complex.arg w|) ≤ ftTau a r (n - 1) θ := by rw [← hτl]; exact hcon
  have hφθ : |Complex.arg w| = θ :=
    ftProp1_closing_principal hn ha hc hr hnr hpar (by omega) hθ hφarc hbat hlo hzeq
  -- so the inner zero is the branch point itself
  have hnormeq : ‖w‖ = ftTau a r (n - 1) θ := by
    have h2 : ‖w‖ = ftTau a r l θ := by rw [hτl, hφθ]
    have hpl : ftTau a r (n - 1) θ ≤ ftTau a r l θ := by
      have h := ftTau_principal_le hn ha (show l ≤ n - 1 by omega) hφπ hbat
        (ftBranchAt_of_arc_principal hn ha hr hnr hφarc)
      rwa [hφθ] at h
    linarith [hcon, hpl, h2]
  have hvval : v = (starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ) := by
    rw [hvarc, hφθ, hnormeq]
    exact ftArcPoint_eq_conj_ftPrincipal a r (n - 1) θ
  rcases hv with rfl | hconj
  · exact hne' hvval
  · refine hne ?_
    have := congrArg (starRingEnd ℂ) (hconj ▸ hvval : (starRingEnd ℂ) w = _)
    simpa using this

/-- **`thm:FT-geometry`'s `hmin` for the constructed branch**, with the cone
condition as its only hypothesis.  `ft_minModulus_at_branch_of_or` is the same
with `2 ≤ n` relaxed to what the argument actually consumes, which is that the
branch exists across the arc. -/
theorem ft_minModulus_at_branch {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hcone : FTArgumentCone (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))) :
    FTMinModulusGap (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) :=
  ft_minModulus_at_branch_of_or (by omega) ha hc hr (Or.inl hn2) hcone

/-- **`ft_minModulus_at_branch` with a redundant range hypothesis.**  `n ≤ 2r` was
load-bearing while the closing squeeze ran on the intermediate index; it is not
any more.  Kept so that consumers written against that form still elaborate. -/
theorem ft_minModulus_at_branch_of_le_two_mul {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (_h2r : n ≤ 2 * r)
    (hcone : FTArgumentCone (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))) :
    FTMinModulusGap (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) :=
  ft_minModulus_at_branch hn2 ha hc hr hcone

/-- **`ft_geometry_at_branch` with `hmin` discharged**, in the finite
upper-endpoint convention of `eq:ab-def`. -/
theorem ft_geometry_at_branch_of_cone {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hcone : FTArgumentCone (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r
      (n - 1))) {b : ℝ}
    (hzb : Filter.Tendsto (ftBranchZ a c r (n - 1))
      (nhdsWithin (π / r) (Ioo 0 (π / r))) (nhds b)) :
    ∃ za : ℝ,
      ftBranchZ a c r (n - 1) '' Ioo 0 (π / r) = Ioo za b
        ∧ FTPrincipalPair (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))
        ∧ FTPrincipalDisk (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) :=
  ft_geometry_at_branch hn2 ha hc hr hzb
    (ft_minModulus_at_branch hn2 ha hc hr hcone)

/-- **`ft_geometry_at_branch_unbounded` with `hmin` discharged**, the `b = +∞`
convention of `eq:ab-def`. -/
theorem ft_geometry_at_branch_unbounded_of_cone {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hcone : FTArgumentCone (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)))
    (hzb : Filter.Tendsto (ftBranchZ a c r (n - 1))
      (nhdsWithin (π / r) (Ioo 0 (π / r))) Filter.atTop) :
    ∃ za : ℝ,
      ftBranchZ a c r (n - 1) '' Ioo 0 (π / r) = Ioi za
        ∧ FTPrincipalPair (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1))
        ∧ FTPrincipalDisk (ftRootPoly c a) r (ftBranchZ a c r (n - 1)) (ftTau a r (n - 1)) :=
  ft_geometry_at_branch_unbounded hn2 ha hc hr hzb
    (ft_minModulus_at_branch hn2 ha hc hr hcone)

end ForgacsTran
