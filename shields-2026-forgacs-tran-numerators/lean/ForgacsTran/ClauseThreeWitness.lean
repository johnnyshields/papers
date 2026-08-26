/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.ClauseThreeComposition
import ForgacsTran.ClauseThreeMonomial
import ForgacsTran.QuadraticWitness

/-!
# The clause-3 composition is not vacuous, and its constants do not move

`ClauseThreeComposition.phaseSupply_of_ftChainGeom` is conditional on a seventeen-fold
conjunction and on `eq:dominance-bound`, and a conditional theorem whose hypotheses nothing
satisfies proves nothing while looking finished.  A witness at one weight is not enough
either: **the whole content of clause 3 is that `C_0` and `C_1` do not move when the numerator
does**, so a certificate has to run a family with `deg B_N` genuinely varying and show the
constants standing still across it.

The Favard case `(deg Q, r) = (2, 1)` of `rem:quadratic-case` supplies both, once the weight
is allowed to be `B = t^k`.  `QuadraticWitness` has done the analytic work at `B = 1`: the
principal pair exhausts a quadratic denominator, so `eq:principal-decomposition` is exact and
`eq:dominance-bound` holds on the whole arc.  `ClauseThreeMonomial` carries that across the
shift: `F_M^{(t^k)} = F_{M-k}^{(1)}` and `𝒲_{t^k} = t^k𝒲_1`, so the remainder
still vanishes and the amplitude acquires the argument `kθ + π/2`.

What the family exhibits is exactly the separation the clause asserts:

| | varies with the weight | fixed before it |
|---|---|---|
| `deg B` | `k` | |
| `eq:phase-derivative-bound` | `κ = k` | |
| `eq:linear-phase-variation` | | `κ_0 = 0`, `κ_1 = π` |
| `eq:retained-range` | | `h = 1` |
| the defect | `4 + 3k` | `C_0`, `C_1` |

`κ` grows with the weight and the defect grows with it linearly, while `κ_0`,
`κ_1` and `h` are literals in the statement of `witness_phaseSupply_pow`, standing
outside the `∀ k`.  That is clause 3.

**Scope**, in two parts.  What is certified is the hypothesis list of
`phaseSupply_of_ftChainGeom`, over weights of every degree — that theorem takes the weight `B`
directly, and `t^k` runs through every degree.  What is **not** certified is that each `t^k` is
the canonical reduced weight `B_N` of a *proper* numerator over this pencil: `hB` of
`clauseThree_of_ftGeometry` asks for `B_N = laurentWeight Q r N`, and
`thm:main`'s properness hypothesis caps `deg_tN` below `max\{deg Q, r\} = 2` here, so `t^k` for `k ≥
2`
would have to be reached through the `z`-dependence of `N` rather than read off directly.
Nothing here proves that it is.

Nor does this certify `clauseThree_of_ftGeometry`'s `∀ N`, which asks for the geometry at
every numerator over one fixed pencil and so cannot be met by any single family of `B`; that
quantifier is what `thm:FT-geometry` and `cor:linear-phase-variation` supply, one numerator at
a time.

Nothing here has a counterpart in the manuscript: `rem:quadratic-case` records the Favard
branch but poses no witness, and a non-vacuity certificate is an addition to the paper rather
than a different route through one of its proofs.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `rem:quadratic-case` in the service
of `thm:main` clause 3.

## Tags

witness, non-vacuity, defect constants
-/

namespace ForgacsTran

open Real Set Polynomial

/-! ### The arc, the chain, and the shifted data -/

/-- The retained arc `[1/M, π - 1/M]` of `eq:retained-range` at `h = 1`, taken whole as the
single component of `eq:Omega-M`: the Favard amplitude has no zero on `(0, π)`, so no window
is deleted. -/
noncomputable def witGeomArc (M : ℕ) : Set ℝ := Icc (1 / (M : ℝ)) (π - 1 / (M : ℝ))

/-- The monotone chain of `phaseSupply_of_chain` for the single component: `w 0` its left
endpoint, every later `w i` its right endpoint. -/
noncomputable def witChain (M : ℕ) : ℕ → ℝ :=
  fun i => if i = 0 then 1 / (M : ℝ) else π - 1 / (M : ℝ)

/-- The coefficient sequence at the weight `t^k`: the `B = 1` sequence, shifted. -/
noncomputable def witPpow (k M : ℕ) : Polynomial ℝ := witP (M - k)

/-- The argument branch at the weight `t^k`: `arg𝒲_{t^k} = kθ + π/2`, so its
derivative is `k` — the numerator-dependent `κ` of `eq:phase-derivative-bound`. -/
noncomputable def witPsi (k : ℕ) : ℝ → ℝ := fun θ => (k : ℝ) * θ + π / 2

theorem witPsi_apply (k : ℕ) (θ : ℝ) : witPsi k θ = (k : ℝ) * θ + π / 2 := rfl

theorem witPpow_map {k M : ℕ} (hkM : k ≤ M) :
    (witPpow k M).map (algebraMap ℝ ℂ) = ftCoeffPoly witQ (X ^ k) 1 M := by
  rw [witPpow, witP_map, ftCoeffPoly_X_pow, if_neg (by omega)]

theorem witPpow_natDegree (k M : ℕ) :
    ((witPpow k M).map (algebraMap ℝ ℂ)).natDegree = M - k := by
  rw [witPpow, witP_natDegree]

private theorem wit_one_le_pi_sub {M : ℕ} (hM : 1 ≤ M) :
    1 / (M : ℝ) ≤ π - 1 / (M : ℝ) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h1 : 1 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have := Real.pi_gt_three
  linarith

private theorem wit_sin_pos {M : ℕ} (hM : 1 ≤ M) {θ : ℝ} (hθ : θ ∈ witGeomArc M) :
    0 < Real.sin θ := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
  rw [witGeomArc] at hθ
  exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hpos hθ.1)
    (lt_of_le_of_lt hθ.2 (by linarith))

/-! ### The amplitude at the weight `t^k` -/

theorem wit_ftPrincipal_eq (θ : ℝ) :
    ftPrincipal witTau θ = Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [ftPrincipal, witTau_eq]
  simp [quadMod_one]

/-- The Favard amplitude at `B = 1`, in closed form on the arc. -/
theorem wit_ftAmp_one {θ : ℝ} (hsin : 0 < Real.sin θ) :
    ftAmp witQ 1 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ)
      = Complex.I / ((2 * Real.sin θ : ℝ) : ℂ) := by
  rw [witQ_eq, witZfun_eq, witTau_eq,
    quad_ftAmp (by norm_num) (by norm_num) (-4) hsin.ne', quadHalf_one]
  norm_num

/-- **The amplitude at the weight `t^k`.**  `𝒲_{t^k} = t_+^k𝒲_1` and
`t_+ = e^{iθ}` here, so the modulus is unchanged and the argument gains `kθ`. -/
theorem wit_ftAmp_pow (k : ℕ) {θ : ℝ} (hsin : 0 < Real.sin θ) :
    ftAmp witQ (X ^ k) 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ)
      = Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)
        * (Complex.I / ((2 * Real.sin θ : ℝ) : ℂ)) := by
  rw [ftAmp_X_pow, wit_ftAmp_one hsin, wit_ftPrincipal_eq, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem wit_ftAmp_pow_ne_zero (k : ℕ) {θ : ℝ} (hsin : 0 < Real.sin θ) :
    ftAmp witQ (X ^ k) 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ) ≠ 0 := by
  have hc : (0 : ℝ) < 2 * Real.sin θ := by linarith
  have hne : ((2 * Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [wit_ftAmp_pow k hsin]
  exact mul_ne_zero (Complex.exp_ne_zero _) (div_ne_zero Complex.I_ne_zero hne)

theorem wit_ftPrincipalAmp_pow (k : ℕ) {θ : ℝ} (hsin : 0 < Real.sin θ) :
    ftPrincipalAmp witQ (X ^ k) 1 witZ witTau θ = 1 / (2 * Real.sin θ) := by
  have hc : (0 : ℝ) < 2 * Real.sin θ := by linarith
  rw [ftPrincipalAmp, wit_ftAmp_pow k hsin, norm_mul, Complex.norm_exp_ofReal_mul_I,
    one_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc]

/-- **The polar form at the weight `t^k`**, with the branch `ψ_k(θ) = kθ + π/2`
of `witPsi`.  Its derivative is the constant `k`, which is the numerator's own `κ`. -/
theorem wit_polar_pow (k : ℕ) {θ : ℝ} (hsin : 0 < Real.sin θ) :
    ftAmp witQ (X ^ k) 1 ((witZ θ : ℝ) : ℂ) (ftPrincipal witTau θ)
      = ((ftPrincipalAmp witQ (X ^ k) 1 witZ witTau θ : ℝ) : ℂ)
        * Complex.exp ((witPsi k θ : ℂ) * Complex.I) := by
  have hc : (0 : ℝ) < 2 * Real.sin θ := by linarith
  have hne : ((2 * Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hI : Complex.exp ((((π / 2 : ℝ)) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  have hsplit : Complex.exp ((witPsi k θ : ℂ) * Complex.I)
      = Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((((π / 2 : ℝ)) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, witPsi_apply]
    congr 1
    push_cast
    ring
  rw [wit_ftAmp_pow k hsin, wit_ftPrincipalAmp_pow k hsin, hsplit, hI,
    Complex.ofReal_div, Complex.ofReal_one]
  ring

/-! ### The remainder at the weight `t^k` -/

/-- **The remainder under a monomial weight, at any modulus.**  `t^k` shifts the coefficient
sequence by `k` and multiplies the amplitude by `t_+^k`; the two shifts cancel in
`eq:principal-decomposition` up to the real scalar `τ^k`, which the normalization
`τ^{M+1}` carries.  So `R_M^{(t^k)} = τ^k R_{M-k}^{(1)}` on any denominator whose
principal branch has positive modulus.

The scalar matters for `r > 1`: there the Forgács--Tran branch has `τ(θ) → 0` at an
endpoint, so a version assuming `τ ≡ 1` covers only pencils with constant modulus —
which is the `(deg Q, r) = (2,1)` Favard case and nothing else. -/
theorem ftRemainder_X_pow_of_pos {Q : Polynomial ℂ} {r k M : ℕ} {z τ : ℝ → ℝ} {θ : ℝ}
    (hτ : 0 < τ θ) (hkM : k ≤ M) :
    ftRemainder Q (X ^ k) r z τ M θ
      = (τ θ) ^ k * ftRemainder Q 1 r z τ (M - k) θ := by
  have hc : ((τ θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have ht : ftPrincipal τ θ ≠ 0 := by
    rw [ftPrincipal]
    exact mul_ne_zero hc (Complex.exp_ne_zero _)
  have hsplit : M + 1 = k + (M - k + 1) := by omega
  have h1 : (ftCoeffPoly Q (X ^ k) r M).eval ((z θ : ℝ) : ℂ)
      = (ftCoeffPoly Q 1 r (M - k)).eval ((z θ : ℝ) : ℂ) := by
    rw [ftCoeffPoly_X_pow, if_neg (by omega)]
  have h2 : ftAmp Q (X ^ k) r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
        / (ftPrincipal τ θ) ^ (M + 1)
      = ftAmp Q 1 r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
        / (ftPrincipal τ θ) ^ (M - k + 1) := by
    rw [ftAmp_X_pow, hsplit, pow_add, mul_div_mul_left _ _ (pow_ne_zero k ht)]
  -- the whole bracket scales by the real `τ^k`
  set A : ℂ := ftAmp Q 1 r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      / (ftPrincipal τ θ) ^ (M - k + 1) with hA
  set E : ℂ := (ftCoeffPoly Q 1 r (M - k)).eval ((z θ : ℝ) : ℂ) with hE
  have hre : (((τ θ : ℝ) : ℂ) ^ (M + 1) * A).re
      = (τ θ) ^ k * ((((τ θ : ℝ) : ℂ) ^ (M - k + 1) * A).re) := by
    rw [hsplit, pow_add, mul_assoc, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rw [ftRemainder, ftRemainder, h1, h2, ← hA, ← hE, hre]
  rw [show ((2 * ((τ θ) ^ k * ((((τ θ : ℝ) : ℂ) ^ (M - k + 1) * A).re)) : ℝ) : ℂ)
      = (((τ θ) ^ k : ℝ) : ℂ) * ((2 * ((((τ θ : ℝ) : ℂ) ^ (M - k + 1) * A).re) : ℝ) : ℂ) by
    push_cast; ring]
  rw [hsplit, pow_add, mul_assoc, ← Complex.ofReal_pow]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos hτ k)]

/-- **The remainder is shift-invariant when the modulus is one**, the `τ ≡ 1`
specialization `ClauseThreeWitness`'s Favard pencil runs on. -/
theorem ftRemainder_X_pow {Q : Polynomial ℂ} {r k M : ℕ} {z τ : ℝ → ℝ} {θ : ℝ}
    (hτ : τ θ = 1) (hkM : k ≤ M) :
    ftRemainder Q (X ^ k) r z τ M θ = ftRemainder Q 1 r z τ (M - k) θ := by
  rw [ftRemainder_X_pow_of_pos (by rw [hτ]; norm_num) hkM, hτ, one_pow, one_mul]

/-- **`eq:dominance-bound` at the weight `t^k`.**  The principal pair exhausts a quadratic
denominator whatever the weight, so past the shift the remainder vanishes identically and the
bound holds with no deleted window at all. -/
theorem witness_dominance_pow (k : ℕ) :
    ∀ M : ℕ, max 1 k ≤ M → ∀ θ : ℝ, 1 / (M : ℝ) ≤ θ → θ ≤ π - 1 / (M : ℝ) →
      θ ∉ (∅ : Set ℝ) →
      ftRemainder witQ (X ^ k) 1 witZ witTau M θ
        ≤ ftPrincipalAmp witQ (X ^ k) 1 witZ witTau θ / 2 := by
  intro M hM θ h1 h2 _
  have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
  have hkM : k ≤ M := le_trans (le_max_right _ _) hM
  have hsin : 0 < Real.sin θ := wit_sin_pos hM1 ⟨h1, h2⟩
  have hτ1 : witTau θ = 1 := by rw [witTau_eq]; exact quadMod_one
  have hzero : ftRemainder witQ (X ^ k) 1 witZ witTau M θ = 0 := by
    rw [ftRemainder_X_pow hτ1 hkM, witQ_eq, witZfun_eq, witTau_eq]
    exact quad_ftRemainder_eq_zero (by norm_num) (by norm_num) (-4) (M - k) hsin
  have hamp : (0 : ℝ) ≤ ftPrincipalAmp witQ (X ^ k) 1 witZ witTau θ := norm_nonneg _
  rw [hzero]
  linarith

/-! ### The geometry, over the whole family -/

/-- **The branch geometry at every weight degree.**  `FTChainGeom` holds for the Favard pencil
`Q = 1 - 4t + t²`, `r = 1` at the weight `B = t^k`, on the retained arc of `eq:retained-range`
at `h = 1`, for every `k ≤ M`.

The three constants standing outside the weight are literals here — `hwin = 1`,
`κ_0 = 0`, `κ_1 = π` — while what the weight moves is `K = deg B = k`, the branch
`ψ_k`, and the phase-derivative constant `κ = k`.  That `κ < M + 1` is what puts
the onset at `M ≥ k`, exactly as `thm:main` clause 3 allows the onset to depend on the
numerator while the constants may not. -/
theorem witness_ftChainGeom_pow {k M : ℕ} (hkM : k ≤ M) (hM : 1 ≤ M) :
    FTChainGeom witQ (X ^ k) 1 witZ witTau (witPsi k) M (X ^ k : Polynomial ℂ).natDegree
      1 0 0 π 1 π (fun _ => (∅ : Set ℝ)) (Ioo 1 7) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hab : 1 / (M : ℝ) ≤ π - 1 / (M : ℝ) := wit_one_le_pi_sub hM
  have hapos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkM' : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hkM
  have hsubIcc : witGeomArc M ⊆ Icc 0 π := by
    rw [witGeomArc]
    exact Icc_subset_Icc hapos.le (by linarith)
  refine ⟨witGeomArc M, witChain M, 1, fun _ => (k : ℝ), (k : ℝ), ordConnected_Icc, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the arc is the retained range of `eq:retained-range`, and no window is deleted
    intro θ hθ
    rw [witGeomArc] at hθ
    exact ⟨hθ.1, hθ.2, by simp⟩
  · -- the chain is monotone
    intro i j hij
    change (if i = 0 then 1 / (M : ℝ) else π - 1 / (M : ℝ))
      ≤ (if j = 0 then 1 / (M : ℝ) else π - 1 / (M : ℝ))
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact hab
    · exact absurd hij (by omega)
    · exact le_rfl
  · intro i
    change (if i = 0 then 1 / (M : ℝ) else π - 1 / (M : ℝ))
      ∈ Icc (1 / (M : ℝ)) (π - 1 / (M : ℝ))
    split_ifs
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
  · -- one component, so the separation condition is vacuous
    intro i hi; omega
  · exact (quadratic_z_strictMonoOn (by norm_num) (by norm_num) (-4)).mono hsubIcc
  · intro θ _
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    rw [witZ_eq]
    exact ⟨by linarith, by linarith⟩
  · exact fun θ _ => by rw [witTau_eq]; simp only [quadMod_one]; norm_num
  · exact fun θ hθ => wit_ftAmp_pow_ne_zero k (wit_sin_pos hM hθ)
  · exact fun θ hθ => wit_polar_pow k (wit_sin_pos hM hθ)
  · -- `eq:phase-derivative-bound`: the branch is affine with slope `k`
    intro θ _
    change HasDerivAt (fun x : ℝ => (k : ℝ) * x + π / 2) ((k : ℝ)) θ
    simpa using ((hasDerivAt_id θ).const_mul (k : ℝ)).add_const (π / 2)
  · exact fun θ _ => by simp
  · -- `κ = k < M + 1`
    linarith
  · simp
  · -- the retained length: the single component is the whole arc
    rw [Finset.sum_range_one]
    change π / ((1 : ℕ) : ℝ) - 2 * 1 / (M : ℝ) - 0
      ≤ (π - 1 / (M : ℝ)) - 1 / (M : ℝ)
    have h2 : 2 * (1 : ℝ) / (M : ℝ) = 1 / (M : ℝ) + 1 / (M : ℝ) := by ring
    rw [h2]
    norm_num
  · simp
  · -- `eq:linear-phase-variation` at `κ₀ = 0`, `κ₁ = π`, both free of the weight
    have hmono : MonotoneOn (witPsi k) (witGeomArc M) := by
      intro x _ y _ hxy
      simp only [witPsi]
      nlinarith
    have hma : (1 / (M : ℝ)) ∈ witGeomArc M := by
      rw [witGeomArc]; exact ⟨le_rfl, hab⟩
    have hmb : (π - 1 / (M : ℝ)) ∈ witGeomArc M := by
      rw [witGeomArc]; exact ⟨hab, le_rfl⟩
    have heq := hmono.eVariationOn_eq hma hmb
    rw [witGeomArc, Set.inter_self] at heq
    rw [witGeomArc, heq, Polynomial.natDegree_X_pow]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [witPsi]
    nlinarith [mul_nonneg hkR hapos.le]

/-! ### The composition, run on the family -/

/-- **The phase supply at every weight degree.**  `phaseSupply_of_ftChainGeom` turns the
Favard geometry and `eq:dominance-bound` into the supply `prop:angular-discrepancy` consumes,
for every `k ≤ M`.

**This is the uniformity statement.**  `hwin = 1`, `κ_0 = 0` and `κ_1 = π` are
literals in the conclusion and do not mention `k`, while `K = deg(t^k) = k` and the branch
`ψ_k` do.  So the constants `defectC₀ hwin κ₀` and `defectC₁ κ₁` that
`ClauseThree.clauseThree` builds from them are the same at every weight degree. -/
theorem witness_phaseSupply_pow {k M : ℕ} (hkM : k ≤ M) (hM : 1 ≤ M) :
    PhaseSupply (witPpow k M) (witPsi k) witZ M (X ^ k : Polynomial ℂ).natDegree 1
      1 0 0 π (Ioo 1 7) :=
  phaseSupply_of_ftChainGeom (witPpow_map hkM) ordConnected_Ioo
    (by
      rw [Polynomial.natDegree_X_pow]
      have := Real.pi_pos
      positivity)
    (max_le hM hkM) (witness_dominance_pow k) (witness_ftChainGeom_pow hkM hM)

/-- **The count clause 3 delivers, across the family.**  At the weight `t^k` and every index
`M ≥ k`, the coefficient polynomial has at least `M - (4 + 3k)` distinct zeros inside
`I_{Q,r} = (1, 7)`.

The defect is `⌈ defectC₀\ 1\ 0 + defectC₁\ π · k⌉ = 4 + 3k`: it grows
linearly in `deg B`, with slope `defectC₁ π = 3` and intercept `4`, **neither of which
depends on `k`**.  The count grows with the index, so the conclusion is non-trivial as well as
non-empty, and the produced set falls short of `deg P = M - k` by `4 + 2k` — a defect linear
in the weight degree, which is the shape `thm:main` clause 3 asserts. -/
theorem witness_clauseThree_uniform {k M : ℕ} (hkM : k ≤ M) (hM : 1 ≤ M) :
    ∃ Z : Finset ℂ, M - (4 + 3 * k) ≤ Z.card ∧
      (∀ w ∈ Z, ((witPpow k M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftInterval 1 7) := by
  obtain ⟨Z, hcard, hroot, hmem⟩ :=
    exists_interiorZeros_of_phaseSupply (witPpow k M) hM le_rfl zero_le_one
      (witness_phaseSupply_pow hkM hM)
  refine ⟨Z, ?_, hroot, hmem⟩
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_lt_four
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hc4 : ⌈(5 / π + 2 : ℝ)⌉₊ = 4 := by
    refine (Nat.ceil_eq_iff (by norm_num)).2 ⟨?_, ?_⟩
    · have : (1 : ℝ) < 5 / π := by rw [lt_div_iff₀ hπ]; linarith
      push_cast; linarith
    · have : (5 : ℝ) / π ≤ 2 := by rw [div_le_iff₀ hπ]; linarith
      push_cast; linarith
  have hval : defectC₀ 1 0 + defectC₁ π * ((k : ℕ) : ℝ)
      = (5 / π + 2) + ((3 * k : ℕ) : ℝ) := by
    rw [defectC₀, defectC₁]
    push_cast
    field
  have hceil : ⌈defectC₀ 1 0 + defectC₁ π * ((k : ℕ) : ℝ)⌉₊ = 4 + 3 * k := by
    rw [hval, Nat.ceil_add_natCast (by positivity), hc4]
  rw [Polynomial.natDegree_X_pow, hceil, Nat.div_one] at hcard
  exact hcard

/-- **The count is unbounded.**  `witness_clauseThree_uniform` bounds the zero count below by
`M - (4 + 3k)`, and in `ℕ` that says *nothing* while `4 + 3k ≥ M` — at `k = 3` the bound is
empty for every `M ≤ 13`.  So the statement that the conclusion is non-trivial is this one:
at every weight degree the witness produces **arbitrarily many** distinct zeros in
`I_{Q,r}`. -/
theorem witness_clauseThree_uniform_unbounded (k n : ℕ) :
    ∃ (M : ℕ) (Z : Finset ℂ), n ≤ Z.card ∧
      (∀ w ∈ Z, ((witPpow k M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ ftInterval 1 7) := by
  obtain ⟨Z, hcard, hroot, hmem⟩ :=
    witness_clauseThree_uniform (k := k) (M := n + 4 + 3 * k) (by omega) (by omega)
  exact ⟨n + 4 + 3 * k, Z, by omega, hroot, hmem⟩

end ForgacsTran
