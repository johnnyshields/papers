/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.ParameterCalculus

/-!
# The first Turán coefficient `α_m = ψ₁(a+m)`

Proves the `A`-row of `shields-2026-turan-bessel.tex`, `sec:coefficients` «Reciprocal-gamma
convolution
and canonical--microcanonical structure» (`thm:coefficients`): the first entry of
`eq:ABC-expansions` together with `eq:alpha`,
```
  A = Z_a^2 - Z Z_aa = ∑_{m≥0} S_m ψ₁(a+m) λ^m .
```

The paper's route is the `δ`-deformation `Z(a+δ,λ)Z(a-δ,λ)`, whose `λ^m` coefficient
`F_m(δ)` of `eq:Fdelta` is `lem:convolution` at `(α,β)=(a+δ,a-δ)`, and whose second
`δ`-derivative at `0` is `-2A` by `eq:A-second-delta` and `-2S_mψ₁(a+m)` by
`eq:F-second-delta`.  Formalized in that order, but with the `δ`-differentiation kept
on the **finite** side: `Fdelta` is the `m+1`-term sum, so `eq:F-second-delta` costs no
domination argument at all, and what crosses the infinite sum is only the Cauchy product
of two series already known to converge absolutely.

* `gammaPairInv2`, `hasDerivAt_scoreMul_gammaPairInv2` — the two-center weight
  `δ ↦ [Γ(u+δ)Γ(v-δ)]⁻¹` and its second `δ`-derivative at `0`.  The score
  `-ψ(u+δ)+ψ(v-δ)` no longer vanishes at `δ=0` when `u ≠ v`, so the square of the
  score survives alongside the two trigammas.
* `Fdelta`, `convolution_second_variation` — the finite deformed convolution and the
  identity `∑_i F_{m,i}''(0) = -2S_mψ₁(a+m)` it yields against the closed form
  `eq:Fdelta`.  This is the whole analytic content of `eq:alpha`.
* `Zparam1`, `Zparam2`, `Afun` — `Z_a`, `Z_aa` and `A` of `eq:Adef` as functions of
  `(a,λ)`, with `Zparam1_eq`/`Zparam2_eq` giving their termwise series.
* `hasSum_Afun`, `Afun_eq_tsum` — `eq:alpha`.  The Cauchy products of `Z_a·Z_a` and
  `Z·Z_aa` are compared coefficientwise; symmetrizing the `λ^m` coefficient under
  `i ↦ m-i` turns the mixed digamma terms into the score square that
  `convolution_second_variation` evaluates.  `Afun_pos` is the sign consequence.

Sorry-free, and axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Filter Topology Set Finset
open scoped BigOperators

namespace TuranBessel

variable {a : ℝ}

/-! ### Absolute convergence of the differentiated series -/

/-- A coefficient sequence with at most geometric growth leaves the `λ^k/(k!Γ(a+k))`
weights absolutely summable. -/
private theorem summable_norm_coeff_zterm {a lam : ℝ} (ha : 0 < a) {c : ℕ → ℝ} {C r : ℝ}
    (hC : ∀ k : ℕ, |c k| ≤ C * r ^ k) :
    Summable (fun k : ℕ => ‖c k * zterm a lam k‖) := by
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hmin : 0 < min a 1 := lt_min ha one_pos
  have hD : 0 < Real.Gamma a * min a 1 := mul_pos hGa hmin
  have hC0 : 0 ≤ C := by
    have h := le_trans (abs_nonneg (c 0)) (hC 0)
    simpa using h
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((Real.summable_pow_div_factorial (r * |lam|)).mul_left
      (C / (Real.Gamma a * min a 1)))
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hGk : 0 < Real.Gamma (a + (k : ℝ)) := Real.Gamma_pos_of_pos (by linarith)
  have hfk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hlow : Real.Gamma a * min a 1 ≤ Real.Gamma (a + (k : ℝ)) :=
    Gamma_mul_min_le_Gamma_add ha k
  have hnorm : ‖c k * zterm a lam k‖
      = |c k| * (|lam| ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, zterm, abs_div, abs_pow,
      abs_of_pos (mul_pos hfk hGk)]
  rw [hnorm]
  have h1 : |c k| * (|lam| ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ))))
      ≤ (C * r ^ k) * (|lam| ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))) :=
    mul_le_mul_of_nonneg_right (hC k) (by positivity)
  refine h1.trans ?_
  have hrk : 0 ≤ C * r ^ k := le_trans (abs_nonneg (c k)) (hC k)
  have h2 : |lam| ^ k / ((Nat.factorial k : ℝ) * Real.Gamma (a + (k : ℝ)))
      ≤ |lam| ^ k / ((Nat.factorial k : ℝ) * (Real.Gamma a * min a 1)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hlow hfk.le
  refine (mul_le_mul_of_nonneg_left h2 hrk).trans (le_of_eq ?_)
  rw [mul_pow]
  field_simp

/-- `∂_a Z` converges absolutely. -/
theorem summable_norm_dzterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ => ‖-realDigamma (a + (k : ℝ)) * zterm a lam k‖) := by
  refine summable_norm_coeff_zterm (C := 2 * |realDigamma a| + 1 / a) (r := 2) ha (fun k => ?_)
  have hk : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hpsi : |realDigamma (a + (k : ℝ))| ≤ |realDigamma a| + |realDigamma a| + (k : ℝ) / a :=
    abs_realDigamma_add_nat_le ha ⟨le_rfl, le_rfl⟩ k
  have hd : (k : ℝ) / a ≤ 1 / a * 2 ^ k := by
    rw [div_eq_mul_inv, one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  rw [abs_neg]
  nlinarith [abs_nonneg (realDigamma a), one_div_pos.2 ha]

/-- `∂_a² Z` converges absolutely. -/
theorem summable_norm_ddzterm (ha : 0 < a) (lam : ℝ) :
    Summable (fun k : ℕ =>
      ‖(realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))) * zterm a lam k‖) := by
  refine summable_norm_coeff_zterm
    (C := (2 * |realDigamma a| + 1 / a) ^ 2 + trigamma a) (r := 4) ha (fun k => ?_)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hak : 0 < a + (k : ℝ) := by linarith
  have hk : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h4k : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have h4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have hpsi : |realDigamma (a + (k : ℝ))| ≤ |realDigamma a| + |realDigamma a| + (k : ℝ) / a :=
    abs_realDigamma_add_nat_le ha ⟨le_rfl, le_rfl⟩ k
  have hd : (k : ℝ) / a ≤ 1 / a * 2 ^ k := by
    rw [div_eq_mul_inv, one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  have hbase : |realDigamma (a + (k : ℝ))| ≤ (2 * |realDigamma a| + 1 / a) * 2 ^ k := by
    nlinarith [abs_nonneg (realDigamma a), one_div_pos.2 ha]
  have hsq : realDigamma (a + (k : ℝ)) ^ 2 ≤ (2 * |realDigamma a| + 1 / a) ^ 2 * 4 ^ k := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hbase 2
    rw [sq_abs] at h
    calc realDigamma (a + (k : ℝ)) ^ 2 ≤ ((2 * |realDigamma a| + 1 / a) * 2 ^ k) ^ 2 := h
      _ = (2 * |realDigamma a| + 1 / a) ^ 2 * 4 ^ k := by rw [mul_pow, h4]
  have htri : trigamma (a + (k : ℝ)) ≤ trigamma a := trigamma_anti ha (by linarith)
  have htri0 : 0 ≤ trigamma (a + (k : ℝ)) := (trigamma_pos hak).le
  have hTa : 0 ≤ trigamma a := (trigamma_pos ha).le
  have hsq0 : 0 ≤ realDigamma (a + (k : ℝ)) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-! ### The parameter derivatives of `Z` and the scalar `A` -/

/-- `Z_a(a,λ) = ∂_a Z(a,λ)` (`eq:Zdef`, `eq:Adef`). -/
noncomputable def Zparam1 (a lam : ℝ) : ℝ := deriv (fun x : ℝ => Zfun x lam) a

/-- `Z_aa(a,λ) = ∂_a² Z(a,λ)` (`eq:Zdef`, `eq:Adef`). -/
noncomputable def Zparam2 (a lam : ℝ) : ℝ := deriv (deriv fun x : ℝ => Zfun x lam) a

/-- `A = Z_a² - Z Z_aa`, the leading entry of the matrix Turánian `eq:Tkt`
(`eq:Adef`). -/
noncomputable def Afun (a lam : ℝ) : ℝ := Zparam1 a lam ^ 2 - Zfun a lam * Zparam2 a lam

theorem Zparam1_eq (ha : 0 < a) (lam : ℝ) :
    Zparam1 a lam = ∑' k : ℕ, -realDigamma (a + (k : ℝ)) * zterm a lam k :=
  deriv_Zfun_param ha lam

theorem Zparam2_eq (ha : 0 < a) (lam : ℝ) :
    Zparam2 a lam
      = ∑' k : ℕ, (realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))) * zterm a lam k :=
  deriv_deriv_Zfun_param ha lam

/-! ### The two-center deformed gamma weight -/

/-- `δ ↦ [Γ(u+δ)Γ(v-δ)]⁻¹`, the summand weight of `eq:Fdelta` at index `i`, with
`u = a+i` and `v = a+m-i`. -/
noncomputable def gammaPairInv2 (u v d : ℝ) : ℝ := (Real.Gamma (u + d) * Real.Gamma (v - d))⁻¹

theorem gammaPairInv2_zero (u v : ℝ) :
    gammaPairInv2 u v 0 = (Real.Gamma u * Real.Gamma v)⁻¹ := by
  simp [gammaPairInv2]

/-- The score form of `∂_δ [Γ(u+δ)Γ(v-δ)]⁻¹`. -/
theorem hasDerivAt_gammaPairInv2 {u v d : ℝ} (h₁ : 0 < u + d) (h₂ : 0 < v - d) :
    HasDerivAt (gammaPairInv2 u v)
      ((-realDigamma (u + d) + realDigamma (v - d)) * gammaPairInv2 u v d) d := by
  have hG1 : Real.Gamma (u + d) ≠ 0 := (Real.Gamma_pos_of_pos h₁).ne'
  have hG2 : Real.Gamma (v - d) ≠ 0 := (Real.Gamma_pos_of_pos h₂).ne'
  have hu : HasDerivAt (fun e : ℝ => (Real.Gamma (u + e))⁻¹)
      (-realDigamma (u + d) / Real.Gamma (u + d)) d := by
    simpa using (hasDerivAt_inv_Gamma h₁).comp d ((hasDerivAt_id d).const_add u)
  have hv : HasDerivAt (fun e : ℝ => (Real.Gamma (v - e))⁻¹)
      (realDigamma (v - d) / Real.Gamma (v - d)) d := by
    have hcomp := (hasDerivAt_inv_Gamma h₂).comp d ((hasDerivAt_id d).const_sub v)
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    field_simp
  have hmul := hu.mul hv
  have hfun : gammaPairInv2 u v
      =ᶠ[𝓝 d] ((fun e : ℝ => (Real.Gamma (u + e))⁻¹) * fun e : ℝ => (Real.Gamma (v - e))⁻¹) := by
    filter_upwards with e
    simp [gammaPairInv2, Pi.mul_apply, mul_comm]
  refine (hmul.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [gammaPairInv2]
  field_simp

/-- **The two-center `eq:F-second-delta`.**  The `δ`-derivative of the score-times-weight
form at `δ = 0`, which is `∂_δ²|_0 [Γ(u+δ)Γ(v-δ)]⁻¹`: unlike the diagonal case `u = v`,
the score `ψ(v)-ψ(u)` need not vanish, so its square survives beside the two trigammas. -/
theorem hasDerivAt_scoreMul_gammaPairInv2 {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (fun d : ℝ => (-realDigamma (u + d) + realDigamma (v - d)) * gammaPairInv2 u v d)
      (((realDigamma v - realDigamma u) ^ 2 - trigamma u - trigamma v)
        * gammaPairInv2 u v 0) 0 := by
  have hb1 : HasDerivAt realDigamma (trigamma u) (u + id (0 : ℝ)) := by
    simp only [id_eq, add_zero]
    rw [← deriv_realDigamma_eq_trigamma hu]
    exact hasDerivAt_realDigamma' hu
  have hs1 : HasDerivAt (fun d : ℝ => realDigamma (u + d)) (trigamma u) 0 := by
    simpa using hb1.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add u)
  have hb2 : HasDerivAt realDigamma (trigamma v) (v - id (0 : ℝ)) := by
    simp only [id_eq, sub_zero]
    rw [← deriv_realDigamma_eq_trigamma hv]
    exact hasDerivAt_realDigamma' hv
  have hs2 : HasDerivAt (fun d : ℝ => realDigamma (v - d)) (-trigamma v) 0 := by
    simpa using hb2.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_sub v)
  have hscore : HasDerivAt (fun d : ℝ => -realDigamma (u + d) + realDigamma (v - d))
      (-trigamma u - trigamma v) 0 := by
    have h := hs1.neg.add hs2
    refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards with e
    simp
  have hg0 : HasDerivAt (gammaPairInv2 u v)
      ((-realDigamma (u + 0) + realDigamma (v - 0)) * gammaPairInv2 u v 0) 0 :=
    hasDerivAt_gammaPairInv2 (by linarith) (by linarith)
  refine (hscore.mul hg0).congr_deriv ?_
  simp only [add_zero, sub_zero]
  ring

/-- `∂_δ²|_0 [Γ(u+δ)Γ(v-δ)]⁻¹`, as an iterated `deriv`. -/
theorem hasDerivAt_deriv_gammaPairInv2 {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (deriv (gammaPairInv2 u v))
      (((realDigamma v - realDigamma u) ^ 2 - trigamma u - trigamma v)
        * gammaPairInv2 u v 0) 0 := by
  refine (hasDerivAt_scoreMul_gammaPairInv2 hu hv).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (show -u < (0 : ℝ) by linarith) hv] with d hd
  exact (hasDerivAt_gammaPairInv2 (by linarith [hd.1]) (by linarith [hd.2])).deriv

/-! ### The finite deformed convolution `F_m(δ)` -/

/-- `F_m(δ) = ∑_{i=0}^m [i!(m-i)!Γ(a+δ+i)Γ(a-δ+m-i)]⁻¹`, the `λ^m` coefficient of
`Z(a+δ,λ)Z(a-δ,λ)` (`eq:Fdelta`), kept as the finite sum. -/
noncomputable def Fdelta (a : ℝ) (m : ℕ) (d : ℝ) : ℝ :=
  ∑ i ∈ range (m + 1),
    (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
      * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d

/-- **`eq:Fdelta`.**  `lem:convolution` at `(α,β) = (a+δ,a-δ)` closes `F_m` for `|δ| < a`. -/
theorem Fdelta_eq_closed (m : ℕ) {d : ℝ} (hd : d ∈ Ioo (-a) a) :
    Fdelta a m d
      = poch (2 * a + (m : ℝ) - 1) m / (Nat.factorial m : ℝ) * gammaPairInv (a + (m : ℝ)) d := by
  have h1 : 0 < a + d := by linarith [hd.1]
  have h2 : 0 < a - d := by linarith [hd.2]
  have hconv := gamma_convolution h1 h2 m
  rw [show a + d + (a - d) + (m : ℝ) - 1 = 2 * a + (m : ℝ) - 1 by ring] at hconv
  rw [Fdelta]
  have hlhs : ∀ i ∈ range (m + 1),
      (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d
        = 1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)
            * Real.Gamma (a + d + (i : ℝ)) * Real.Gamma (a - d + ((m - i : ℕ) : ℝ))) := by
    intro i _
    rw [gammaPairInv2, show a + (i : ℝ) + d = a + d + (i : ℝ) by ring,
      show a + ((m - i : ℕ) : ℝ) - d = a - d + ((m - i : ℕ) : ℝ) by ring]
    field_simp
  rw [Finset.sum_congr rfl hlhs, hconv, gammaPairInv,
    show a + d + (m : ℝ) = a + (m : ℝ) + d by ring,
    show a - d + (m : ℝ) = a + (m : ℝ) - d by ring]
  have hfm : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  field_simp

/-- The termwise `δ`-derivative of `F_m`, valid on `|δ| < a`. -/
theorem hasDerivAt_Fdelta (m : ℕ) {d : ℝ} (hd : d ∈ Ioo (-a) a) :
    HasDerivAt (Fdelta a m)
      (∑ i ∈ range (m + 1),
        (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * ((-realDigamma (a + (i : ℝ) + d) + realDigamma (a + ((m - i : ℕ) : ℝ) - d))
              * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d)) d := by
  unfold Fdelta
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hmi : (0 : ℝ) ≤ ((m - i : ℕ) : ℝ) := Nat.cast_nonneg (m - i)
  exact (hasDerivAt_gammaPairInv2 (u := a + (i : ℝ)) (v := a + ((m - i : ℕ) : ℝ)) (d := d)
    (by linarith [hd.1]) (by linarith [hd.2])).const_mul _

/-- **`eq:F-second-delta` from the sum side.**  `F_m''(0)` read off the `m+1` summands. -/
theorem deriv_deriv_Fdelta_sum (ha : 0 < a) (m : ℕ) :
    deriv (deriv (Fdelta a m)) 0
      = ∑ i ∈ range (m + 1),
          (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
            * (((realDigamma (a + ((m - i : ℕ) : ℝ)) - realDigamma (a + (i : ℝ))) ^ 2
                  - trigamma (a + (i : ℝ)) - trigamma (a + ((m - i : ℕ) : ℝ)))
                * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) 0) := by
  have heq : deriv (Fdelta a m) =ᶠ[𝓝 (0 : ℝ)] fun d : ℝ =>
      ∑ i ∈ range (m + 1),
        (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * ((-realDigamma (a + (i : ℝ) + d) + realDigamma (a + ((m - i : ℕ) : ℝ) - d))
              * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d) := by
    filter_upwards [Ioo_mem_nhds (show -a < (0 : ℝ) by linarith) ha] with d hd
    exact (hasDerivAt_Fdelta m hd).deriv
  have hDderiv : HasDerivAt (fun d : ℝ =>
      ∑ i ∈ range (m + 1),
        (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * ((-realDigamma (a + (i : ℝ) + d) + realDigamma (a + ((m - i : ℕ) : ℝ) - d))
              * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) d))
      (∑ i ∈ range (m + 1),
        (1 / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)))
          * (((realDigamma (a + ((m - i : ℕ) : ℝ)) - realDigamma (a + (i : ℝ))) ^ 2
                - trigamma (a + (i : ℝ)) - trigamma (a + ((m - i : ℕ) : ℝ)))
              * gammaPairInv2 (a + (i : ℝ)) (a + ((m - i : ℕ) : ℝ)) 0)) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hmi : (0 : ℝ) ≤ ((m - i : ℕ) : ℝ) := Nat.cast_nonneg (m - i)
    exact (hasDerivAt_scoreMul_gammaPairInv2 (u := a + (i : ℝ)) (v := a + ((m - i : ℕ) : ℝ))
      (by linarith) (by linarith)).const_mul _
  exact (hDderiv.congr_of_eventuallyEq heq).deriv

/-- **The second variation of `lem:convolution`.**  Differentiating
`eq:asymmetric-convolution` twice in `δ` along `(α,β) = (a+δ,a-δ)` and evaluating at
`δ = 0` gives `eq:F-second-delta` in the form the coefficient of `λ^m` in `A` needs. -/
theorem convolution_second_variation (ha : 0 < a) (m : ℕ) :
    ∑ i ∈ range (m + 1),
        ((realDigamma (a + ((m - i : ℕ) : ℝ)) - realDigamma (a + (i : ℝ))) ^ 2
            - trigamma (a + (i : ℝ)) - trigamma (a + ((m - i : ℕ) : ℝ)))
          / ((Nat.factorial i : ℝ) * (Nat.factorial (m - i) : ℝ)
              * Real.Gamma (a + (i : ℝ)) * Real.Gamma (a + ((m - i : ℕ) : ℝ)))
      = -2 * (sweight a m * trigamma (a + (m : ℝ))) := by
  have hclosed : Fdelta a m =ᶠ[𝓝 (0 : ℝ)]
      fun d : ℝ => poch (2 * a + (m : ℝ) - 1) m / (Nat.factorial m : ℝ)
        * gammaPairInv (a + (m : ℝ)) d := by
    filter_upwards [Ioo_mem_nhds (show -a < (0 : ℝ) by linarith) ha] with d hd
    exact Fdelta_eq_closed m hd
  have hderiv : deriv (Fdelta a m) =ᶠ[𝓝 (0 : ℝ)]
      deriv (fun d : ℝ => poch (2 * a + (m : ℝ) - 1) m / (Nat.factorial m : ℝ)
        * gammaPairInv (a + (m : ℝ)) d) := hclosed.deriv
  have hkey : deriv (deriv (Fdelta a m)) 0 = -2 * (sweight a m * trigamma (a + (m : ℝ))) := by
    rw [hderiv.deriv_eq]
    exact deriv_deriv_Fdelta ha m
  rw [deriv_deriv_Fdelta_sum ha m] at hkey
  rw [← hkey]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gammaPairInv2_zero]
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hmi : (0 : ℝ) ≤ ((m - i : ℕ) : ℝ) := Nat.cast_nonneg (m - i)
  have hG1 : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : (0 : ℝ) < Real.Gamma (a + ((m - i : ℕ) : ℝ)) := Real.Gamma_pos_of_pos (by linarith)
  have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfmi : (0 : ℝ) < (Nat.factorial (m - i) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - i)
  field_simp

/-! ### `eq:alpha` -/

/-- **`eq:ABC-expansions` and `eq:alpha`.**  `A = Z_a² - Z Z_aa` has the expansion
`∑_m S_m ψ₁(a+m) λ^m`.  The `λ^m` coefficient is the Cauchy product
`∑_{i+j=m}[ψ(a+i)ψ(a+j) - ψ(a+j)² + ψ₁(a+j)]/(i!j!Γ(a+i)Γ(a+j))`; symmetrizing under
`i ↦ m-i` turns the digamma part into `-(ψ(a+j)-ψ(a+i))²/2`, and
`convolution_second_variation` evaluates the result. -/
theorem hasSum_Afun (ha : 0 < a) (lam : ℝ) :
    HasSum (fun m : ℕ => sweight a m * trigamma (a + (m : ℝ)) * lam ^ m) (Afun a lam) := by
  set z : ℕ → ℝ := fun k => zterm a lam k with hz
  set dz : ℕ → ℝ := fun k => -realDigamma (a + (k : ℝ)) * zterm a lam k with hdz
  set ddz : ℕ → ℝ := fun k =>
    (realDigamma (a + (k : ℝ)) ^ 2 - trigamma (a + (k : ℝ))) * zterm a lam k with hddz
  have hnz : Summable (fun k => ‖z k‖) := summable_norm_zterm ha lam
  have hndz : Summable (fun k => ‖dz k‖) := summable_norm_dzterm ha lam
  have hnddz : Summable (fun k => ‖ddz k‖) := summable_norm_ddzterm ha lam
  -- the two Cauchy products
  have hprod1 : Zparam1 a lam ^ 2
      = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, dz kl.1 * dz kl.2 := by
    rw [Zparam1_eq ha lam, sq]
    exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hndz hndz
  have hprod2 : Zfun a lam * Zparam2 a lam
      = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, z kl.1 * ddz kl.2 := by
    rw [Zparam2_eq ha lam, Zfun]
    exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnz hnddz
  have hs1 : Summable (fun n : ℕ => ∑ kl ∈ Finset.antidiagonal n, dz kl.1 * dz kl.2) :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hndz hndz).of_norm
  have hs2 : Summable (fun n : ℕ => ∑ kl ∈ Finset.antidiagonal n, z kl.1 * ddz kl.2) :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hnz hnddz).of_norm
  -- coefficientwise identification
  have hcoeff : ∀ n : ℕ,
      (∑ kl ∈ Finset.antidiagonal n, dz kl.1 * dz kl.2)
        - (∑ kl ∈ Finset.antidiagonal n, z kl.1 * ddz kl.2)
      = sweight a n * trigamma (a + (n : ℝ)) * lam ^ n := by
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Finset.sum_sub_distrib]
    -- abbreviations
    set ψ : ℕ → ℝ := fun i => realDigamma (a + (i : ℝ)) with hψ
    set t : ℕ → ℝ := fun i => trigamma (a + (i : ℝ)) with ht
    set w : ℕ → ℝ := fun i =>
      1 / ((Nat.factorial i : ℝ) * (Nat.factorial (n - i) : ℝ)
        * Real.Gamma (a + (i : ℝ)) * Real.Gamma (a + ((n - i : ℕ) : ℝ))) with hw
    have hterm : ∀ i ∈ range (n + 1),
        dz i * dz (n - i) - z i * ddz (n - i)
          = lam ^ n * (w i * (ψ i * ψ (n - i) - ψ (n - i) ^ 2 + t (n - i))) := by
      intro i hi
      have him : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hpow : lam ^ i * lam ^ (n - i) = lam ^ n := by
        rw [← pow_add, Nat.add_sub_cancel' him]
      have hGi : (0 : ℝ) < Real.Gamma (a + (i : ℝ)) :=
        Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
      have hGj : (0 : ℝ) < Real.Gamma (a + ((n - i : ℕ) : ℝ)) :=
        Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) (n - i); linarith)
      have hfi : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
      have hfj : (0 : ℝ) < (Nat.factorial (n - i) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (n - i)
      have hstep : dz i * dz (n - i) - z i * ddz (n - i)
          = (lam ^ i * lam ^ (n - i))
              * (w i * (ψ i * ψ (n - i) - ψ (n - i) ^ 2 + t (n - i))) := by
        simp only [hdz, hz, hddz, hw, hψ, ht, zterm]
        field
      rw [hstep, hpow]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    -- symmetrize under `i ↦ n - i`
    set g : ℕ → ℝ := fun i => w i * (ψ i * ψ (n - i) - ψ (n - i) ^ 2 + t (n - i)) with hg
    set h : ℕ → ℝ := fun i => w i * (ψ i * ψ (n - i) - ψ i ^ 2 + t i) with hh
    have hrefl : ∑ i ∈ range (n + 1), g i = ∑ i ∈ range (n + 1), h i := by
      rw [← Finset.sum_range_reflect g (n + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hidx : n + 1 - 1 - i = n - i := by omega
      have hback : n - (n - i) = i := by omega
      simp only [hg, hh, hidx, hback, hw]
      ring
    have hsum2 : 2 * ∑ i ∈ range (n + 1), g i
        = ∑ i ∈ range (n + 1), (g i + h i) := by
      rw [Finset.sum_add_distrib, ← hrefl]; ring
    have hgh : ∀ i ∈ range (n + 1), g i + h i
        = -(((ψ (n - i) - ψ i) ^ 2 - t i - t (n - i)) * w i) := by
      intro i _
      simp only [hg, hh]
      ring
    have hvar := convolution_second_variation ha n
    have hvar' : ∑ i ∈ range (n + 1), ((ψ (n - i) - ψ i) ^ 2 - t i - t (n - i)) * w i
        = -2 * (sweight a n * trigamma (a + (n : ℝ))) := by
      rw [← hvar]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hψ, ht, hw]
      rw [div_eq_mul_inv]
      field_simp
    have htwice : 2 * ∑ i ∈ range (n + 1), g i
        = 2 * (sweight a n * trigamma (a + (n : ℝ))) := by
      rw [hsum2, Finset.sum_congr rfl hgh, Finset.sum_neg_distrib, hvar']
      ring
    have hgval : ∑ i ∈ range (n + 1), g i = sweight a n * trigamma (a + (n : ℝ)) := by
      linarith
    rw [hgval]
    ring
  -- assemble
  have hfe : (fun m : ℕ => sweight a m * trigamma (a + (m : ℝ)) * lam ^ m)
      = fun n : ℕ => (∑ kl ∈ Finset.antidiagonal n, dz kl.1 * dz kl.2)
          - ∑ kl ∈ Finset.antidiagonal n, z kl.1 * ddz kl.2 := by
    funext n
    exact (hcoeff n).symm
  rw [Afun, hprod1, hprod2, hfe]
  exact hs1.hasSum.sub hs2.hasSum

/-- `eq:alpha` as an equality of sums. -/
theorem Afun_eq_tsum (ha : 0 < a) (lam : ℝ) :
    Afun a lam = ∑' m : ℕ, sweight a m * trigamma (a + (m : ℝ)) * lam ^ m :=
  (hasSum_Afun ha lam).tsum_eq.symm

/-- `A > 0` for `a > 0` and `λ ≥ 0`: every coefficient of `eq:alpha` is `S_m ψ₁(a+m) > 0`.
This is the leading-entry positivity the matrix Turánian `eq:Tkt` needs alongside
`Δ^{(κ)} > 0`. -/
theorem Afun_pos {a lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) : 0 < Afun a lam := by
  rw [Afun_eq_tsum ha lam]
  refine (hasSum_Afun ha lam).summable.tsum_pos (fun m => ?_) 0 ?_
  · have ham : 0 < a + (m : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) m; linarith
    exact mul_nonneg (mul_pos (sweight_pos ha m) (trigamma_pos ham)).le (pow_nonneg hlam m)
  · simpa using mul_pos (sweight_pos ha 0) (trigamma_pos ha)

end TuranBessel
