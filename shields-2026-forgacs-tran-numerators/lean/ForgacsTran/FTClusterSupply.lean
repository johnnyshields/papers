/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.FTGeometryAssembly
import ForgacsTran.FTBranchZRate

/-!
# The lower cluster's hypotheses, discharged at the branch

`FTMinModulus.exists_cluster_normalized_expansion_of_pencil` proves
`eq:lower-cluster-expansion` at the pencil from five inputs it cannot reach:
four about the principal branch, and the scalar identity saying the cluster
directions are the Rouché model's own roots.  All five are objects of
`FTBranchZRate` and `FTGeometryAssembly`, which sit *above* `FTMinModulus` in
the import graph, so the composition has to happen here.

Proved here:

## Main statements

* `ftRootPoly_factor_of_fiber` — the pencil numerator factored at its repeated
  smallest zero, `Q = (X - x_1)^ρq` with `q` explicit and `q(x_1) ≠ 0`.
* `clusterAlpha_pow_eq_neg` — `α_j^ρ = -(-x_1/sin(π/ρ))^ρ`, the value the sign
  question turns on.
* `model_identity_of_branch` — the scalar identity at the branch's own rate,
  which is where the two factors of `(-1)^ρ` cancel against `ω_j^ρ = -1`.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Weighted dominance»
(`sec:dominance`) — the supply side of `thm:weighted-dominance`'s `hexp₀`.

## Tags

lower cluster, hypothesis discharge, Forgacs-Tran branch
-/

namespace ForgacsTran

open Polynomial

/-! ### The pencil numerator at its repeated smallest zero -/

/-- The cofactor of `eq:lower-cluster-expansion`'s repeated zero: what is left of
`ftRootPoly` once the `ρ` copies of `a_i` are divided out.  The sign `(-1)^ρ` is
carried explicitly because it is the whole content of the model identity. -/
noncomputable def ftFiberCofactor {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (ρ : ℕ) : Polynomial ℂ :=
  C ((-1 : ℂ) ^ ρ * (c : ℂ)) * ∏ k ∈ Sᶜ, (C ((a k : ℝ) : ℂ) - X)

/-- **`Q = (X - x_1)^ρ q` at the fiber.**  The `ρ` zeros of `ftRootPoly` equal to
`a_i` are exactly the members of `S`, so the product splits and the `ρ` linear
factors `a_i - t` become `(-1)^ρ(t - a_i)^ρ`. -/
theorem ftRootPoly_factor_of_fiber {n ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    {i : Fin n} (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (c : ℝ) :
    ftRootPoly c a = (X - C ((a i : ℝ) : ℂ)) ^ ρ * ftFiberCofactor c a S ρ := by
  classical
  rw [ftRootPoly, ftFiberCofactor, ← Finset.prod_mul_prod_compl S]
  have hfib : ∏ k ∈ S, (C ((a k : ℝ) : ℂ) - X) = (C ((a i : ℝ) : ℂ) - X) ^ ρ := by
    rw [Finset.prod_congr rfl (fun k hk => by rw [(hS k).mp hk]), Finset.prod_const, hcard]
  have hneg : (C ((a i : ℝ) : ℂ) - X) ^ ρ
      = (-1 : ℂ[X]) ^ ρ * (X - C ((a i : ℝ) : ℂ)) ^ ρ := by
    rw [← mul_pow]
    congr 1
    ring
  have hC : C ((-1 : ℂ) ^ ρ * (c : ℂ)) = (-1 : ℂ[X]) ^ ρ * C (c : ℂ) := by
    rw [map_mul, map_pow]
    congr 2
    simp
  rw [hfib, hneg, hC]
  ring

/-- The cofactor does not vanish at the repeated zero: every remaining zero is a
different one, and the leading constant is nonzero. -/
theorem eval_ftFiberCofactor_ne_zero {n ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    {i : Fin n} (hS : ∀ k, k ∈ S ↔ a k = a i) {c : ℝ} (hc : c ≠ 0) :
    (ftFiberCofactor c a S ρ).eval ((a i : ℝ) : ℂ) ≠ 0 := by
  classical
  rw [ftFiberCofactor, eval_mul, eval_C, eval_prod]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) ?_
  · exact_mod_cast hc
  · refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
    simp only [eval_sub, eval_C, eval_X, sub_ne_zero]
    have hkS : k ∉ S := Finset.mem_compl.mp hk
    have : a k ≠ a i := fun h => hkS ((hS k).mpr h)
    exact_mod_cast this

/-! ### The model identity, at the branch's own rate -/

/-- `α_j^ρ = -(-x_1/sin(π/ρ))^ρ`, from `ω_j^ρ = -1`.  This is the sign the model
identity turns on: the `(-1)^ρ` here has to cancel the one
`ftRootPoly_factor_of_fiber` puts in `q(x_1)`, and it is `ω_j^ρ = -1` that makes
it do so rather than double it. -/
theorem clusterAlpha_pow_eq_neg {x₁ : ℝ} {ρ : ℕ} (hρ : 1 ≤ ρ) (j : ℕ) :
    clusterAlpha x₁ ρ j ^ ρ
      = -((-(x₁ : ℂ) / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) ^ ρ) := by
  rw [clusterAlpha, div_pow, mul_pow, clusterOmega_pow hρ, div_pow]
  ring

/-- **The cluster directions are the Rouché model's own roots.**  At the value
`FTBranchZRate.tendsto_ftBranchZ_div_pow` gives for `z_0`,

`q(x_1)α_j^ρ + z_0x_1^r = 0`,

which is `FTMinModulus.exists_cluster_normalized_expansion_of_pencil`'s `hmodel`
discharged.  Two factors of `(-1)^ρ` meet — one from writing `∏(a_k - t)` as
`(t - x_1)^ρq(t)`, one from `α_j = -x_1ω_j/sin(π/ρ)` — and they cancel against
`ω_j^ρ = -1` rather than reinforcing.  Nothing about the modulus is at issue: the
two sides have equal modulus by construction, and the identity is the statement
that they also have equal argument. -/
theorem model_identity_of_branch {n ρ r : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    {i : Fin n} (hρ : 2 ≤ ρ) (hai : 0 < a i) (c : ℝ) :
    (ftFiberCofactor c a S ρ).eval ((a i : ℝ) : ℂ) * clusterAlpha (a i) ρ 1 ^ ρ
      + ((c * ((a i / Real.sin (Real.pi / ρ)) ^ ρ * ∏ k ∈ Sᶜ, (a k - a i))
            / a i ^ r : ℝ) : ℂ) * ((a i : ℝ) : ℂ) ^ r = 0 := by
  classical
  have hρ1 : 1 ≤ ρ := by omega
  have hs : 0 < Real.sin (Real.pi / ρ) := sin_pi_div_pos hρ
  have haiC : ((a i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hai.ne'
  have hsq : ((-1 : ℂ) ^ ρ) * ((-1 : ℂ) ^ ρ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  set A : ℂ := (((a i : ℝ) : ℂ) / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) ^ ρ with hA
  set P : ℂ := ∏ k ∈ Sᶜ, (((a k : ℝ) : ℂ) - ((a i : ℝ) : ℂ)) with hP
  have hE : (ftFiberCofactor c a S ρ).eval ((a i : ℝ) : ℂ)
      = (-1 : ℂ) ^ ρ * (c : ℂ) * P := by
    rw [ftFiberCofactor, eval_mul, eval_C, eval_prod, hP]
    simp only [eval_sub, eval_C, eval_X]
  have hneg : ((-((a i : ℝ) : ℂ)) / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) ^ ρ
      = (-1 : ℂ) ^ ρ * A := by
    rw [hA, ← mul_pow]
    congr 1
    ring
  have hz : ((c * ((a i / Real.sin (Real.pi / ρ)) ^ ρ * ∏ k ∈ Sᶜ, (a k - a i))
        / a i ^ r : ℝ) : ℂ) = (c : ℂ) * (A * P) / ((a i : ℝ) : ℂ) ^ r := by
    rw [hA, hP]
    push_cast
    ring
  rw [hE, clusterAlpha_pow_eq_neg hρ1 1, hneg, hz,
    div_mul_cancel₀ _ (pow_ne_zero r haiC)]
  linear_combination (-(c : ℂ) * P * A) * hsq

/-! ### The four principal-branch inputs, and the supply theorem -/

/-- The zeros outside the fiber are bounded away from `a_i` by a fixed ratio, which
is the `hgap` `exists_principal_expansion_of_branch` consumes.  Finitely many
zeros, each strictly above `a_i`, so their infimum is too. -/
theorem exists_fiber_gap {n : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)} {i : Fin n}
    (ha : ∀ k, 0 < a k) (hS : ∀ k, k ∈ S ↔ a k = a i) (hmin : ∀ k, a i ≤ a k) :
    ∃ cg : ℝ, 0 < cg ∧ ∀ k ∉ S, a i * (1 + cg) < a k := by
  classical
  have hai : 0 < a i := ha i
  rcases (Sᶜ : Finset (Fin n)).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun k hk => ?_⟩
    exact absurd (Finset.mem_compl.mpr hk) (by rw [hE]; simp)
  · have hmgt : a i < (Sᶜ).inf' hne (fun k => a k) := by
      rw [Finset.lt_inf'_iff]
      intro k hk
      have hkS : k ∉ S := Finset.mem_compl.mp hk
      rcases lt_or_eq_of_le (hmin k) with h | h
      · exact h
      · exact absurd ((hS k).mpr h.symm) hkS
    refine ⟨((Sᶜ).inf' hne (fun k => a k) - a i) / (2 * a i),
      div_pos (by linarith only [hmgt]) (by linarith only [hai]), fun k hk => ?_⟩
    have hle : (Sᶜ).inf' hne (fun k => a k) ≤ a k :=
      Finset.inf'_le _ (Finset.mem_compl.mpr hk)
    have hexp : a i * (1 + ((Sᶜ).inf' hne (fun k => a k) - a i) / (2 * a i))
        = a i + ((Sᶜ).inf' hne (fun k => a k) - a i) / 2 := by
      field_simp
    rw [hexp]
    linarith only [hle, hmgt]

/-- **`thm:weighted-dominance`'s `hexp₀`, at the branch.**  Every input of
`FTMinModulus.exists_cluster_normalized_expansion_of_pencil` is discharged at
the real objects: the pencil is `ftRootPoly`, the spectral parameter is
`ftBranchZ`, the principal point is `ftPrincipal (ftTau …)`, and the normalizing
radius is `ftTau` itself.  What comes out is `ρ` roots of the pencil, one per
cluster direction, whose normalized expansions are
`1 + [(cos(π/ρ) - ω_i)/sin(π/ρ)]δ + O(δ^2)`.

Nothing is left as a hypothesis about the branch.  The model identity is
`model_identity_of_branch` at the rate `FTBranchZRate.tendsto_ftBranchZ_div_pow`
states; the principal expansion is `exists_principal_expansion_of_branch`; the
principal point is a root by `FTGeometryAssembly.ft_branch_root_and_pos`, which
also gives `τ > 0`, hence `τ = ‖t_p‖`; and `τ ≥ x_1/2` on a window because `τ`
converges to `x_1` at the endpoint. -/
theorem cluster_normalized_expansion_at_branch {n r ρ : ℕ} {a : Fin n → ℝ}
    {S : Finset (Fin n)} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {c : ℝ} (hc : 0 < c) :
    ∃ C₀ ε : ℝ, 0 ≤ C₀ ∧ 0 < ε ∧ ∃ g : ℝ → Fin ρ → ℂ,
      (∀ m : Fin ρ, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
        (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)).eval (g δ m) = 0) ∧
      (∀ m : Fin ρ, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
        ‖g δ m / ((ftTau a r (n - 1) δ : ℝ) : ℂ)
          - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ)
              - clusterOmega ρ ((m : ℕ) + 1))
            / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ C₀ * δ ^ 2) := by
  classical
  have hai : 0 < a i := ha i
  have hn : 0 < n := by omega
  have hρ1 : 1 ≤ ρ := by omega
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hiS : i ∈ S := (hS i).2 rfl
  obtain ⟨j, hj⟩ : (S.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hiS, hcard]; omega
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hjS : j ∈ S := Finset.mem_of_mem_erase hj
  obtain ⟨cg, hcg, hgap⟩ := exists_fiber_gap ha hS hmin
  -- the principal index is `j = 0`
  have hp0 : clusterOmega ρ 0
      = Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * Complex.I) := by
    rw [clusterOmega, clusterAngle]
    norm_num
    ring_nf
  have hjpre : (clusterOmega ρ 0).re = Real.cos (Real.pi / ρ) := by
    rw [clusterOmega_re, clusterAngle]
    have harg : (2 * ((0 : ℕ) : ℝ) - 1) * Real.pi / ρ = -(Real.pi / ρ) := by
      push_cast; ring
    rw [harg, Real.cos_neg]
  obtain ⟨Cp, εp, hCp, hεp, hpexp⟩ :=
    exists_principal_expansion_of_branch hn2 ha hr hS hcard hρ hmin hjS hji hcg hgap hp0
  obtain ⟨hbroot, hτpos⟩ := ft_branch_root_and_pos (a := a) c hn ha hr (Or.inl hn2)
  -- `τ` stays in the window
  have hτlim : Filter.Tendsto (ftTau a r (n - 1)) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (a i)) :=
    tendsto_ftTau_nhdsGT_zero_of_repeated_min hn2 ha hr (Ne.symm hji)
      ((hS j).1 hjS).symm hmin
  have hwinev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      a i / 2 < ftTau a r (n - 1) δ :=
    hτlim.eventually_const_lt (by linarith only [hai])
  rw [eventually_nhdsWithin_iff] at hwinev
  obtain ⟨εw, hεw, hwball⟩ := Metric.eventually_nhds_iff.mp hwinev
  -- one window for all four
  set ε₁ : ℝ := min (min εp (εw / 2)) (Real.pi / r / 2) with hε₁def
  have hπr : (0 : ℝ) < Real.pi / r := div_pos Real.pi_pos hrR
  have hε₁ : 0 < ε₁ :=
    lt_min (lt_min hεp (by linarith only [hεw])) (by linarith only [hπr])
  have hδπ : ∀ δ : ℝ, 0 < δ → δ ≤ ε₁ → δ ∈ Set.Ioo (0 : ℝ) (Real.pi / r) := by
    intro δ hδ hδe
    refine ⟨hδ, ?_⟩
    have h1 : δ ≤ Real.pi / r / 2 := le_trans hδe (min_le_right _ _)
    linarith only [h1, hπr]
  have hδw : ∀ δ : ℝ, 0 < δ → δ ≤ ε₁ → a i / 2 < ftTau a r (n - 1) δ := by
    intro δ hδ hδe
    refine hwball ?_ (Set.mem_Ioi.mpr hδ)
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    have h1 : δ ≤ εw / 2 := le_trans hδe (le_trans (min_le_left _ _) (min_le_right _ _))
    linarith only [h1, hεw]
  -- the spectral rate, cast
  set z₀ : ℝ := c * ((a i / Real.sin (Real.pi / ρ)) ^ ρ * ∏ k ∈ Sᶜ, (a k - a i))
    / a i ^ r with hz₀def
  have hProd : (0 : ℝ) < ∏ k ∈ Sᶜ, (a k - a i) := by
    refine Finset.prod_pos fun k hk => ?_
    have hkS : k ∉ S := Finset.mem_compl.mp hk
    rcases lt_or_eq_of_le (hmin k) with h | h
    · linarith only [h]
    · exact absurd ((hS k).mpr h.symm) hkS
  have hz₀pos : 0 < z₀ := by
    rw [hz₀def]
    have hs : 0 < Real.sin (Real.pi / ρ) := sin_pi_div_pos hρ
    positivity
  have hz₀ : ((z₀ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz₀pos.ne'
  have hzrate : Filter.Tendsto
      (fun δ : ℝ => ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ) / (δ : ℂ) ^ ρ)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds ((z₀ : ℝ) : ℂ)) := by
    have hreal := tendsto_ftBranchZ_div_pow hn2 ha hr hS hcard hρ hmin hc
    have hcast := (Complex.continuous_ofReal.tendsto _).comp hreal
    refine hcast.congr fun δ => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  refine exists_cluster_normalized_expansion_of_pencil (x₁ := a i) (ρ := ρ) (r := r)
    (q := ftFiberCofactor c a S ρ)
    (z := fun δ => ((ftBranchZ a c r (n - 1) δ : ℝ) : ℂ)) (z₀ := ((z₀ : ℝ) : ℂ))
    (tp := fun δ => ftPrincipal (ftTau a r (n - 1)) δ) (τ := ftTau a r (n - 1))
    (jp := 0) (Cp := Cp) (ε₁ := ε₁)
    hai hρ (ftRootPoly_factor_of_fiber hS hcard c)
    (eval_ftFiberCofactor_ne_zero hS hc.ne') hz₀ hzrate ?_ hCp hε₁ hjpre
    (fun δ hδ hδe => hbroot δ (hδπ δ hδ hδe)) ?_
    (fun δ hδ hδe => (norm_ftPrincipal_eq (hτpos δ (hδπ δ hδ hδe))).symm)
    (fun δ hδ hδe => le_of_lt (hδw δ hδ hδe))
  · rw [hz₀def]
    exact model_identity_of_branch hρ hai c
  · intro δ hδ hδe
    have := hpexp δ hδ (le_trans hδe (le_trans (min_le_left _ _) (min_le_left _ _)))
    rw [ftPrincipal]
    exact this

/-! ### The whole chain at one pencil

Every window in the composition is chosen after the one before it, so the
question the binders do not answer is whether the five are jointly satisfiable at
a real pencil rather than each on its own.  This settles it by instantiating.
-/

/-- **Non-vacuity, end to end.**  `Q(t) = (1-t)^3(3-t)` with `r = 1`: the smallest
zero `x_1 = 1` is triple, so `ρ = 3`, the fiber is `\{0,1,2\}`, and the remaining
zero `3` is outside it.  Every binder of `cluster_normalized_expansion_at_branch`
is discharged at once, so the theorem has content and the composed windows — the
Rouché radius, the ratio bound, the model's own `ε`, the principal expansion's,
and the `τ` window — are jointly satisfiable.

This is the smallest pencil whose lower cluster has a nonprincipal member:
`ρ - 2 = 1`. -/
theorem cluster_normalized_expansion_at_branch_nonvacuous :
    ∃ C₀ ε : ℝ, 0 ≤ C₀ ∧ 0 < ε ∧ ∃ g : ℝ → Fin 3 → ℂ,
      (∀ m : Fin 3, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
        (ftDen (ftRootPoly 1 ![1, 1, 1, 3]) 1
            ((ftBranchZ ![1, 1, 1, 3] 1 1 3 δ : ℝ) : ℂ)).eval (g δ m) = 0) ∧
      (∀ m : Fin 3, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
        ‖g δ m / ((ftTau ![1, 1, 1, 3] 1 3 δ : ℝ) : ℂ)
          - (1 + ((((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ)
              - clusterOmega 3 ((m : ℕ) + 1))
            / ((Real.sin (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ)) * (δ : ℂ))‖
          ≤ C₀ * δ ^ 2) := by
  refine cluster_normalized_expansion_at_branch (n := 4) (r := 1) (ρ := 3)
    (a := ![1, 1, 1, 3]) (S := {0, 1, 2}) (i := 0) (c := 1)
    (by norm_num) ?_ le_rfl ?_ (by decide) (by norm_num) ?_ one_pos
  · intro k
    fin_cases k <;> norm_num
  · intro k
    fin_cases k <;> simp
  · intro k
    fin_cases k <;> norm_num

end ForgacsTran
