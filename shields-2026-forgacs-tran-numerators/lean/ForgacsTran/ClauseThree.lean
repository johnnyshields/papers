/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.ViewingAngle
import ForgacsTran.PhaseVariation
import ForgacsTran.SignAlternation
import ForgacsTran.LaurentReduction
import ForgacsTran.Amplitude

/-!
# The numerator-uniform defect

Clause 2 asserts *some* defect constant `C(Q, r, N)`.  Clause 3 asserts constants
`C₀ = C₀(Q, r)` and `C₁ = C₁(Q, r)`, **fixed before the numerator**, with defect at most
`C₀ + C₁ deg B_N`.  That binding is the whole content of the clause, and here it is visible in
the statement of `clauseThree` rather than asserted in prose: `defectC₀` and `defectC₁` are
bound outside the quantifier over numerators.

The proof is the counting argument of `prop:angular-discrepancy`, and it is elementary once
its inputs are named.  On a component of `eq:Omega-M` the phase `Φ_M` of `eq:Phi-def` is
strictly increasing, so it meets `πℤ` at least `(Φ(v) - Φ(u))/π - 1` times; at each such point
`eq:principal-decomposition` fixes the sign of the principal term and `thm:weighted-dominance`
transfers it to the whole coefficient, so consecutive phase points enclose a zero and the
component carries at least `(Φ(v) - Φ(u))/π - 2` of them.  Summing over the components, the
defect picks up `κ₁/π` per unit of `deg B` from `eq:linear-phase-variation` and a further `2`
from each of the `J ≤ K` amplitude windows — which is the slope-`2` envelope
`scripts/verify_equidistribution.py` measures against.

The angular parameter and the polynomial's variable are kept apart, as the manuscript keeps
them: `Φ_M`, the component lengths and `eq:retained-range` live in `θ`, while the zeros
produced live in `z(θ)` and land in `I_{Q,r}`.  The strictly monotone reparametrization `z`
of `thm:FT-geometry` is what carries one to the other, and it is an explicit argument
throughout.

Two of the three inputs are discharged from what is already proven, not assumed:

## Main statements

* `card_amplitudeZeros_le` — `J ≤ deg B` (`eq:amplitude-zero-count`), from
  `Amplitude.amplitude_zero_count`;
* `sum_abs_sub_le_of_eVariationOn` — the summed phase increments are a sub-sum of one
  partition sum, hence below `eVariationOn ψ`, which `eq:linear-phase-variation`
  (`PhaseVariation.linear_phase_variation_regular`) bounds by `κ₀ + κ₁ deg B`.

* `exists_phaseZeros` — the count on one component.
* `exists_phaseZeros_sum` — the components are disjoint, so the counts add.
* `angular_distinct_lower` — `eq:angular-distinct-lower`, with the defect split as
  `C₀ + C₁ K`.
* `PhaseSupply`, `exists_interiorZeros_of_phaseSupply` — the supply, and the `ℕ`-valued bound
  `Main.main_bound_interval_ofRecurrence` consumes.
* `phaseSupply_of_chain` — the supply assembled from one monotone chain, with the
  phase-variation input taken from `eq:linear-phase-variation`.
* `numeratorUniform_ceil`, `numeratorUniform_defect`, `clauseThree` — the clause.

## Implementation notes

What is **not** discharged is the phase supply itself — the existence of the components, the
strict monotonicity of `Φ_M`, and the sign at each phase point.  That is the analytic content
of `thm:weighted-dominance`, the same content `Bridge.FTInputs` carries for clause 2, and it
is carried here as the explicit hypothesis `PhaseSupply`.  So clause 3 is conditional on
exactly what clause 2 is conditional on, and no more.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair dominance and the
fixed-numerator theorem» (`subsec:proof`, `prop:angular-discrepancy`) and `thm:main` clause 3.

## Tags

numerator-uniform defect, exceptional zero, weight polynomial
-/

namespace ForgacsTran

open Real Set Finset

theorem stripSign_mul_succ (k : ℤ) : stripSign k * stripSign (k + 1) = -1 := by
  unfold stripSign
  rcases Int.even_or_odd k with hk | hk
  · have h1 : ¬ Even (k + 1) := by
      rw [Int.not_even_iff_odd]
      exact Even.add_one hk
    rw [if_pos hk, if_neg h1]; ring
  · have h0 : ¬ Even k := by rw [Int.not_even_iff_odd]; exact hk
    have h1 : Even (k + 1) := Odd.add_one hk
    rw [if_neg h0, if_pos h1]; ring

/-! ### The count on one component of `eq:Omega-M` -/

/-- Paper `prop:angular-discrepancy`, the phase count on one component of `eq:Omega-M`.
`Φ = Φ_M` of `eq:Phi-def` is strictly increasing on the component, and at each point where it
meets `πℤ` the coefficient carries the sign that `eq:principal-decomposition` predicts and
`thm:weighted-dominance` transfers to the whole coefficient.  Consecutive phase points
therefore enclose a zero, and the component carries at least `(Φ(v) - Φ(u))/π - 2` of them.

`hsign` is the analytic supply, stated outright rather than bundled: it is exactly what
`thm:weighted-dominance` delivers at a phase point. -/
theorem exists_phaseZeros
    (P : Polynomial ℝ) {Φ z : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hΦc : ContinuousOn Φ (Icc u v)) (hΦm : StrictMonoOn Φ (Icc u v))
    (hz : StrictMonoOn z (Icc u v))
    (hsign : ∀ θ ∈ Icc u v, ∀ k : ℤ, Φ θ = (k : ℝ) * π → 0 < stripSign k * P.eval (z θ)) :
    ∃ Z : Finset ℂ, ((Φ v - Φ u) / π - 2 : ℝ) ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' (Icc (z u) (z v))) := by
  classical
  have hπ : (0:ℝ) < π := Real.pi_pos
  set k₀ : ℤ := ⌈Φ u / π⌉ with hk₀
  set k₁ : ℤ := ⌊Φ v / π⌋ with hk₁
  have hb₀ : Φ u ≤ (k₀ : ℝ) * π := by
    have := Int.le_ceil (Φ u / π)
    rw [div_le_iff₀ hπ] at this
    exact this
  have hb₁ : ((k₁ : ℤ) : ℝ) * π ≤ Φ v := by
    have := Int.floor_le (Φ v / π)
    rw [le_div_iff₀ hπ] at this
    exact this
  by_cases hk : k₁ < k₀
  · refine ⟨∅, ?_, by simp, by simp⟩
    have h1 : (k₀ : ℝ) ≤ Φ u / π + 1 := by
      have := Int.ceil_lt_add_one (Φ u / π)
      linarith
    have h2 : Φ v / π - 1 ≤ (k₁ : ℝ) := by
      have := Int.sub_one_lt_floor (Φ v / π)
      linarith
    have h3 : ((k₁ : ℤ) : ℝ) ≤ ((k₀ : ℤ) : ℝ) - 1 := by exact_mod_cast Int.le_sub_one_of_lt hk
    have : Φ v / π - Φ u / π ≤ 1 := by linarith
    have hdiv : (Φ v - Φ u) / π = Φ v / π - Φ u / π := by ring
    simp only [Finset.card_empty, Nat.cast_zero, hdiv]
    linarith
  push Not at hk
  set n : ℕ := (k₁ - k₀).toNat with hn
  have hnk : ((n : ℤ)) = k₁ - k₀ := Int.toNat_of_nonneg (by omega)
  -- a phase point for each integer level in range
  have hex : ∀ j : Fin (n + 1), ∃ x ∈ Icc u v, Φ x = ((k₀ + (j : ℕ) : ℤ) : ℝ) * π := by
    intro j
    have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.1 j.isLt
    have hlow : Φ u ≤ ((k₀ + (j : ℕ) : ℤ) : ℝ) * π := by
      refine hb₀.trans ?_
      have hle : (k₀ : ℝ) ≤ ((k₀ + (j : ℕ) : ℤ) : ℝ) := by
        exact_mod_cast (by omega : (k₀ : ℤ) ≤ k₀ + (j : ℕ))
      nlinarith
    have hhigh : ((k₀ + (j : ℕ) : ℤ) : ℝ) * π ≤ Φ v := by
      refine le_trans ?_ hb₁
      have hle : ((k₀ + (j : ℕ) : ℤ) : ℝ) ≤ (k₁ : ℝ) := by
        have : (k₀ + (j : ℕ) : ℤ) ≤ k₁ := by omega
        exact_mod_cast this
      nlinarith
    have := intermediate_value_Icc huv hΦc ⟨hlow, hhigh⟩
    obtain ⟨x, hx, hxv⟩ := this
    exact ⟨x, hx, hxv⟩
  choose x hxmem hxval using hex
  have hxmono : StrictMono x := by
    intro i j hij
    have hlt : Φ (x i) < Φ (x j) := by
      rw [hxval i, hxval j]
      have : ((k₀ + (i : ℕ) : ℤ) : ℝ) < ((k₀ + (j : ℕ) : ℤ) : ℝ) := by
        have : (k₀ + (i : ℕ) : ℤ) < (k₀ + (j : ℕ) : ℤ) := by
          have : (i : ℕ) < (j : ℕ) := hij
          omega
        exact_mod_cast this
      nlinarith
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hcon with h | h
    · rw [h] at hlt; exact lt_irrefl _ hlt
    · exact absurd (hΦm (hxmem j) (hxmem i) h) (not_lt.2 hlt.le)
  have hzmem : ∀ j, z (x j) ∈ Icc (z u) (z v) := by
    intro j
    exact ⟨hz.monotoneOn (left_mem_Icc.2 huv) (hxmem j) (hxmem j).1,
      hz.monotoneOn (hxmem j) (right_mem_Icc.2 huv) (hxmem j).2⟩
  have hzxmono : StrictMono (fun j => z (x j)) := fun i j hij =>
    hz (hxmem i) (hxmem j) (hxmono hij)
  have halt : ∀ k : Fin n, P.eval (z (x k.castSucc)) * P.eval (z (x k.succ)) < 0 := by
    intro k
    have h1 := hsign (x k.castSucc) (hxmem _) _ (hxval k.castSucc)
    have h2 := hsign (x k.succ) (hxmem _) _ (hxval k.succ)
    have hsucc : (k₀ + (k.succ : ℕ) : ℤ) = (k₀ + (k.castSucc : ℕ) : ℤ) + 1 := by
      simp [Fin.val_succ, Fin.val_castSucc]; ring
    rw [hsucc] at h2
    have hprod := mul_pos h1 h2
    have hss := stripSign_mul_succ (k₀ + (k.castSucc : ℕ) : ℤ)
    nlinarith [hprod, hss]
  obtain ⟨Z, hZcard, hZroot, hZmem⟩ :=
    exists_interiorZeros_of_alternating P (S := Icc (z u) (z v)) ordConnected_Icc
      (fun j => z (x j)) hzxmono hzmem halt
  refine ⟨Z, ?_, hZroot, hZmem⟩
  have h1 : (k₀ : ℝ) ≤ Φ u / π + 1 := by
    have := Int.ceil_lt_add_one (Φ u / π); linarith
  have h2 : Φ v / π - 1 ≤ (k₁ : ℝ) := by
    have := Int.sub_one_lt_floor (Φ v / π); linarith
  have hncast : (n : ℝ) = (k₁ : ℝ) - (k₀ : ℝ) := by exact_mod_cast hnk
  have hcard : (n : ℝ) ≤ (Z.card : ℝ) := by exact_mod_cast hZcard
  have hdiv : (Φ v - Φ u) / π = Φ v / π - Φ u / π := by ring
  rw [hdiv]
  linarith


/-! ### Summing over the components of `eq:Omega-M` -/

/-- The components are disjoint, so their zeros are distinct and the counts add.  Paper
`prop:angular-discrepancy`: summing the phase count over the components of
`Ω_M ∩ (α, β)` costs `2` per component. -/
theorem exists_phaseZeros_sum
    (P : Polynomial ℝ) {ι : Type*} (s : Finset ι)
    {Φ z : ℝ → ℝ} {u v : ι → ℝ} {T : Set ℝ}
    (huv : ∀ i ∈ s, u i ≤ v i)
    (hΦc : ∀ i ∈ s, ContinuousOn Φ (Icc (u i) (v i)))
    (hΦm : ∀ i ∈ s, StrictMonoOn Φ (Icc (u i) (v i)))
    (hz : ∀ i ∈ s, StrictMonoOn z (Icc (u i) (v i)))
    (hsign : ∀ i ∈ s, ∀ θ ∈ Icc (u i) (v i), ∀ k : ℤ,
        Φ θ = (k : ℝ) * π → 0 < stripSign k * P.eval (z θ))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Disjoint (Icc (z (u i)) (z (v i))) (Icc (z (u j)) (z (v j))))
    (hT : ∀ i ∈ s, Icc (z (u i)) (z (v i)) ⊆ T) :
    ∃ Z : Finset ℂ,
      (∑ i ∈ s, (Φ (v i) - Φ (u i)) / π) - 2 * (s.card : ℝ) ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' T) := by
  classical
  have hex : ∀ i : ι, ∃ Z : Finset ℂ, (i ∈ s →
      ((Φ (v i) - Φ (u i)) / π - 2 : ℝ) ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' (Icc (z (u i)) (z (v i))))) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨Z, h1, h2, h3⟩ :=
        exists_phaseZeros P (huv i hi) (hΦc i hi) (hΦm i hi) (hz i hi) (hsign i hi)
      exact ⟨Z, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun hh => absurd hh hi⟩
  choose Z hZ using hex
  have hZdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Z i) (Z j) := by
    intro i hi j hj hij
    refine Finset.disjoint_left.2 fun z hzi hzj => ?_
    obtain ⟨a, ha, rfl⟩ := (hZ i hi).2.2 z hzi
    obtain ⟨b, hb, hab⟩ := (hZ j hj).2.2 _ hzj
    have : b = a := by exact_mod_cast hab
    subst this
    exact (Set.disjoint_left.1 (hdisj i hi j hj hij) ha) hb
  refine ⟨s.biUnion Z, ?_, ?_, ?_⟩
  · rw [Finset.card_biUnion hZdisj]
    have hsum : ∀ i ∈ s, ((Φ (v i) - Φ (u i)) / π - 2 : ℝ) ≤ ((Z i).card : ℝ) :=
      fun i hi => (hZ i hi).1
    have := Finset.sum_le_sum hsum
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at this
    push_cast at this ⊢
    linarith
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.1 hz
    exact (hZ i hi).2.1 z hzi
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨a, ha, rfl⟩ := (hZ i hi).2.2 z hzi
    exact ⟨a, hT i hi ha, rfl⟩


/-! ### The constant splits as `C₀ + C₁ K` -/

/-- Paper `prop:angular-discrepancy`, `eq:angular-distinct-lower`.  With `Φ_M` of
`eq:Phi-def`, the phase count over the components of `eq:Omega-M` has a defect that splits as
`C₀ + C₁ K`, and neither part sees the numerator past `K = deg B`:

* `C₀ = 4h/π + 1/π + κ₀/π + 2` collects the two endpoint windows of `eq:retained-range`, the
  amplitude windows through `eq:amplitude-window-negligible`, the denominator factor's phase
  variation `κ₀`, and the `2` that one component costs;
* `C₁ = κ₁/π + 2` collects Radon's constant `κ₁ = 𝒦_γ + π` from `eq:linear-phase-variation`
  and the further `2` that each of the `J ≤ K` amplitude windows costs.

`h` is the constant of `eq:retained-range`, and `κ₀`, `κ₁` are the constants of
`cor:linear-phase-variation` — all three functions of `Q` and `r` alone.  The threshold in `M`
hidden in `hΦm` may depend on the numerator; the constants may not, and do not. -/
theorem angular_distinct_lower
    (P : Polynomial ℝ) {ι : Type*} (s : Finset ι)
    {ψ z : ℝ → ℝ} {u v : ι → ℝ} {T : Set ℝ} {M K r : ℕ} {hwin w κ₀ κ₁ : ℝ}
    (hM : 1 ≤ M) (hr : 1 ≤ r) (hh : 0 ≤ hwin)
    (huv : ∀ i ∈ s, u i ≤ v i)
    (hΦc : ∀ i ∈ s, ContinuousOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Icc (u i) (v i)))
    (hΦm : ∀ i ∈ s, StrictMonoOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Icc (u i) (v i)))
    (hz : ∀ i ∈ s, StrictMonoOn z (Icc (u i) (v i)))
    (hsign : ∀ i ∈ s, ∀ θ ∈ Icc (u i) (v i), ∀ k : ℤ,
        ((M : ℝ) + 1) * θ - ψ θ = (k : ℝ) * π → 0 < stripSign k * P.eval (z θ))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Disjoint (Icc (z (u i)) (z (v i))) (Icc (z (u j)) (z (v j))))
    (hT : ∀ i ∈ s, Icc (z (u i)) (z (v i)) ⊆ T)
    (hcard : s.card ≤ K + 1)
    (hlen : π / r - 2 * hwin / M - w ≤ ∑ i ∈ s, (v i - u i))
    (hw : ((M : ℝ) + 1) * w ≤ 1)
    (hvar : ∑ i ∈ s, (ψ (v i) - ψ (u i)) ≤ κ₀ + κ₁ * K) :
    ∃ Z : Finset ℂ,
      ((M : ℝ) + 1) / r - (4 * hwin / π + 1 / π + κ₀ / π + 2)
          - (κ₁ / π + 2) * K ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' T) := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hr0 : ((r : ℝ)) ≠ 0 := by
    have : (1:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hdivmono : ∀ a b : ℝ, a ≤ b → a / π ≤ b / π := by
    intro a b hab; gcongr
  obtain ⟨Z, hZ, hZr, hZm⟩ :=
    exists_phaseZeros_sum P s huv hΦc hΦm hz hsign hdisj hT
  refine ⟨Z, ?_, hZr, hZm⟩
  refine le_trans ?_ hZ
  -- the summed phase increase, in terms of the retained length and the phase variation
  have hMpos : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hsplit : ∑ i ∈ s, ((((M : ℝ) + 1) * v i - ψ (v i)) - (((M : ℝ) + 1) * u i - ψ (u i))) / π
      = (((M : ℝ) + 1) * (∑ i ∈ s, (v i - u i)) - ∑ i ∈ s, (ψ (v i) - ψ (u i))) / π := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hΦsum : ∑ i ∈ s, ((fun θ => ((M : ℝ) + 1) * θ - ψ θ) (v i)
      - (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (u i)) / π
      = (((M : ℝ) + 1) * (∑ i ∈ s, (v i - u i)) - ∑ i ∈ s, (ψ (v i) - ψ (u i))) / π := hsplit
  rw [hΦsum]
  -- the two length losses
  have hlow : ((M : ℝ) + 1) / r - 4 * hwin / π - 1 / π
      ≤ ((M : ℝ) + 1) * (∑ i ∈ s, (v i - u i)) / π := by
    have hstep : ((M : ℝ) + 1) * (π / r - 2 * hwin / M - w)
        ≤ ((M : ℝ) + 1) * (∑ i ∈ s, (v i - u i)) := by
      have : (0:ℝ) ≤ (M : ℝ) + 1 := by positivity
      exact mul_le_mul_of_nonneg_left hlen this
    have hMM : ((M : ℝ) + 1) / M ≤ 2 := by
      rw [div_le_iff₀ hMpos]
      have : (1:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have hexp : ((M : ℝ) + 1) * (π / r - 2 * hwin / M - w)
        = ((M : ℝ) + 1) * π / r - 2 * hwin * (((M : ℝ) + 1) / M) - ((M : ℝ) + 1) * w := by
      field_simp
    have hbound : ((M : ℝ) + 1) * π / r - 4 * hwin - 1
        ≤ ((M : ℝ) + 1) * (∑ i ∈ s, (v i - u i)) := by
      refine le_trans ?_ hstep
      rw [hexp]
      have h1 : 2 * hwin * (((M : ℝ) + 1) / M) ≤ 4 * hwin := by nlinarith
      linarith
    calc ((M : ℝ) + 1) / r - 4 * hwin / π - 1 / π
        = (((M : ℝ) + 1) * π / r - 4 * hwin - 1) / π := by field_simp
      _ ≤ _ := hdivmono _ _ hbound
  have hvar' : -(κ₀ / π) - (κ₁ / π) * (K : ℝ) ≤ (- ∑ i ∈ s, (ψ (v i) - ψ (u i))) / π := by
    have hstep := hdivmono (-(κ₀ + κ₁ * (K : ℝ))) (- ∑ i ∈ s, (ψ (v i) - ψ (u i)))
      (by linarith)
    have he : (-(κ₀ + κ₁ * (K : ℝ))) / π = -(κ₀ / π) - (κ₁ / π) * (K : ℝ) := by
      field
    rwa [he] at hstep
  have hcard' : ((s.card : ℝ)) ≤ (K : ℝ) + 1 := by exact_mod_cast hcard
  have hkey : (((M : ℝ) + 1) * (∑ i ∈ s, (v i - u i)) - ∑ i ∈ s, (ψ (v i) - ψ (u i))) / π
      = ((M : ℝ) + 1) * (∑ i ∈ s, (v i - u i)) / π
        + (- ∑ i ∈ s, (ψ (v i) - ψ (u i))) / π := by ring
  rw [hkey]
  have hK : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  nlinarith [hlow, hvar', hcard', hπ, hK]



/-! ### `thm:main` clause 3 -/

/-- The phase supply of `thm:weighted-dominance` at one index, spelled out rather than bundled:
a finite family of components of `eq:Omega-M`, on each of which `Φ_M` of `eq:Phi-def` is
strictly increasing and the coefficient carries at every phase point the sign
`eq:principal-decomposition` predicts, together with the three quantitative facts
`prop:angular-discrepancy` runs on — at most `K + 1` components (`eq:amplitude-zero-count`),
the retained length of `eq:retained-range`, and `eq:linear-phase-variation`. -/
def PhaseSupply (P : Polynomial ℝ) (ψ z : ℝ → ℝ) (M K r : ℕ) (hwin w κ₀ κ₁ : ℝ)
    (T : Set ℝ) : Prop :=
  ∃ (s : Finset ℕ) (u v : ℕ → ℝ),
    (∀ i ∈ s, u i ≤ v i) ∧
    (∀ i ∈ s, ContinuousOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Icc (u i) (v i))) ∧
    (∀ i ∈ s, StrictMonoOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Icc (u i) (v i))) ∧
    (∀ i ∈ s, StrictMonoOn z (Icc (u i) (v i))) ∧
    (∀ i ∈ s, ∀ θ ∈ Icc (u i) (v i), ∀ k : ℤ,
        ((M : ℝ) + 1) * θ - ψ θ = (k : ℝ) * π → 0 < stripSign k * P.eval (z θ)) ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Disjoint (Icc (z (u i)) (z (v i))) (Icc (z (u j)) (z (v j)))) ∧
    (∀ i ∈ s, Icc (z (u i)) (z (v i)) ⊆ T) ∧
    s.card ≤ K + 1 ∧
    (π / r - 2 * hwin / M - w ≤ ∑ i ∈ s, (v i - u i)) ∧
    (((M : ℝ) + 1) * w ≤ 1) ∧
    (∑ i ∈ s, (ψ (v i) - ψ (u i)) ≤ κ₀ + κ₁ * K)

/-- The clause-3 constants: `C₀` sees only `Q` and `r` through `h`, `κ₀`; `C₁` only through
Radon's `κ₁ = 𝒦_γ + π`.  Neither sees the numerator. -/
noncomputable def defectC₀ (hwin κ₀ : ℝ) : ℝ := 4 * hwin / π + 1 / π + κ₀ / π + 2

/-- The clause-3 slope, `κ₁/π + 2`: Radon's constant plus the `2` each amplitude window
costs the phase count. -/
noncomputable def defectC₁ (κ₁ : ℝ) : ℝ := κ₁ / π + 2

/-- Paper `prop:angular-discrepancy`, `eq:angular-distinct-lower`, in the `ℕ`-valued form
`Main.main_bound_interval_ofRecurrence` consumes: the phase supply gives at least
`M/r - ⌈C₀ + C₁ K⌉₊` distinct zeros inside `T`. -/
theorem exists_interiorZeros_of_phaseSupply
    (P : Polynomial ℝ) {ψ z : ℝ → ℝ} {M K r : ℕ} {hwin w κ₀ κ₁ : ℝ} {T : Set ℝ}
    (hM : 1 ≤ M) (hr : 1 ≤ r) (hh : 0 ≤ hwin)
    (hsup : PhaseSupply P ψ z M K r hwin w κ₀ κ₁ T) :
    ∃ Z : Finset ℂ,
      M / r - ⌈defectC₀ hwin κ₀ + defectC₁ κ₁ * (K : ℝ)⌉₊ ≤ Z.card ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal '' T) := by
  classical
  obtain ⟨s, u, v, huv, hΦc, hΦm, hzm, hsign, hdisj, hT, hcard, hlen, hw, hvar⟩ := hsup
  obtain ⟨Z, hZ, hZr, hZm⟩ :=
    angular_distinct_lower P s hM hr hh huv hΦc hΦm hzm hsign hdisj hT hcard hlen hw hvar
  refine ⟨Z, ?_, hZr, hZm⟩
  -- the real bound becomes a `ℕ` bound
  set C : ℝ := defectC₀ hwin κ₀ + defectC₁ κ₁ * (K : ℝ) with hC
  have hZ' : ((M : ℝ) + 1) / r - C ≤ (Z.card : ℝ) := by
    simp only [hC, defectC₀, defectC₁]
    linarith [hZ]
  have hr0 : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hstep : ((M / r : ℕ) : ℝ) ≤ (Z.card : ℝ) + (⌈C⌉₊ : ℝ) := by
    have h1 : ((M / r : ℕ) : ℝ) ≤ (M : ℝ) / r := Nat.cast_div_le
    have h2 : (M : ℝ) / r ≤ ((M : ℝ) + 1) / r := by gcongr; linarith
    have h3 : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
    linarith
  have : M / r ≤ Z.card + ⌈C⌉₊ := by exact_mod_cast hstep
  omega

/-- **Paper `thm:main` clause 3.**  A defect constant of the shape `angular_distinct_lower`
produces is numerator-uniform: with `C₀` and `C₁` fixed before the numerator, the `ℕ`-valued
constant `⌈C₀ + C₁ deg B_N⌉₊` is bounded by `⌈C₀⌉₊ + ⌈C₁⌉₊ deg B_N`, which is the
`NumeratorUniform` shape `Main.main_bound_interval` consumes. -/
theorem numeratorUniform_ceil (Q : Polynomial ℝ) (r : ℕ) (C₀ C₁ : ℝ) :
    NumeratorUniform Q r
      (fun N => ⌈C₀ + C₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊) := by
  refine ⟨⌈C₀⌉₊, ⌈C₁⌉₊, fun N => ?_⟩
  calc ⌈C₀ + C₁ * (((laurentWeight Q r N).natDegree : ℕ) : ℝ)⌉₊
      ≤ ⌈C₀⌉₊ + ⌈C₁ * (((laurentWeight Q r N).natDegree : ℕ) : ℝ)⌉₊ := Nat.ceil_add_le _ _
    _ ≤ ⌈C₀⌉₊ + ⌈C₁⌉₊ * (laurentWeight Q r N).natDegree := by
        gcongr
        refine Nat.ceil_le.2 ?_
        push_cast
        exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₁) (by positivity)

/-- The two composed: the clause-3 defect family produced by the phase supply is
numerator-uniform, with `C₀ = 4h/π + 1/π + κ₀/π + 2` and `C₁ = 𝒦_γ/π + 1 + 2` fixed before
`N`, since `h`, `κ₀` and `κ₁` are constants of `Q` and `r` alone. -/
theorem numeratorUniform_defect (Q : Polynomial ℝ) (r : ℕ) (hwin κ₀ κ₁ : ℝ) :
    NumeratorUniform Q r
      (fun N => ⌈defectC₀ hwin κ₀
        + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊) :=
  numeratorUniform_ceil Q r _ _


/-! ### The two inputs, discharged from what is already proven -/

/-- Paper `eq:amplitude-zero-count`: the zeros of the principal amplitude on the arc number at
most `deg B`, so the components of `eq:Omega-M` number at most `deg B + 1`.  This is
`amplitude_zero_count` with each window counted at multiplicity at least one. -/
theorem card_amplitudeZeros_le {B : Polynomial ℂ} (hB : B ≠ 0) {γ : ℝ → ℂ} {S : Finset ℝ}
    (hinj : Set.InjOn γ (S : Set ℝ)) (hroot : ∀ θ ∈ S, B.IsRoot (γ θ)) :
    S.card ≤ B.natDegree := by
  refine le_trans ?_ (amplitude_zero_count hB hinj)
  calc S.card = ∑ _θ ∈ S, 1 := by simp
    _ ≤ ∑ θ ∈ S, B.rootMultiplicity (γ θ) :=
        Finset.sum_le_sum fun θ hθ => (Polynomial.rootMultiplicity_pos hB).2 (hroot θ hθ)

/-- The components of `eq:Omega-M` are the odd-to-even steps of one monotone chain
`w 0 ≤ w 1 ≤ ⋯`, so the increments of `ψ` across them are a sub-sum of a single partition sum
and are bounded by the total variation.  This is what lets `eq:linear-phase-variation` — which
bounds that variation — discharge the phase-variation input of `prop:angular-discrepancy`. -/
theorem sum_abs_sub_le_of_eVariationOn {ψ : ℝ → ℝ} {S : Set ℝ} {w : ℕ → ℝ} {n : ℕ} {V : ℝ}
    (hV : 0 ≤ V) (hvar : eVariationOn ψ S ≤ ENNReal.ofReal V)
    (hw : Monotone w) (hmem : ∀ i, w i ∈ S) :
    ∑ i ∈ Finset.range n, |ψ (w (2 * i + 1)) - ψ (w (2 * i))| ≤ V := by
  classical
  set F : ℕ → ENNReal := fun j => edist (ψ (w (j + 1))) (ψ (w j)) with hF
  have hsub : (Finset.range n).image (fun i => 2 * i) ⊆ Finset.range (2 * n) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_range.2 (by have := Finset.mem_range.1 hi; omega)
  have himg : ∑ i ∈ Finset.range n, F (2 * i)
      = ∑ j ∈ (Finset.range n).image (fun i => 2 * i), F j :=
    (Finset.sum_image (fun x _ y _ h => by omega)).symm
  have hle : ∑ i ∈ Finset.range n, F (2 * i) ≤ eVariationOn ψ S := by
    rw [himg]
    exact le_trans (Finset.sum_le_sum_of_subset hsub) (eVariationOn.sum_le hw hmem)
  have hcast : ∑ i ∈ Finset.range n, F (2 * i)
      = ENNReal.ofReal (∑ i ∈ Finset.range n, |ψ (w (2 * i + 1)) - ψ (w (2 * i))|) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hF]; simp only []; rw [edist_dist, Real.dist_eq]
  rw [hcast] at hle
  have := le_trans hle hvar
  exact (ENNReal.ofReal_le_ofReal_iff hV).1 this


/-- Paper `prop:angular-discrepancy`: the supply assembled from a single monotone chain
`w 0 ≤ w 1 ≤ ⋯`, whose odd-to-even steps `[w(2i), w(2i+1)]` are the components of
`eq:Omega-M` and whose even-to-odd steps are the deleted windows.  The phase-variation input
is now `eq:linear-phase-variation` itself — `eVariationOn ψ` bounded by `κ₀ + κ₁ K`, which
`linear_phase_variation_regular` proves — rather than a summed hypothesis. -/
theorem phaseSupply_of_chain
    (P : Polynomial ℝ) {ψ z : ℝ → ℝ} {w : ℕ → ℝ} {M K r n : ℕ} {hwin wid κ₀ κ₁ : ℝ}
    {A T : Set ℝ} (hAconn : A.OrdConnected) (hTconn : T.OrdConnected)
    (hw : Monotone w) (hmem : ∀ i, w i ∈ A)
    (hzmono : StrictMonoOn z A) (hzT : ∀ a ∈ A, z a ∈ T)
    (hsep : ∀ i, i + 1 < n → w (2 * i + 1) < w (2 * i + 2))
    (hΦc : ∀ i, i < n → ContinuousOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ)
        (Icc (w (2 * i)) (w (2 * i + 1))))
    (hΦm : ∀ i, i < n → StrictMonoOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ)
        (Icc (w (2 * i)) (w (2 * i + 1))))
    (hsign : ∀ i, i < n → ∀ θ ∈ Icc (w (2 * i)) (w (2 * i + 1)), ∀ k : ℤ,
        ((M : ℝ) + 1) * θ - ψ θ = (k : ℝ) * π → 0 < stripSign k * P.eval (z θ))
    (hcard : n ≤ K + 1)
    (hlen : π / r - 2 * hwin / M - wid
        ≤ ∑ i ∈ Finset.range n, (w (2 * i + 1) - w (2 * i)))
    (hwid : ((M : ℝ) + 1) * wid ≤ 1)
    (hκ : 0 ≤ κ₀ + κ₁ * K)
    (hvar : eVariationOn ψ A ≤ ENNReal.ofReal (κ₀ + κ₁ * K)) :
    PhaseSupply P ψ z M K r hwin wid κ₀ κ₁ T := by
  classical
  have hsubA : ∀ i j : ℕ, i ≤ j → Icc (w i) (w j) ⊆ A := fun i j _ =>
    hAconn.out (hmem i) (hmem j)
  refine ⟨Finset.range n, fun i => w (2 * i), fun i => w (2 * i + 1),
    fun i _ => hw (by omega), fun i hi => hΦc i (Finset.mem_range.1 hi),
    fun i hi => hΦm i (Finset.mem_range.1 hi),
    fun i _ => hzmono.mono (hsubA _ _ (by omega)),
    fun i hi => hsign i (Finset.mem_range.1 hi), ?_, ?_, ?_, ?_, hwid, ?_⟩
  · -- the components are separated by the deleted windows, hence disjoint
    have key : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i < j →
        Disjoint (Icc (z (w (2 * i))) (z (w (2 * i + 1))))
          (Icc (z (w (2 * j))) (z (w (2 * j + 1)))) := by
      intro i hi j hj hij
      have hjn : j < n := Finset.mem_range.1 hj
      have h1 : w (2 * i + 1) < w (2 * i + 2) := hsep i (by omega)
      have h2 : w (2 * i + 2) ≤ w (2 * j) := hw (by omega)
      have hz1 : z (w (2 * i + 1)) < z (w (2 * i + 2)) :=
        hzmono (hmem _) (hmem _) h1
      have hz2 : z (w (2 * i + 2)) ≤ z (w (2 * j)) :=
        hzmono.monotoneOn (hmem _) (hmem _) h2
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      have hx2 : x ≤ z (w (2 * i + 1)) := hx.2
      have hx3 : z (w (2 * j)) ≤ x := hx'.1
      linarith
    intro i hi j hj hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i hi j hj h
    · exact (key j hj i hi h).symm
  · exact fun i _ => hTconn.out (hzT _ (hmem _)) (hzT _ (hmem _))
  · simpa using hcard
  · exact hlen
  · -- the phase variation, from `eq:linear-phase-variation`
    have habs := sum_abs_sub_le_of_eVariationOn (n := n) hκ hvar hw hmem
    refine le_trans (Finset.sum_le_sum fun i _ => le_abs_self _) habs


/-! ### The clause itself -/

/-- **Paper `thm:main` clause 3.**  Fix `(Q, r)` and the three constants of the analysis — `h`
from `eq:retained-range`, `κ₀` and `κ₁` from `cor:linear-phase-variation` — each a function of
`Q` and `r` alone.  If for every numerator `N` the phase supply of `thm:weighted-dominance`
holds at every large index with `K = deg B_N`, then one `Cbulk` family bounds the defect at
every large index and is numerator-uniform.

The supply is an explicit hypothesis, not a bundle: `PhaseSupply` is an `∃` over the objects
the manuscript names, and it is the same supply clause 2 already runs on.  What clause 3 adds,
and what is proven here, is that the constant it produces splits as
`C₀ + C₁ deg B_N` with `C₀ = defectC₀ h κ₀` and `C₁ = defectC₁ κ₁` **bound outside the
quantifier over numerators** — that binding is the whole content of the clause, and it is
visible in the statement rather than asserted in prose. -/
theorem clauseThree
    (Q : Polynomial ℝ) (r : ℕ) (hr : 1 ≤ r) {hwin κ₀ κ₁ : ℝ} (hh : 0 ≤ hwin)
    {F : Polynomial (Polynomial ℝ) → ℕ → Polynomial ℝ}
    {ψ : Polynomial (Polynomial ℝ) → ℕ → ℝ → ℝ} {z : ℝ → ℝ}
    {wid : Polynomial (Polynomial ℝ) → ℕ → ℝ} {T : Set ℝ}
    (supply : ∀ N, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M →
        PhaseSupply (F N M) (ψ N M) z M (laurentWeight Q r N).natDegree r
          hwin (wid N M) κ₀ κ₁ T) :
    NumeratorUniform Q r
        (fun N => ⌈defectC₀ hwin κ₀
          + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊)
      ∧ ∀ N, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → 1 ≤ M → ∃ Z : Finset ℂ,
          M / r - ⌈defectC₀ hwin κ₀
            + defectC₁ κ₁ * ((laurentWeight Q r N).natDegree : ℝ)⌉₊ ≤ Z.card ∧
          (∀ w ∈ Z, ((F N M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ Complex.ofReal '' T) := by
  refine ⟨numeratorUniform_defect Q r hwin κ₀ κ₁, fun N => ?_⟩
  obtain ⟨M₀, hM₀⟩ := supply N
  exact ⟨M₀, fun M hM hM1 =>
    exists_interiorZeros_of_phaseSupply (F N M) hM1 hr hh (hM₀ M hM hM1)⟩

end ForgacsTran
