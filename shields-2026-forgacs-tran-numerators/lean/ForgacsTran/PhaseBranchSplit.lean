/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.ViewingAngle
import ForgacsTran.AttractorPole

/-!
# `eq:W-on-g` at the level of derivatives

`cor:linear-phase-variation` bounds the variation of the branch written as the fixed
factor's angle plus one `ViewingAngle.polarAngle` per zero of `B`.
`AngularDiscrepancyFT.FTPhaseSupply`'s other clauses are about a branch built on `W`
itself.  The two are branches of one argument, so they differ by a constant -- but each
side type-checks alone and nothing in a build compares them, and constancy is not a fact
either side states.

What identifies them is the **derivative**.  Both have derivative `Im(W'/W)`, and this
module is the identity that says so: writing `W = V·∏(γ - β)` over the zeros of `B`, the
logarithmic derivative splits as `V'/V + ∑ γ'/(γ - β)`, and the summed branch's derivative
is the imaginary part of exactly that sum term by term.
`PhaseVariationBlocks.sub_eq_sub_of_hasDerivAt_eq` turns one derivative into one increment.

The route is through logarithmic derivatives rather than through a second polar
decomposition on purpose: a factorization `W = ‖W‖e^{iΨ}` for the summed branch would
have to be built, while the derivative identity is the product rule.

## Main statements

* `hasDerivAt_multisetProd_sub` -- the product rule over the zeros of `B` as a multiset,
  in logarithmic form.
* `im_logDeriv_factorization` -- `Im(W'/W) = Im(V'/V) + ∑ Im(γ'/(γ - β))`.
* `hasDerivAt_sum_polarAngle` -- the summed branch's derivative, term by term, with each
  branch based wherever its block puts it.
* `hasDerivAt_sum_polarAngle_of_factorization` -- the two composed, which is
  `PhaseVariationBlocks.exists_varPhase_of_blocks_of_derivEq`'s `hsum` **in the state where
  the arc misses every zero of `B`**; see the Implementation notes.
* `ftAmp_eq_fixed_mul_prod`, `ne_root_of_ftAmp_ne_zero` -- the factorization and the
  avoidance above, at the paper's own amplitude, so neither is assumed.

## Implementation notes

The multiset carries multiplicity, so a zero of `B` of order `ν` contributes `ν` branches
and `ν` copies of its viewing angle.  That is what `eq:amplitude-zero-count` counts and
what makes the constant of `eq:linear-phase-variation` multiply `deg B` rather than the
number of distinct zeros.

`hne` is per element of the multiset and on the whole block: an argument branch does not
exist through a zero of `W`, which is why the supply's blocks avoid the amplitude divisor
and why this identity is stated on a block rather than on the arc.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
and the principal amplitude» (`sec:geometry`, `eq:W-def`, `cor:linear-phase-variation`,
`eq:linear-phase-variation`).

## Tags

phase branch, logarithmic derivative, viewing angle, weight polynomial
-/

namespace ForgacsTran

open Set

/-- `Im` commutes with a multiset sum.  Needed as a standalone step: inside
`im_logDeriv_factorization` the multiset is already mentioned by several hypotheses, so it
cannot be inducted on there. -/
private theorem multiset_sum_im (m : Multiset ℂ) :
    m.sum.im = (m.map Complex.im).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [ih]

/-- **The product rule over the zeros of `B`, in logarithmic form.**  The multiset carries
multiplicity, so a zero of order `ν` contributes `ν` terms to the sum. -/
theorem hasDerivAt_multisetProd_sub {γ : ℝ → ℂ} {dγ : ℂ} {θ : ℝ} (m : Multiset ℂ)
    (hγ : HasDerivAt γ dγ θ) (hne : ∀ β ∈ m, γ θ - β ≠ 0) :
    HasDerivAt (fun y => (m.map (fun β => γ y - β)).prod)
      ((m.map (fun β => dγ / (γ θ - β))).sum * (m.map (fun β => γ θ - β)).prod) θ := by
  classical
  induction m using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const θ (1 : ℂ)
  | cons a m ih =>
      have hane : γ θ - a ≠ 0 := hne a (Multiset.mem_cons_self a m)
      have hm : ∀ β ∈ m, γ θ - β ≠ 0 := fun β hβ => hne β (Multiset.mem_cons_of_mem hβ)
      have hfun : (fun y => ((a ::ₘ m).map (fun β => γ y - β)).prod)
          = fun y => (γ y - a) * (m.map (fun β => γ y - β)).prod := by
        funext y
        simp only [Multiset.map_cons, Multiset.prod_cons]
      have hd : ((a ::ₘ m).map (fun β => dγ / (γ θ - β))).sum
            * ((a ::ₘ m).map (fun β => γ θ - β)).prod
          = dγ * (m.map (fun β => γ θ - β)).prod
            + (γ θ - a) * ((m.map (fun β => dγ / (γ θ - β))).sum
                * (m.map (fun β => γ θ - β)).prod) := by
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
        field_simp
      rw [hfun, hd]
      exact (hγ.sub_const a).mul (ih hm)

/-- **`Im(W'/W)` splits along `eq:W-on-g`.**  `V` is the fixed factor and the multiset is
the zeros of `B` with multiplicity. -/
theorem im_logDeriv_factorization {V γ W : ℝ → ℂ} {dV dγ dW : ℂ} {U : Set ℝ} {θ : ℝ}
    (m : Multiset ℂ) (hU : IsOpen U) (hθ : θ ∈ U)
    (hV : HasDerivAt V dV θ) (hγ : HasDerivAt γ dγ θ) (hW : HasDerivAt W dW θ)
    (hV0 : V θ ≠ 0) (hne : ∀ β ∈ m, γ θ - β ≠ 0)
    (hfac : ∀ s ∈ U, W s = V s * (m.map (fun β => γ s - β)).prod) :
    (dW / W θ).im = (dV / V θ).im + (m.map (fun β => (dγ / (γ θ - β)).im)).sum := by
  classical
  set P : ℝ → ℂ := fun y => (m.map (fun β => γ y - β)).prod with hP
  set S : ℂ := (m.map (fun β => dγ / (γ θ - β))).sum with hS
  have hP0 : P θ ≠ 0 := by
    rw [hP]
    exact Multiset.prod_ne_zero (by
      intro hmem
      obtain ⟨β, hβ, hzero⟩ := Multiset.mem_map.1 hmem
      exact hne β hβ hzero)
  have hPd : HasDerivAt P (S * P θ) θ := hasDerivAt_multisetProd_sub m hγ hne
  have hWd : HasDerivAt W (dV * P θ + V θ * (S * P θ)) θ := by
    have hprod := hV.mul hPd
    refine hprod.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hθ] with s hs
    exact hfac s hs
  have heq : dW = dV * P θ + V θ * (S * P θ) := hW.unique hWd
  have hWθ : W θ = V θ * P θ := hfac θ hθ
  have hsplit : dW / W θ = dV / V θ + S := by
    rw [heq, hWθ]
    field_simp
  rw [hsplit, Complex.add_im, hS, multiset_sum_im, Multiset.map_map]
  rfl

/-- **The summed branch's derivative.**  One `polarAngle` per zero of `B`, plus the fixed
factor's own branch at `β = 0`; each term's derivative is
`ViewingAngle.hasDerivAt_polarAngle`. -/
theorem hasDerivAt_sum_polarAngle {V γ dV dγ : ℝ → ℂ} {U : Set ℝ} {a b θ c₀ : ℝ}
    {cr : ℂ → ℝ} (m : Multiset ℂ) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hVd : ∀ s ∈ U, HasDerivAt V (dV s) s) (hVc : ContinuousOn dV U)
    (hγd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hγc : ContinuousOn dγ U)
    (hV0 : ∀ s ∈ Icc a b, V s ≠ 0)
    (hne : ∀ β ∈ m, ∀ s ∈ Icc a b, γ s ≠ β)
    (hc₀ : c₀ ∈ Icc a b) (hcr : ∀ β ∈ m, cr β ∈ Icc a b) (hθ : θ ∈ Icc a b) :
    HasDerivAt (fun y => polarAngle V dV 0 c₀ y
        + (m.map (fun β => polarAngle γ dγ β (cr β) y)).sum)
      ((dV θ / V θ).im + (m.map (fun β => (dγ θ / (γ θ - β)).im)).sum) θ := by
  classical
  have hV := hasDerivAt_polarAngle_base (β := (0 : ℂ)) hU hsub hVd hVc
    (by simpa using hV0) hc₀ hθ
  simp only [sub_zero] at hV
  refine hV.add ?_
  induction m using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const θ (0 : ℝ)
  | cons c m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (hasDerivAt_polarAngle_base hU hsub hγd hγc
        (fun s hs => hne c (Multiset.mem_cons_self c m) s hs)
        (hcr c (Multiset.mem_cons_self c m)) hθ).add
        (ih (fun β hβ => hne β (Multiset.mem_cons_of_mem hβ))
          (fun β hβ => hcr β (Multiset.mem_cons_of_mem hβ)))

/-- **The two composed.**  The summed branch has derivative `Im(W'/W)`, which is what
identifies it with the branch built on `W` itself.

**One interval, and that is the scope of this form.**  `[a,b]` has to carry every base
point `cr β`, the parameter `θ`, and no zero of `B` at all, which is
`PhaseVariationBlocks.sum_eVariationOn_branch_le`'s **first** state -- the arc missing
every zero.  In its second state the arc meets `β` at `m`, the base point travels with the
side, and an interval joining a block right of `m` to the base point on the left would have
to cross `m`.  There the sum is differentiated term by term over
`im_logDeriv_factorization` instead, one interval per zero and per block; see
`BranchSupply.hasDerivAt_of_rootBranchState`. -/
theorem hasDerivAt_sum_polarAngle_of_factorization {V γ dV dγ W dW : ℝ → ℂ} {U : Set ℝ}
    {a b θ c₀ : ℝ} {cr : ℂ → ℝ} (m : Multiset ℂ) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hVd : ∀ s ∈ U, HasDerivAt V (dV s) s) (hVc : ContinuousOn dV U)
    (hγd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hγc : ContinuousOn dγ U)
    (hWd : ∀ s ∈ U, HasDerivAt W (dW s) s)
    (hV0 : ∀ s ∈ Icc a b, V s ≠ 0)
    (hne : ∀ β ∈ m, ∀ s ∈ Icc a b, γ s ≠ β)
    (hfac : ∀ s ∈ U, W s = V s * (m.map (fun β => γ s - β)).prod)
    (hc₀ : c₀ ∈ Icc a b) (hcr : ∀ β ∈ m, cr β ∈ Icc a b) (hθ : θ ∈ Icc a b) :
    HasDerivAt (fun y => polarAngle V dV 0 c₀ y
        + (m.map (fun β => polarAngle γ dγ β (cr β) y)).sum) ((dW θ / W θ).im) θ := by
  have hθU : θ ∈ U := hsub hθ
  have hsplit := im_logDeriv_factorization (V := V) (γ := γ) (W := W) m hU hθU
    (hVd θ hθU) (hγd θ hθU) (hWd θ hθU) (hV0 θ hθ)
    (fun β hβ => sub_ne_zero.2 (hne β hβ θ hθ)) hfac
  rw [hsplit]
  exact hasDerivAt_sum_polarAngle m hU hsub hVd hVc hγd hγc hV0 hne hc₀ hcr hθ

/-! ### At the paper's own amplitude -/

/-- **`eq:W-on-g`'s factorization at `eq:W-def`.**  `𝒜 = -B(t)/S(t)` and `B` splits over
`ℂ`, so the fixed factor is `-lc(B)/S(t)` and the multiset is the zeros of `B` with
multiplicity.

Unconditional, `B = 0` included: there the empty product is `1`, the leading coefficient
is `0`, and both sides are `0`. -/
theorem ftAmp_eq_fixed_mul_prod (Q B : Polynomial ℂ) (r : ℕ) (z t : ℂ) :
    ftAmp Q B r z t
      = -(B.leadingCoeff / (ftCofactor Q r z t).eval t)
        * (B.roots.map (fun β => t - β)).prod := by
  have hcard : Multiset.card B.roots = B.natDegree :=
    ((_root_.IsAlgClosed.splits B).natDegree_eq_card_roots).symm
  have hev : B.eval t = B.leadingCoeff * (B.roots.map (fun β => t - β)).prod := by
    conv_lhs => rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    simp [Polynomial.eval_multiset_prod, Multiset.map_map]
  rw [ftAmp, hev]
  ring

/-- **The arc avoids every zero of `B` where the amplitude does not vanish.**  This is
`hasDerivAt_sum_polarAngle`'s `hne` on the supply's retained blocks, where the amplitude
is nonzero by construction -- an argument branch does not exist through a zero of `W`. -/
theorem ne_root_of_ftAmp_ne_zero {Q B : Polynomial ℂ} {r : ℕ} {z t : ℂ}
    (hW : ftAmp Q B r z t ≠ 0) {β : ℂ} (hβ : β ∈ B.roots) : t ≠ β := by
  rintro rfl
  exact hW (by rw [ftAmp, (Polynomial.isRoot_of_mem_roots hβ : B.eval t = 0)]; simp)

end ForgacsTran
