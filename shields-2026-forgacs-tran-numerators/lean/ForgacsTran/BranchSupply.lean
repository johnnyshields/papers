/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.BoundedVariation.DerivBound
import ForgacsTran.ArcPhaseBound
import ForgacsTran.ComplexPart
import ForgacsTran.PhaseBranchSplit
import ForgacsTran.PhaseVariationBlocks
import ForgacsTran.DominanceFT
import ForgacsTran.Amplitude

/-!
# The branch clause of `FTPhaseSupply`, composed

`PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` leaves two hypotheses.  This
module produces the second, `hbranch`, from the pieces the tree already carries.

Its inner existential has six clauses and two theorems produce them.  The factorization,
the differentiability and `eq:phase-derivative-bound` come from
`ArcPhaseBound.exists_phase_family_of_regions_of_open`, whose branch is built on the
amplitude itself; the three variation clauses come from
`PhaseVariationBlocks.exists_varPhase_of_blocks_of_derivEq`, whose branch is the fixed
factor's angle plus one viewing angle per zero of `B` — the only form in which
`eq:linear-phase-variation`'s constants do not see `B`.

**What joins the two halves is `im_logDeriv_eq_of_polar_branch`.**  The first half's
`dψ` is bound by an existential and its statement does not say what it is, so the two
branches cannot be matched by inspection; what identifies them is that a differentiable
branch of `arg W` has derivative `Im(W'/W)`, whatever branch it is.  The proof is the
mean value theorem on `W e^{-iψ}`, which is real-valued on the block: its imaginary part
is constant there, and `uniqueDiffOn_Icc` reads that off at the block's endpoints as
well as inside it.

## Main statements

* `im_logDeriv_eq_of_polar_branch` — a differentiable branch of the argument has
  derivative `Im(W'/W)`; the link between the two halves.
* `ftFixedFactor`, `ftAmp_eq_ftFixedFactor_mul` — `eq:W-on-g` at the paper's own
  amplitude, in the shape `PhaseBranchSplit.im_logDeriv_factorization` consumes.
* `ftCofactorAlong`, `ftFixedAngle`, `hasDerivAt_ftFixedAngle` — the fixed factor's
  angle written on `∂_t D` alone, so that `κ₀` carries no weight.
* `exists_varPhase_of_nondegenerate_blocks` — the variation clauses with the block
  containment asked only of the blocks that are not a point.
* `RootBranchState` — the two states a zero of `B` is in relative to the arc, as
  `PhaseVariationBlocks.sum_eVariationOn_branch_le` states them.
* `hasDerivAt_of_rootBranchState` — the block branches of a root state are
  differentiable, with the derivative the split needs.
* `exists_branchData_of_rootStates` — the states turned into the per-root data below.
* `interior_of_endpoint_vanishing` — a block on which the amplitude does not vanish
  cannot reach an endpoint at which it does.
* `exists_phase_family_of_regions_of_interior` —
  `ArcPhaseBound.exists_phase_family_of_regions_of_open` with the two endpoint values
  replaced by the block interiority they were a means to, which is what the amplitude
  supplies at `2 ≤ r` and the endpoint values do not.
* `exists_ftBranchSupply` — `hbranch`, at `κ₁ = 𝒦_γ + π`.
* `exists_ftBranchSupply_of_rootStates` — the same driven by the root states directly.
* `exists_uniform_ftBranchSupply` — the same with `κ₀` and `κ₁` bound ahead of `∀ B`.
* `eVariationOn_le_of_abs_deriv_le`, `eVariationOn_ftFixedAngle_le` — `h0` reduced to a
  derivative bound on the open arc.
* `exists_lipschitz_of_continuousOn_deriv2` — the collar's `hlip` reduced to `γ''`
  continuous up to the endpoint, with the endpoint derivative asked for one-sidedly.
* `ftCriticalAlong`, `ftCofactorAlong_eq_ftCritical_div`, `ftCofactorAlong_ne_zero_on` —
  `∂_t D = E(γ)/γ` along the arc, and `hS0` off it.
* `im_logDeriv_ftPrincipal` — the arc's own logarithmic derivative has imaginary part
  exactly one.
* `abs_im_logDeriv_ftCofactorAlong_le` — that derivative bound reduced to one on `E` along
  the arc.
* `ftCofactorEval_eq_endpoint_factorization`, `exists_bound_im_logDeriv_ftCofactor_endpoint`,
  `exists_bound_im_logDeriv_ftCofactorAlong_lower`,
  `exists_bound_im_logDeriv_ftCofactorAlong_upper` — the collar at a collision, one-sided,
  at any multiplicity, at either end of the arc.
* `abs_im_logDeriv_comp_const_sub` — reflecting the arc negates the logarithmic derivative
  and nothing else, which is how the far end is reached.
* `abs_im_logDeriv_ftCofactorAlong_le_of_bounds` — the bound where `E(γ)` does not
  degenerate, which covers the middle and the endpoint at which the branch runs into the
  origin.
* `exists_bound_im_logDeriv_ftCofactorAlong_mid`,
  `exists_bound_im_logDeriv_ftCofactorAlong_of_cover`, `exists_kappaZero_of_cover` — the
  three regions assembled into `κ₀`.
* `ftCritical_eq_pow_mul_ftCriticalReduced` — the canonical `hEfac`/`hH0` pair.
* `kappaZero_bundle_witness` — the weight-free bundle is satisfiable.

## Implementation notes

**The base points travel with the block, and no one interval serves them all.**
`PhaseBranchSplit.hasDerivAt_sum_polarAngle_of_factorization` asks for a single `[a,b]`
carrying every base point, every block and no zero of `B`.  That is the state in which
the arc misses every zero.  Where the arc meets one, at `m`, the blocks left of `m` are
based at `0` and those right of it at `π/r`, and an interval joining a right-hand block
to the base point `0` would have to cross `m`.  So the sum is differentiated term by
term instead — `hasDerivAt_of_rootBranchState` supplies one interval per zero and per
block — over `im_logDeriv_factorization`, which is the identity that theorem was built
on and is used here unchanged.

**`κ₀` is carried on the cofactor, not on the fixed factor, and that is what makes it
weight-free.**  `B` enters `V = -lc(B)/∂_t D` only as the nonzero constant `-lc(B)`, so
`V'/V = -(∂_t D)'/(∂_t D)` identically and the weight is invisible to the angle.
Writing the branch as `ftFixedAngle`, on `ftCofactorAlong`, puts that in the statement:
`h0` mentions `Q`, `r`, `z`, `τ` and nothing else, so `κ₀` can be — and in
`exists_uniform_ftBranchSupply` is — bound ahead of `∀ B`.  Stated on `V` instead it
type-checks equally well and silently permits a weight-dependent `κ₀`, which is exactly
what `thm:main` clause 3 forbids.  The **modulus** does not have this property:
`|V|` scales with `|lc(B)|`, so a `κ₀` taken through `‖V‖` would not be weight-free.

**What `κ₀` costs, in the end, is one bound on `E` and the constant one.**
`eq:Dprime-identity` gives `∂_t D = E(γ)/γ` on the arc, and the two factors behave
completely differently.  The `1/γ` looks like the dangerous one — `γ` runs into the origin
at one end — and is in fact free: `γ = τ e^{iθ}` with `τ` real, so `γ'/γ = τ'/τ + i` and
its imaginary part is **exactly one**, at every parameter and with no collar.  That
exactness is what makes the origin endpoint costless: a bound through `1/‖γ‖` would
diverge there.  What is left is `E = XQ' - rQ` along the arc, which carries neither the
weight nor the spectral parameter.

**The two ends of the arc are not alike, and one collar does not serve both.**  Where the
arc starts, `E(γ)` vanishes — a collision — and the divided difference splits the `ν`-fold
zero into a real power, nothing by `im_logDeriv_ofRealSub_zpow`, a cofactor
`EndpointCofactorBound` bounds, and a polynomial that does not vanish; no simplicity of
the collision is assumed, since the order is `rootMultiplicity` and the reduced factor is
nonzero by construction.  Where the branch runs into the **origin**, `E(γ) → E(0)` is
nonzero and there is no collision at all: continuity suffices, and it is the `1/γ` that
would have been fatal had its contribution not been exactly one.  The collars are
therefore stated separately, and both are **one-sided** — `θ` is an angular distance, so
a two-sided derivative at an endpoint asks for the negation of the phenomenon.

**The branch geometry is asked for only on the open arc too, and that is not a weakening
of the hypotheses but a change of where they are taken.**  `ViewingAngle`'s branch lift is
an integral, so `hasDerivAt_polarAngle_base` needs a genuinely two-sided derivative on an
**open** set containing the interval it works over — and the arc's own endpoints are where
`ftTauLower` extends the radius by a constant, so that derivative does not exist there and
no endpoint value repairs it.  The endpoints entered only because the branches were pinned
at them.  They need not be: `sum_eVariationOn_branch_le` and `hasDerivAt_of_rootBranchState`
are parametric in the interval, every **evaluation** point is interior (a block on which the
amplitude does not vanish cannot reach an endpoint at which it does), and so the family's
own hull `[a', b'] ⊆ Ioo 0 (π/r)` serves.  `hstates` is therefore asked over an arbitrary
closed sub-interval of the open arc rather than over the closed arc, `hKvar` over the open
arc at an arbitrary base point, and `hγd`, `hd2`, `hc2`, `hreg` on the open arc alone.  A
base point moves a branch by a constant, which the variation does not see, so nothing in
the conclusion changes.

**Everything about the fixed factor is asked for only on the open arc.**  `W` vanishes
at both endpoints, which is `exists_phase_family_of_regions_of_open`'s own hypothesis,
and there the pencil has a double root (`EndpointCollision`), so `∂_t D` vanishes and
`ftFixedFactor` is `-lc(B)/0` — which is `0` under Lean's division convention, with
nothing in a build to report it.  So `hSd`, `hS0` and `h0` are all stated on
`Ioo 0 (π/r)`, where the branch is genuinely pinned.

**`h0` is on the open arc, which is why the block containment had to be weakened.**
`PhaseVariationBlocks.exists_varPhase_of_blocks` asks `Icc (Lb i) (Rb i) ⊆ s` for every
`i`, and a degenerate block sitting at an endpoint defeats `s = Ioo 0 (π/r)`.  A block
that is a point or empty has zero variation, so `exists_varPhase_of_nondegenerate_blocks`
replaces it by `∅` before the sum and asks the containment only where `Lb i < Rb i`.
Without that the variation bound would have to be asked on the closed arc, where the
branch's two endpoint values are the same division convention again.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
and the principal amplitude» (`sec:geometry`, `eq:W-def`, `eq:W-on-g`,
`lem:amplitude-divisor`, `cor:linear-phase-variation`, `eq:phase-derivative-bound`), in
the form «Angular discrepancy and proof of the main theorem» (`subsec:proof`) consumes
it.

## Tags

phase supply, argument branch, phase variation, logarithmic derivative
-/

namespace ForgacsTran

open Set Real

theorem im_logDeriv_eq_of_polar_branch {W : ℝ → ℂ} {dW : ℂ} {ψ : ℝ → ℝ} {dψ a b θ : ℝ}
    (hab : a < b) (hθ : θ ∈ Icc a b)
    (hfac : ∀ x ∈ Icc a b, W x = ((‖W x‖ : ℝ) : ℂ) * Complex.exp ((ψ x : ℂ) * Complex.I))
    (hW : HasDerivAt W dW θ) (hψ : HasDerivAt ψ dψ θ) (hW0 : W θ ≠ 0) :
    dψ = (dW / W θ).im := by
  have hEd : HasDerivAt (fun y => Complex.exp (-(ψ y : ℂ) * Complex.I))
      (Complex.exp (-(ψ θ : ℂ) * Complex.I) * (-(dψ : ℂ) * Complex.I)) θ :=
    (((hψ.ofReal_comp).neg).mul_const Complex.I).cexp
  have hgd : HasDerivAt (fun y => W y * Complex.exp (-(ψ y : ℂ) * Complex.I))
      (dW * Complex.exp (-(ψ θ : ℂ) * Complex.I)
        + W θ * (Complex.exp (-(ψ θ : ℂ) * Complex.I) * (-(dψ : ℂ) * Complex.I))) θ :=
    hW.mul hEd
  have hgval : ∀ x ∈ Icc a b,
      W x * Complex.exp (-(ψ x : ℂ) * Complex.I) = ((‖W x‖ : ℝ) : ℂ) := by
    intro x hx
    have h := hfac x hx
    have hcancel : Complex.exp ((ψ x : ℂ) * Complex.I)
        * Complex.exp (-(ψ x : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add,
        show ((ψ x : ℂ) * Complex.I + -(ψ x : ℂ) * Complex.I) = 0 from by ring,
        Complex.exp_zero]
    calc W x * Complex.exp (-(ψ x : ℂ) * Complex.I)
        = ((‖W x‖ : ℝ) : ℂ) * (Complex.exp ((ψ x : ℂ) * Complex.I)
            * Complex.exp (-(ψ x : ℂ) * Complex.I)) := by rw [← mul_assoc, ← h]
      _ = ((‖W x‖ : ℝ) : ℂ) := by rw [hcancel, mul_one]
  have him : ∀ x ∈ Icc a b, (W x * Complex.exp (-(ψ x : ℂ) * Complex.I)).im = 0 := by
    intro x hx; rw [hgval x hx]; simp
  have hzero : HasDerivWithinAt
      (fun y => (W y * Complex.exp (-(ψ y : ℂ) * Complex.I)).im) 0 (Icc a b) θ :=
    (hasDerivWithinAt_const θ (Icc a b) (0 : ℝ)).congr him (him θ hθ)
  have hone : HasDerivWithinAt
      (fun y => (W y * Complex.exp (-(ψ y : ℂ) * Complex.I)).im)
      (dW * Complex.exp (-(ψ θ : ℂ) * Complex.I)
        + W θ * (Complex.exp (-(ψ θ : ℂ) * Complex.I)
          * (-(dψ : ℂ) * Complex.I))).im (Icc a b) θ := by
    exact hgd.im.hasDerivWithinAt
  have hkey : (dW * Complex.exp (-(ψ θ : ℂ) * Complex.I)
      + W θ * (Complex.exp (-(ψ θ : ℂ) * Complex.I) * (-(dψ : ℂ) * Complex.I))).im = 0 :=
    (uniqueDiffOn_Icc hab θ hθ).eq_deriv (Icc a b) hone hzero
  have halg : dW * Complex.exp (-(ψ θ : ℂ) * Complex.I)
      + W θ * (Complex.exp (-(ψ θ : ℂ) * Complex.I) * (-(dψ : ℂ) * Complex.I))
      = ((‖W θ‖ : ℝ) : ℂ) * (dW / W θ - (dψ : ℂ) * Complex.I) := by
    rw [← hgval θ hθ]
    field
  rw [halg] at hkey
  have hn : ‖W θ‖ ≠ 0 := norm_ne_zero_iff.2 hW0
  have hkey2 : ‖W θ‖ * ((dW / W θ).im - dψ) = 0 := by
    rw [← hkey]; simp [Complex.mul_im, Complex.sub_im]
  rcases mul_eq_zero.1 hkey2 with h | h
  · exact absurd h hn
  · linarith

/-- Derivative of a multiset-indexed sum of real branches, term by term. -/
private theorem hasDerivAt_multisetSum {f : ℂ → ℝ → ℝ} {f' : ℂ → ℝ} {θ : ℝ} (m : Multiset ℂ)
    (h : ∀ β ∈ m, HasDerivAt (f β) (f' β) θ) :
    HasDerivAt (fun y => (m.map (fun β => f β y)).sum) ((m.map f').sum) θ := by
  induction m using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const θ (0 : ℝ)
  | cons a m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (h a (Multiset.mem_cons_self a m)).add
        (ih fun β hβ => h β (Multiset.mem_cons_of_mem hβ))

/-- The fixed factor of `eq:W-on-g` along the principal branch. -/
noncomputable def ftFixedFactor (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  -(B.leadingCoeff
    / (ftCofactor Q r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)).eval (ftPrincipal τ θ))

theorem ftAmp_eq_ftFixedFactor_mul (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (θ : ℝ) :
    ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ftFixedFactor Q B r z τ θ
        * (B.roots.map (fun β => ftPrincipal τ θ - β)).prod :=
  ftAmp_eq_fixed_mul_prod Q B r _ _

/-- `∂_t D` along the principal branch: the cofactor of `eq:W-def`, evaluated at the
principal root.  Carries `Q`, `r`, `z` and `τ` and **no weight**. -/
noncomputable def ftCofactorAlong (Q : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  (ftCofactor Q r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)).eval (ftPrincipal τ θ)

theorem ftFixedFactor_eq (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) :
    ftFixedFactor Q B r z τ
      = fun θ => -B.leadingCoeff * (ftCofactorAlong Q r z τ θ)⁻¹ := by
  funext θ
  rw [ftFixedFactor, ftCofactorAlong]
  ring

theorem hasDerivAt_ftFixedFactor {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {dSx : ℂ} {x : ℝ}
    (hS : HasDerivAt (ftCofactorAlong Q r z τ) dSx x)
    (hS0 : ftCofactorAlong Q r z τ x ≠ 0) :
    HasDerivAt (ftFixedFactor Q B r z τ)
      (-B.leadingCoeff * (-dSx / (ftCofactorAlong Q r z τ x) ^ 2)) x := by
  rw [ftFixedFactor_eq]
  exact HasDerivAt.const_mul _ (hS.inv hS0)

theorem im_logDeriv_ftFixedFactor {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {dSx : ℂ}
    {x : ℝ} (hB0 : B ≠ 0) (hS0 : ftCofactorAlong Q r z τ x ≠ 0) :
    ((-B.leadingCoeff * (-dSx / (ftCofactorAlong Q r z τ x) ^ 2))
        / ftFixedFactor Q B r z τ x).im
      = -(dSx / ftCofactorAlong Q r z τ x).im := by
  have hlc : B.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hB0
  simp only [ftFixedFactor_eq]
  rw [show (-B.leadingCoeff * (-dSx / (ftCofactorAlong Q r z τ x) ^ 2))
      / (-B.leadingCoeff * (ftCofactorAlong Q r z τ x)⁻¹)
      = -(dSx / ftCofactorAlong Q r z τ x) from by field_simp]
  rw [Complex.neg_im]

/-- The branch of `arg` of the fixed factor, written on the **cofactor**: `B` enters the
fixed factor only through `-lc(B)`, a nonzero constant, which the logarithmic derivative
kills.  Carries no weight, which is what lets `κ₀` be bound ahead of `∀ B`. -/
noncomputable def ftFixedAngle (Q : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ)
    (dS : ℝ → ℂ) (c : ℝ) (θ : ℝ) : ℝ :=
  -polarAngle (ftCofactorAlong Q r z τ) dS 0 c θ

theorem hasDerivAt_ftFixedAngle {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {dS : ℝ → ℂ}
    {c : ℝ} {V : Set ℝ} (hV : IsOpen V) (hconn : V.OrdConnected)
    (hSd : ∀ s ∈ V, HasDerivAt (ftCofactorAlong Q r z τ) (dS s) s)
    (hSc : ContinuousOn dS V)
    (hS0 : ∀ s ∈ V, ftCofactorAlong Q r z τ s ≠ 0)
    (hc : c ∈ V) {x : ℝ} (hx : x ∈ V) :
    HasDerivAt (ftFixedAngle Q r z τ dS c)
      (-(dS x / ftCofactorAlong Q r z τ x).im) x := by
  have key : ∀ a b : ℝ, Icc a b ⊆ V → c ∈ Icc a b → x ∈ Icc a b →
      HasDerivAt (ftFixedAngle Q r z τ dS c)
        (-(dS x / ftCofactorAlong Q r z τ x).im) x := by
    intro a b hsub hcm hxm
    have h := hasDerivAt_polarAngle_base (β := (0 : ℂ)) hV hsub hSd hSc
      (fun s hs => by simpa using hS0 s (hsub hs)) hcm hxm
    have h2 := h.neg
    rw [sub_zero] at h2
    exact h2
  rcases le_total c x with h | h
  · exact key c x (hconn.out hc hx) ⟨le_rfl, h⟩ ⟨h, le_rfl⟩
  · exact key x c (hconn.out hx hc) ⟨h, le_rfl⟩ ⟨le_rfl, h⟩


theorem exists_varPhase_of_nondegenerate_blocks {k : ℕ} {ψ₀ : ℝ → ℝ} {Lb Rb : Fin k → ℝ}
    {ψ : ℂ → Fin k → ℝ → ℝ} {Ψ dΨ : Fin k → ℝ → ℝ}
    {κ₀ Kγ : ℝ} {B : Polynomial ℂ} {s : Set ℝ}
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hJ : ∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ s)
    (hord : ∀ i j : Fin k, i < j → Rb i ≤ Lb j)
    (h0 : eVariationOn ψ₀ s ≤ ENNReal.ofReal κ₀)
    (hroots : ∀ β ∈ B.roots,
      ∑ i, eVariationOn (ψ β i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal (Kγ + π))
    (hΨ : ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i), HasDerivAt (Ψ i) (dΨ i x) x)
    (hsum : ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i),
      HasDerivAt (fun y => ψ₀ y + (B.roots.map (fun β => ψ β i y)).sum) (dΨ i x) x) :
    ∃ varψ : Fin k → ℝ, (∀ i, 0 ≤ varψ i) ∧
      (∀ i, Lb i ≤ Rb i → |Ψ i (Rb i) - Ψ i (Lb i)| ≤ varψ i) ∧
      ∑ i, varψ i ≤ κ₀ + (Kγ + π) * B.natDegree := by
  classical
  set J : Fin k → Set ℝ := fun i => if Lb i < Rb i then Icc (Lb i) (Rb i) else ∅ with hJdef
  have hvar : ∀ (f : ℝ → ℝ) (i : Fin k),
      eVariationOn f (J i) = eVariationOn f (Icc (Lb i) (Rb i)) := by
    intro f i
    by_cases h : Lb i < Rb i
    · simp only [hJdef, if_pos h]
    · simp only [hJdef, if_neg h]
      rw [eVariationOn.subsingleton f Set.subsingleton_empty,
        eVariationOn.subsingleton f (Set.subsingleton_Icc_of_ge (not_lt.1 h))]
  have hJsub : ∀ i, J i ⊆ s := by
    intro i
    by_cases h : Lb i < Rb i
    · simp only [hJdef, if_pos h]; exact hJ i h
    · simp only [hJdef, if_neg h]; exact Set.empty_subset s
  have hordJ : ∀ i j : Fin k, i < j → ∀ x ∈ J i, ∀ y ∈ J j, x ≤ y := by
    intro i j hij x hx y hy
    by_cases hi : Lb i < Rb i
    · by_cases hj : Lb j < Rb j
      · simp only [hJdef, if_pos hi] at hx
        simp only [hJdef, if_pos hj] at hy
        exact le_trans hx.2 (le_trans (hord i j hij) hy.1)
      · simp only [hJdef, if_neg hj] at hy; exact absurd hy (Set.notMem_empty y)
    · simp only [hJdef, if_neg hi] at hx; exact absurd hx (Set.notMem_empty x)
  have hroots' : ∀ β ∈ B.roots,
      ∑ i, eVariationOn (ψ β i) (J i) ≤ ENNReal.ofReal (Kγ + π) := by
    intro β hβ
    have he : ∑ i, eVariationOn (ψ β i) (J i)
        = ∑ i, eVariationOn (ψ β i) (Icc (Lb i) (Rb i)) :=
      Finset.sum_congr rfl fun i _ => hvar (ψ β i) i
    rw [he]; exact hroots β hβ
  have hmain := linear_phase_variation_components_fin hκ₀ hKγ hJsub hordJ h0 hroots'
  have he : ∑ i, eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum) (J i)
      = ∑ i, eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum)
          (Icc (Lb i) (Rb i)) :=
    Finset.sum_congr rfl fun i _ =>
      hvar (fun x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum) i
  rw [he] at hmain
  have hKπ : (0 : ℝ) ≤ Kγ + π := by linarith [Real.pi_pos]
  obtain ⟨varψ, hnn, hinc, hsumle⟩ :=
    exists_varPhase_of_sum_eVariationOn
      (ψ := fun i x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum)
      (add_nonneg hκ₀ (mul_nonneg hKπ (Nat.cast_nonneg _))) hmain
  refine ⟨varψ, hnn, fun i hi => ?_, hsumle⟩
  rcases eq_or_lt_of_le hi with heq | hlt
  · rw [heq, sub_self, abs_zero]; exact hnn i
  have hL : Lb i ∈ Icc (Lb i) (Rb i) := ⟨le_rfl, hi⟩
  have hR : Rb i ∈ Icc (Lb i) (Rb i) := ⟨hi, le_rfl⟩
  have heq2 := sub_eq_sub_of_hasDerivAt_eq (f := Ψ i)
    (g := fun y => ψ₀ y + (B.roots.map (fun β => ψ β i y)).sum)
    (f' := dΨ i) (hΨ i hlt) (hsum i hlt) hL hR
  rw [heq2]
  exact hinc i hi



/-- The two states a zero `β` of `B` can be in relative to the arc, in the form
`PhaseVariationBlocks.sum_eVariationOn_branch_le` consumes: either the arc misses `β`
and one branch based at `a` serves every block, or the arc meets it once, at `m`, and
each block takes the branch based at whichever endpoint its side of `m` reaches. -/
def RootBranchState (γ dγ d2γ : ℝ → ℂ) (β : ℂ) (a b : ℝ) {k : ℕ}
    (Lb Rb : Fin k → ℝ) (ψ : Fin k → ℝ → ℝ) : Prop :=
  (∃ S : Finset ℝ, (∀ x ∈ Icc a b, γ x ≠ β) ∧ (∀ x ∈ S, x ∈ Icc a b)
      ∧ (∀ x ∈ Ioo a b, ∀ j : ℤ,
          polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (j : ℝ) * π → x ∈ S)
      ∧ ∀ i, ψ i = polarAngle γ dγ β a)
    ∨ (∃ m, a ≤ m ∧ m ≤ b ∧ ∃ S₁ S₂ : Finset ℝ, γ m = β
        ∧ (∀ x ∈ Icc a b, x ≠ m → γ x ≠ β)
        ∧ (∀ x ∈ Ioo a m, ∀ j : ℤ,
            polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (j : ℝ) * π → x ∈ S₁)
        ∧ (∀ x ∈ Ioo m b, ∀ j : ℤ,
            polarAngle dγ d2γ 0 a x - polarAngle γ dγ β b x = (j : ℝ) * π → x ∈ S₂)
        ∧ ∀ i, (Icc (Lb i) (Rb i) ⊆ Ico a m ∧ ψ i = polarAngle γ dγ β a)
            ∨ (Icc (Lb i) (Rb i) ⊆ Ioc m b ∧ ψ i = polarAngle γ dγ β b))

/-- **The block branches of a root state are differentiable, with derivative
`Im(γ'/(γ - β))`.**  Each block is joined to its own base point by a sub-interval the arc
crosses without meeting `β`: the whole of `[a,b]` when the arc misses `β`, and `[a, R i]`
or `[L i, b]` on the two sides of `m` when it meets it.  No one interval serves every
block in the second state, which is why the base point travels with the side. -/
theorem hasDerivAt_of_rootBranchState {γ dγ d2γ : ℝ → ℂ} {U : Set ℝ} {a b : ℝ} {β : ℂ}
    {k : ℕ} {Lb Rb : Fin k → ℝ} {ψ : Fin k → ℝ → ℝ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc a b)
    (hstate : RootBranchState γ dγ d2γ β a b Lb Rb ψ) :
    ∀ i, Lb i ≤ Rb i → ∀ x ∈ Icc (Lb i) (Rb i),
      HasDerivAt (ψ i) ((dγ x / (γ x - β)).im) x := by
  rcases hstate with ⟨S, hne, -, -, hψ⟩ | ⟨m, ham, hmb, S₁, S₂, -, hne, -, -, hside⟩
  · intro i _ x hx
    rw [hψ i]
    exact hasDerivAt_polarAngle_base hU hsub hd hc hne ⟨le_rfl, hab⟩ (hJ i hx)
  · intro i hle x hx
    have hLmem : Lb i ∈ Icc (Lb i) (Rb i) := ⟨le_rfl, hle⟩
    have hRmem : Rb i ∈ Icc (Lb i) (Rb i) := ⟨hle, le_rfl⟩
    rcases hside i with ⟨hsubI, hψi⟩ | ⟨hsubI, hψi⟩
    · have hRlt : Rb i < m := (hsubI hRmem).2
      have hale : a ≤ Rb i := (hsubI hRmem).1
      have hsub' : Icc a (Rb i) ⊆ U :=
        fun s hs => hsub ⟨hs.1, le_trans hs.2 (le_trans hRlt.le hmb)⟩
      have hne' : ∀ s ∈ Icc a (Rb i), γ s ≠ β := fun s hs =>
        hne s ⟨hs.1, le_trans hs.2 (le_trans hRlt.le hmb)⟩
          (ne_of_lt (lt_of_le_of_lt hs.2 hRlt))
      rw [hψi]
      exact hasDerivAt_polarAngle_base hU hsub' hd hc hne' ⟨le_rfl, hale⟩
        ⟨le_trans (hsubI hLmem).1 hx.1, hx.2⟩
    · have hLgt : m < Lb i := (hsubI hLmem).1
      have hble : Lb i ≤ b := (hsubI hLmem).2
      have hsub' : Icc (Lb i) b ⊆ U :=
        fun s hs => hsub ⟨le_trans (le_trans ham hLgt.le) hs.1, hs.2⟩
      have hne' : ∀ s ∈ Icc (Lb i) b, γ s ≠ β := fun s hs =>
        hne s ⟨le_trans (le_trans ham hLgt.le) hs.1, hs.2⟩
          (ne_of_gt (lt_of_lt_of_le hLgt hs.1))
      rw [hψi]
      exact hasDerivAt_polarAngle_base hU hsub' hd hc hne' ⟨hble, le_rfl⟩
        ⟨hx.1, le_trans hx.2 (hsubI hRmem).2⟩

/-- **The per-root data `exists_ftBranchSupply` consumes, from the root states.**  The
variation cap is `sum_eVariationOn_branch_le`; the derivative clause is
`hasDerivAt_of_rootBranchState`.  The two travel together because they are about the
same branch: a cap proved for one choice of base points says nothing about the branch
whose derivative the phase supply needs. -/
theorem exists_branchData_of_rootStates {γ dγ d2γ : ℝ → ℂ} {U : Set ℝ} {a b Kγ : ℝ}
    {B : Polynomial ℂ} {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0) (hKγ : 0 ≤ Kγ)
    (hKvar : eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) ≤ ENNReal.ofReal Kγ)
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc a b)
    (hord : ∀ i j : Fin k, i < j → Rb i ≤ Lb j)
    (hstates : ∀ β ∈ B.roots, ∃ ψ : Fin k → ℝ → ℝ,
      RootBranchState γ dγ d2γ β a b Lb Rb ψ) :
    ∃ ψ : ℂ → Fin k → ℝ → ℝ,
      (∀ β ∈ B.roots, ∀ i, Lb i ≤ Rb i → ∀ x ∈ Icc (Lb i) (Rb i),
        HasDerivAt (ψ β i) ((dγ x / (γ x - β)).im) x) ∧
      (∀ β ∈ B.roots,
        ∑ i, eVariationOn (ψ β i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal (Kγ + π)) := by
  classical
  have hc : ContinuousOn dγ U := fun x hx => (hd2 x hx).continuousAt.continuousWithinAt
  refine ⟨fun β => if h : β ∈ B.roots then Classical.choose (hstates β h) else 0, ?_, ?_⟩
  · intro β hβ
    simp only [dif_pos hβ]
    exact hasDerivAt_of_rootBranchState hab hU hsub hd hc hJ
      (Classical.choose_spec (hstates β hβ))
  · intro β hβ
    simp only [dif_pos hβ]
    exact sum_eVariationOn_branch_le hab hU hsub hd hd2 hc2 hreg hKγ hKvar hJ hord
      (Classical.choose_spec (hstates β hβ))

/-! ### The endpoint values replaced by what they were used for

`ArcPhaseBound.exists_phase_family_of_regions_of_open` asks the amplitude to vanish at
both ends of the arc, and its proof spends that hypothesis in one place only: a block on
which the amplitude does not vanish cannot reach an endpoint at which it does, so the
block lies in the open arc, where the derivative data lives.  It is a means to block
interiority and nothing else.

At `2 ≤ r` the means is unavailable.  The upper endpoint of the arc is the origin, the
pencil does not vanish there, and `AmplitudeUpperEndpoint.hWL_false_of_two_le_r` shows the
formalized amplitude is a nonzero number — while the paper's
`W = B(γ)·γ/(rQ(γ) − γQ′(γ))` carries an explicit `γ` and does vanish.  The divergence is
`x/0`'s mirror: at the lower endpoint the formalized amplitude is `0` where the true one
blows up, and here it is finite where the true one vanishes.

Asking for interiority directly removes the divergence from the statement rather than
encoding it, and it is no extra burden on a producer: `AngularDiscrepancyFT.FTPhaseSupply`
already hands its branch clause the guarded `Icc (Lb i) (Rb i) ⊆ Ret`, and every
admissible `Ret` sits inside the collar of `eq:retained-range`, hence inside the open arc.
A pencil that does have the vanishing keeps the cheap route, through
`interior_of_endpoint_vanishing`.

**The same fact punctures the two outer regions.**  `ArcPhaseBound`'s endpoint collars —
`exists_bound_im_logDeriv_ftAmp_endpoint` at a finite endpoint and
`exists_bound_im_logDeriv_ftAmp_origin` at the origin one — conclude on `Ioc 0 b'`, and
the two seam lemmas that lift a punctured collar to the closed interval ask for the
endpoint value again: `forall_Icc_of_Ioc_of_eq_zero` for `W 0 = 0` and
`forall_Icc_of_Ico_of_eq_zero` for `W L = 0`.  So a region binder written on `Icc` routes
the amplitude group's defect into the region group, and at `2 ≤ r` it is unsatisfiable
there for the same reason.  Asking `h₁` on `Ioc 0 b₁` and `h₃` on `Ico b₂ L` takes the
collars in the shape they are proved in, and neither seam is needed: the truncation is `0`
at both endpoints, so neither is ever consulted.  The three half-open regions still cover
the open arc, with **no** ordering assumption on `b₁` and `b₂`.
-/

/-- **Endpoint vanishing gives block interiority.**  This is the step
`ArcPhaseBound.exists_phase_family_of_regions_of_open` takes internally, exposed so that a
caller which has the endpoint values meets the interiority binder in one application. -/
theorem interior_of_endpoint_vanishing {W : ℝ → ℂ} {L : ℝ} {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hL : ∀ i, Lb i ∈ Icc (0 : ℝ) L) (hR : ∀ i, Rb i ∈ Icc (0 : ℝ) L)
    (hW0 : W 0 = 0) (hWL : W L = 0)
    (hne : ∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), W θ ≠ 0) :
    ∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) L := by
  intro i hi x hx
  refine ⟨lt_of_le_of_ne (le_trans (hL i).1 hx.1) ?_,
    lt_of_le_of_ne (le_trans hx.2 (hR i).2) ?_⟩
  · intro h; exact hne i hi x hx (by rw [← h]; exact hW0)
  · intro h; exact hne i hi x hx (by rw [h]; exact hWL)

/-- **`ArcPhaseBound.exists_phase_family_of_regions_of_open` with the two endpoint values
replaced by block interiority.**  The proof runs the open-arc assembly at the amplitude
truncated to the open arc — `W'` is `W` on `Ioo 0 L` and `0` outside it.  The truncation
meets the endpoint hypotheses by definition rather than by a fact about `W`, agrees with
`W` on every interior block, and is invisible in the statement. -/
theorem exists_phase_family_of_regions_of_interior {W dW : ℝ → ℂ} {U : Set ℝ}
    {L b₁ b₂ κ₁ κ₂ κ₃ : ℝ}
    (hsub : Ioo (0 : ℝ) L ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (h₁ : ∀ s ∈ Ioc (0 : ℝ) b₁, W s ≠ 0 → |(dW s / W s).im| ≤ κ₁)
    (h₂ : ∀ s ∈ Icc b₁ b₂, W s ≠ 0 → |(dW s / W s).im| ≤ κ₂)
    (h₃ : ∀ s ∈ Ico b₂ L, W s ≠ 0 → |(dW s / W s).im| ≤ κ₃) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) L) → (∀ i, Rb i ∈ Icc (0 : ℝ) L) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) L) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), W θ ≠ 0) →
      ∃ ψ dψ : Fin k → ℝ → ℝ,
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          W θ = ((‖W θ‖ : ℝ) : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) := by
  classical
  set W' : ℝ → ℂ := fun s => if s ∈ Ioo (0 : ℝ) L then W s else 0 with hW'def
  have hW'eq : ∀ s ∈ Ioo (0 : ℝ) L, W' s = W s := fun s hs => if_pos hs
  have hW'ne : ∀ s, W' s ≠ 0 → s ∈ Ioo (0 : ℝ) L := by
    intro s hs
    by_contra h
    exact hs (if_neg h)
  have hd' : ∀ s ∈ Ioo (0 : ℝ) L, HasDerivAt W' (dW s) s := fun s hs =>
    (hd s (hsub hs)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs) (fun y hy => hW'eq y hy))
  -- the three regions cover the OPEN arc with no ordering assumption on `b₁`, `b₂`, and
  -- the truncation is `0` at both endpoints, so neither endpoint is ever consulted
  have hbd' : ∀ s ∈ Icc (0 : ℝ) L, W' s ≠ 0 → |(dW s / W' s).im| ≤ max κ₁ (max κ₂ κ₃) := by
    intro s _ hs0
    have hmem := hW'ne s hs0
    have hWne : W s ≠ 0 := by rwa [hW'eq s hmem] at hs0
    rw [hW'eq s hmem]
    rcases le_or_gt s b₁ with h | h
    · exact le_trans (h₁ s ⟨hmem.1, h⟩ hWne) (le_max_left _ _)
    · rcases le_or_gt s b₂ with h2 | h2
      · exact le_trans (h₂ s ⟨h.le, h2⟩ hWne) (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact le_trans (h₃ s ⟨h2.le, hmem.2⟩ hWne)
          (le_trans (le_max_right _ _) (le_max_right _ _))
  have hzero : W' 0 = 0 := if_neg (by simp)
  have hLzero : W' L = 0 := if_neg (by simp)
  obtain ⟨M₀, hM₀⟩ := exists_phase_family_of_bound_of_open (W := W') (dW := dW)
    (U := Ioo (0 : ℝ) L) isOpen_Ioo Subset.rfl hd' (hc.mono hsub) hzero hLzero hbd'
  refine ⟨M₀, fun M hM k Lb Rb hL hR hint hne => ?_⟩
  obtain ⟨ψ, dψ, hfac, hψd, hψb⟩ := hM₀ M hM k Lb Rb hL hR
    (fun i hi θ hθ => by rw [hW'eq θ (hint i hi hθ)]; exact hne i hi θ hθ)
  refine ⟨ψ, dψ, fun i hi θ hθ => ?_, hψd, hψb⟩
  have := hfac i hi θ hθ
  rwa [hW'eq θ (hint i hi hθ)] at this

/-- **`AngularDiscrepancyFT.FTPhaseSupply`'s branch clause.**  `κ₀` and `Kγ` are carried
by hypotheses that mention no weight — `h0` and `hKvar` are about the cofactor and the
tangent alone — so a `B`-dependent constant is unstateable here rather than merely
wrong. -/
theorem exists_ftBranchSupply
    {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {U : Set ℝ} {dW dS dγ : ℝ → ℂ}
    {b₁ b₂ c₁ c₂ c₃ c₀ κ₀ Kγ : ℝ}
    (hB0 : B ≠ 0)
    (_hU : IsOpen U) (hsub : Ioo (0 : ℝ) (π / r) ⊆ U)
    (hWd : ∀ s ∈ U,
      HasDerivAt (fun x => ftAmp Q B r ((z x : ℝ) : ℂ) (ftPrincipal τ x)) (dW s) s)
    (hWc : ContinuousOn dW U)
    (h₁ : ∀ s ∈ Ioc (0 : ℝ) b₁, ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
      |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₁)
    (h₂ : ∀ s ∈ Icc b₁ b₂, ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
      |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₂)
    (h₃ : ∀ s ∈ Ico b₂ (π / r), ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
      |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₃)
    (hγd : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt (ftPrincipal τ) (dγ s) s)
    (hSd : ∀ s ∈ Ioo (0 : ℝ) (π / r),
      HasDerivAt (ftCofactorAlong Q r z τ) (dS s) s)
    (hSc : ContinuousOn dS (Ioo (0 : ℝ) (π / r)))
    (hS0 : ∀ s ∈ Ioo (0 : ℝ) (π / r), ftCofactorAlong Q r z τ s ≠ 0)
    (hc₀ : c₀ ∈ Ioo (0 : ℝ) (π / r))
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (h0 : eVariationOn (ftFixedAngle Q r z τ dS c₀) (Ioo (0 : ℝ) (π / r))
      ≤ ENNReal.ofReal κ₀)
    (hroot : ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) (π / r)) → (∀ i, Rb i ∈ Icc (0 : ℝ) (π / r)) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / r)) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
      ∃ ψ : ℂ → Fin k → ℝ → ℝ,
        (∀ β ∈ B.roots, ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i),
          HasDerivAt (ψ β i) ((dγ x / (ftPrincipal τ x - β)).im) x) ∧
        (∀ β ∈ B.roots,
          ∑ i, eVariationOn (ψ β i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal (Kγ + π))) :
    ∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) (π / r)) → (∀ i, Rb i ∈ Icc (0 : ℝ) (π / r)) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / r)) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
            = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ)
              * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀ + (Kγ + π) * B.natDegree := by
  obtain ⟨M₀, hM₀⟩ :=
    exists_phase_family_of_regions_of_interior hsub hWd hWc h₁ h₂ h₃
  refine ⟨M₀, fun M hM k Lb Rb hL hR hord hint hne => ?_⟩
  obtain ⟨Ψ, dΨ, hfacΨ, hΨd, hbd⟩ := hM₀ M hM k Lb Rb hL hR hint hne
  obtain ⟨ψ, hψd, hψvar⟩ := hroot k Lb Rb hL hR hord hint hne
  have hblkIoo : ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i), x ∈ Ioo (0 : ℝ) (π / r) :=
    fun i hi x hx => hint i hi hx
  have hdΨ : ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i),
      dΨ i x = (dW x / ftAmp Q B r ((z x : ℝ) : ℂ) (ftPrincipal τ x)).im := by
    intro i hi x hx
    exact im_logDeriv_eq_of_polar_branch
      (W := fun s => ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)) (ψ := Ψ i)
      (a := Lb i) (b := Rb i) (θ := x) hi hx (hfacΨ i hi)
      (hWd x (hsub (hblkIoo i hi x hx))) (hΨd i hi x hx) (hne i hi x hx)
  have hsum : ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i),
      HasDerivAt (fun y => ftFixedAngle Q r z τ dS c₀ y
        + (B.roots.map (fun β => ψ β i y)).sum) (dΨ i x) x := by
    intro i hi x hx
    have hxIoo := hblkIoo i hi x hx
    have hWne := hne i hi x hx
    have hVne : ftFixedFactor Q B r z τ x ≠ 0 := by
      intro h
      exact hWne (by rw [ftAmp_eq_ftFixedFactor_mul, h, zero_mul])
    have hsplit := im_logDeriv_factorization (V := ftFixedFactor Q B r z τ)
      (γ := ftPrincipal τ)
      (W := fun s => ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s))
      B.roots isOpen_Ioo hxIoo
      (hasDerivAt_ftFixedFactor (hSd x hxIoo) (hS0 x hxIoo)) (hγd x hxIoo)
      (hWd x (hsub hxIoo)) hVne
      (fun β hβ => sub_ne_zero.2 (ne_root_of_ftAmp_ne_zero hWne hβ))
      (fun s _ => ftAmp_eq_ftFixedFactor_mul Q B r z τ s)
    rw [hdΨ i hi x hx, hsplit, im_logDeriv_ftFixedFactor hB0 (hS0 x hxIoo)]
    exact (hasDerivAt_ftFixedAngle isOpen_Ioo Set.ordConnected_Ioo hSd hSc hS0 hc₀ hxIoo).add
      (hasDerivAt_multisetSum B.roots (fun β hβ => hψd β hβ i hi x hx))
  obtain ⟨varψ, hnn, hinc, hsumle⟩ :=
    exists_varPhase_of_nondegenerate_blocks (ψ₀ := ftFixedAngle Q r z τ dS c₀) (ψ := ψ)
      (s := Ioo (0 : ℝ) (π / r)) hκ₀ hKγ (fun i hi x hx => hblkIoo i hi x hx) hord h0
      hψvar hΨd hsum
  exact ⟨Ψ, dΨ, varψ,
    fun i hi θ hθ => by simpa only [ftPrincipalAmp] using hfacΨ i hi θ hθ,
    hΨd, hbd, hnn, fun i hi => hinc i hi.le, hsumle⟩

/-- **The same driven by the root states.**  `exists_branchData_of_rootStates` supplies
`hroot`; everything else is unchanged. -/
theorem exists_ftBranchSupply_of_rootStates
    {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {U : Set ℝ} {dW dS dγ d2γ : ℝ → ℂ}
    {b₁ b₂ c₁ c₂ c₃ c₀ κ₀ Kγ : ℝ}
    (hB0 : B ≠ 0)
    (hU : IsOpen U) (hsub : Ioo (0 : ℝ) (π / r) ⊆ U)
    (hWd : ∀ s ∈ U,
      HasDerivAt (fun x => ftAmp Q B r ((z x : ℝ) : ℂ) (ftPrincipal τ x)) (dW s) s)
    (hWc : ContinuousOn dW U)
    (h₁ : ∀ s ∈ Ioc (0 : ℝ) b₁, ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
      |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₁)
    (h₂ : ∀ s ∈ Icc b₁ b₂, ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
      |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₂)
    (h₃ : ∀ s ∈ Ico b₂ (π / r), ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
      |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₃)
    (hγd : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt (ftPrincipal τ) (dγ s) s)
    (hd2 : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt dγ (d2γ s) s)
    (hc2 : ContinuousOn d2γ (Ioo (0 : ℝ) (π / r)))
    (hreg : ∀ s ∈ Ioo (0 : ℝ) (π / r), dγ s ≠ 0)
    (hKvar : ∀ c ∈ Ioo (0 : ℝ) (π / r),
      eVariationOn (polarAngle dγ d2γ 0 c) (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal Kγ)
    (hSd : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt (ftCofactorAlong Q r z τ) (dS s) s)
    (hSc : ContinuousOn dS (Ioo (0 : ℝ) (π / r)))
    (hS0 : ∀ s ∈ Ioo (0 : ℝ) (π / r), ftCofactorAlong Q r z τ s ≠ 0)
    (hc₀ : c₀ ∈ Ioo (0 : ℝ) (π / r))
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (h0 : eVariationOn (ftFixedAngle Q r z τ dS c₀) (Ioo (0 : ℝ) (π / r))
      ≤ ENNReal.ofReal κ₀)
    (hstates : ∀ (a' b' : ℝ), a' ≤ b' → Icc a' b' ⊆ Ioo (0 : ℝ) (π / r) →
      ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc a' b') → (∀ i, Rb i ∈ Icc a' b') →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
      ∀ β ∈ B.roots, ∃ ψ : Fin k → ℝ → ℝ,
        RootBranchState (ftPrincipal τ) dγ d2γ β a' b' Lb Rb ψ) :
    ∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) (π / r)) → (∀ i, Rb i ∈ Icc (0 : ℝ) (π / r)) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / r)) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
            = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ)
              * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀ + (Kγ + π) * B.natDegree :=
  exists_ftBranchSupply hB0 hU hsub hWd hWc h₁ h₂ h₃
    hγd hSd hSc hS0 hc₀ hκ₀ hKγ h0
    (fun k Lb Rb hL hR hord hint hne => by
      classical
      have hKπ : (0 : ℝ) ≤ Kγ + π := by linarith [Real.pi_pos]
      have hblkIoo : ∀ i, Lb i < Rb i → ∀ x ∈ Icc (Lb i) (Rb i), x ∈ Ioo (0 : ℝ) (π / r) :=
        fun i hi x hx => hint i hi hx
      by_cases hex : ∃ i, Lb i < Rb i
      · obtain ⟨i₀, hi₀⟩ := hex
        set S : Finset (Fin k) := Finset.univ.filter (fun i => Lb i < Rb i) with hSdef
        have hmemS : ∀ i, i ∈ S ↔ Lb i < Rb i := by intro i; simp [hSdef]
        have hSne : S.Nonempty := ⟨i₀, (hmemS i₀).2 hi₀⟩
        set a' : ℝ := S.inf' hSne Lb with ha'
        set b' : ℝ := S.sup' hSne Rb with hb'
        have ha'Ioo : a' ∈ Ioo (0 : ℝ) (π / r) := by
          obtain ⟨j, hjS, hj⟩ := Finset.exists_mem_eq_inf' hSne Lb
          have hjnd := (hmemS j).1 hjS
          rw [ha', hj]
          exact hblkIoo j hjnd (Lb j) ⟨le_rfl, hjnd.le⟩
        have hb'Ioo : b' ∈ Ioo (0 : ℝ) (π / r) := by
          obtain ⟨j, hjS, hj⟩ := Finset.exists_mem_eq_sup' hSne Rb
          have hjnd := (hmemS j).1 hjS
          rw [hb', hj]
          exact hblkIoo j hjnd (Rb j) ⟨hjnd.le, le_rfl⟩
        have hinf : ∀ i, Lb i < Rb i → a' ≤ Lb i := fun i hi =>
          Finset.inf'_le _ ((hmemS i).2 hi)
        have hsup : ∀ i, Lb i < Rb i → Rb i ≤ b' := fun i hi =>
          Finset.le_sup' _ ((hmemS i).2 hi)
        have ha'b' : a' < b' := lt_of_le_of_lt (hinf i₀ hi₀) (lt_of_lt_of_le hi₀ (hsup i₀ hi₀))
        have hsubab : Icc a' b' ⊆ Ioo (0 : ℝ) (π / r) :=
          fun x hx => ⟨lt_of_lt_of_le ha'Ioo.1 hx.1, lt_of_le_of_lt hx.2 hb'Ioo.2⟩
        -- degenerate blocks are emptied INSIDE the hull, so `hstates` sees closed blocks
        set Lb' : Fin k → ℝ := fun i => if Lb i < Rb i then Lb i else b' with hLb'
        set Rb' : Fin k → ℝ := fun i => if Lb i < Rb i then Rb i else a' with hRb'
        have hnd : ∀ i, Lb i < Rb i → Lb' i = Lb i ∧ Rb' i = Rb i := by
          intro i hi
          constructor
          · simp only [hLb']; rw [if_pos hi]
          · simp only [hRb']; rw [if_pos hi]
        have hdegL : ∀ i, ¬ Lb i < Rb i → Lb' i = b' := by
          intro i hi; simp only [hLb']; rw [if_neg hi]
        have hdegR : ∀ i, ¬ Lb i < Rb i → Rb' i = a' := by
          intro i hi; simp only [hRb']; rw [if_neg hi]
        have hdeg : ∀ i, ¬ Lb i < Rb i → Icc (Lb' i) (Rb' i) = (∅ : Set ℝ) := by
          intro i hi
          rw [hdegL i hi, hdegR i hi]
          exact Icc_eq_empty (by linarith)
        have hL' : ∀ i, Lb' i ∈ Icc a' b' := by
          intro i
          by_cases hi : Lb i < Rb i
          · rw [(hnd i hi).1]; exact ⟨hinf i hi, le_trans hi.le (hsup i hi)⟩
          · rw [hdegL i hi]; exact ⟨ha'b'.le, le_rfl⟩
        have hR' : ∀ i, Rb' i ∈ Icc a' b' := by
          intro i
          by_cases hi : Lb i < Rb i
          · rw [(hnd i hi).2]; exact ⟨le_trans (hinf i hi) hi.le, hsup i hi⟩
          · rw [hdegR i hi]; exact ⟨le_rfl, ha'b'.le⟩
        have hord' : ∀ i j : Fin k, i < j → Rb' i ≤ Lb' j := by
          intro i j hij
          by_cases hi : Lb i < Rb i
          · rw [(hnd i hi).2]
            by_cases hj : Lb j < Rb j
            · rw [(hnd j hj).1]; exact hord i j hij
            · rw [hdegL j hj]; exact hsup i hi
          · rw [hdegR i hi]
            by_cases hj : Lb j < Rb j
            · rw [(hnd j hj).1]; exact hinf j hj
            · rw [hdegL j hj]; exact ha'b'.le
        have hne' : ∀ i, ∀ θ ∈ Icc (Lb' i) (Rb' i),
            ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0 := by
          intro i θ hθ
          by_cases hi : Lb i < Rb i
          · obtain ⟨h1, h2⟩ := hnd i hi
            rw [h1, h2] at hθ
            exact hne i hi θ hθ
          · rw [hdeg i hi] at hθ
            exact absurd hθ (Set.notMem_empty θ)
        obtain ⟨ψ, hψd, hψvar⟩ :=
          exists_branchData_of_rootStates (B := B) ha'b'.le isOpen_Ioo hsubab
            (fun s hs => hγd s hs) (fun s hs => hd2 s hs) hc2
            (fun s hs => hreg s (hsubab hs)) hKγ
            (le_trans (eVariationOn.mono _ hsubab) (hKvar a' (hsubab ⟨le_rfl, ha'b'.le⟩)))
            (fun i => Icc_subset_Icc (hL' i).1 (hR' i).2) hord'
            (hstates a' b' ha'b'.le hsubab k Lb' Rb' hL' hR' hord' hne')
        refine ⟨ψ, fun β hβ i hi x hx => ?_, fun β hβ => ?_⟩
        · obtain ⟨h1, h2⟩ := hnd i hi
          exact hψd β hβ i (by rw [h1, h2]; exact hi.le) x (by rw [h1, h2]; exact hx)
        · have heq : ∀ i : Fin k, eVariationOn (ψ β i) (Icc (Lb i) (Rb i))
              = eVariationOn (ψ β i) (Icc (Lb' i) (Rb' i)) := by
            intro i
            by_cases hi : Lb i < Rb i
            · obtain ⟨h1, h2⟩ := hnd i hi; rw [h1, h2]
            · rw [hdeg i hi, eVariationOn.subsingleton _ Set.subsingleton_empty,
                eVariationOn.subsingleton _ (Set.subsingleton_Icc_of_ge (not_lt.1 hi))]
          rw [Finset.sum_congr rfl (fun i _ => heq i)]
          exact hψvar β hβ
      · -- every block is a point or empty: no branch is asked for and none varies
        refine ⟨fun _ _ _ => 0, fun β hβ i hi => absurd ⟨i, hi⟩ hex, fun β hβ => ?_⟩
        have hz : ∀ i : Fin k, eVariationOn (fun _ : ℝ => (0 : ℝ)) (Icc (Lb i) (Rb i)) = 0 :=
          fun i => eVariationOn.constant_on (by rintro x ⟨p, -, rfl⟩ y ⟨q, -, rfl⟩; rfl)
        rw [Finset.sum_congr rfl (fun i _ => hz i)]
        simp)

/-- **`eq:Dprime-identity` along the arc.**  `∂_t D = E(t)/t` at a nonzero root of the
pencil, so the cofactor along the principal branch is `E(γ)/γ` — and `E = XQ' - rQ`
carries no weight and no spectral parameter. -/
theorem ftCofactorAlong_eq_ftCritical_div {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {z τ : ℝ → ℝ} {θ : ℝ} (hγ0 : ftPrincipal τ θ ≠ 0)
    (hroot : (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) :
    ftCofactorAlong Q r z τ θ
      = (ftCritical Q r).eval (ftPrincipal τ θ) / ftPrincipal τ θ := by
  rw [ftCofactorAlong, ← eval_derivative_ftDen hroot,
    eval_derivative_ftDen_eq_ftCritical_div hr hγ0 hroot]

/-- **`hS0`, discharged.**  The cofactor along the arc vanishes exactly where the arc
meets a zero of `E` — which is a collision, and `EndpointCollision` puts those at the
ends of the arc, not inside it. -/
theorem ftCofactorAlong_ne_zero {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {z τ : ℝ → ℝ} {θ : ℝ} (hγ0 : ftPrincipal τ θ ≠ 0)
    (hroot : (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hE : (ftCritical Q r).eval (ftPrincipal τ θ) ≠ 0) :
    ftCofactorAlong Q r z τ θ ≠ 0 := by
  rw [ftCofactorAlong_eq_ftCritical_div hr hγ0 hroot]
  exact div_ne_zero hE hγ0

theorem hasDerivAt_ftPrincipal {τ : ℝ → ℝ} {dτ θ : ℝ} (h : HasDerivAt τ dτ θ) :
    HasDerivAt (ftPrincipal τ)
      ((dτ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
        + ((τ θ : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I))) θ := by
  have h1 : HasDerivAt (fun s : ℝ => ((τ s : ℝ) : ℂ)) ((dτ : ℝ) : ℂ) θ := h.ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I)) θ :=
    (((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).cexp
  exact h1.mul h2

/-- **The arc's own logarithmic derivative has imaginary part exactly one.**
`γ = τ e^{iθ}` with `τ` real, so `γ'/γ = τ'/τ + i` and the modulus contributes nothing.
This is `im_logDeriv_ofRealSub_zpow`'s mechanism in its cleanest instance: the whole
`1/γ` of `∂_t D = E(γ)/γ` costs the bound one, at every parameter and with no collar. -/
theorem im_logDeriv_ftPrincipal {τ : ℝ → ℝ} {dτ θ : ℝ} {dγ : ℂ}
    (hτd : HasDerivAt τ dτ θ) (hτ0 : τ θ ≠ 0)
    (hγ : HasDerivAt (ftPrincipal τ) dγ θ) :
    (dγ / ftPrincipal τ θ).im = 1 := by
  have heq : dγ = (dτ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      + ((τ θ : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I)) :=
    hγ.unique (hasDerivAt_ftPrincipal hτd)
  have hE : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hτc : ((τ θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hτ0
  have : dγ / ftPrincipal τ θ = ((dτ : ℝ) : ℂ) / ((τ θ : ℝ) : ℂ) + Complex.I := by
    rw [heq, ftPrincipal]
    field_simp
  rw [this]
  simp [Complex.div_im]

section CofactorAlong

open Polynomial

variable {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}

/-- `E = XQ' - rQ` evaluated along the principal branch — the subject of the fourth
region family, and it carries neither the weight nor the spectral parameter. -/
noncomputable def ftCriticalAlong (Q : Polynomial ℂ) (r : ℕ) (τ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  (ftCritical Q r).eval (ftPrincipal τ θ)

theorem hasDerivAt_ftCriticalAlong {θ : ℝ} {dγ : ℂ}
    (hγ : HasDerivAt (ftPrincipal τ) dγ θ) :
    HasDerivAt (ftCriticalAlong Q r τ)
      (dγ * (derivative (ftCritical Q r)).eval (ftPrincipal τ θ)) θ :=
  hasDerivAt_eval_comp (γ := ftPrincipal τ) (dγ := fun _ => dγ) (ftCritical Q r) hγ

theorem im_logDeriv_ftCofactorAlong_eq (hr : 1 ≤ r) {θ dτ : ℝ} {dγ dS : ℂ}
    (hev : ∀ᶠ s in nhds θ, ftPrincipal τ s ≠ 0
      ∧ (ftDen Q r ((z s : ℝ) : ℂ)).eval (ftPrincipal τ s) = 0)
    (hτd : HasDerivAt τ dτ θ) (hτ0 : τ θ ≠ 0)
    (hγ : HasDerivAt (ftPrincipal τ) dγ θ)
    (hE : ftCriticalAlong Q r τ θ ≠ 0)
    (hSd : HasDerivAt (ftCofactorAlong Q r z τ) dS θ) :
    (dS / ftCofactorAlong Q r z τ θ).im
      = (logDeriv (ftCriticalAlong Q r τ) θ).im - 1 := by
  have hγ0 : ftPrincipal τ θ ≠ 0 := hev.self_of_nhds |>.1
  have hfeq : ftCofactorAlong Q r z τ =ᶠ[nhds θ]
      fun s => ftCriticalAlong Q r τ s / ftPrincipal τ s := by
    filter_upwards [hev] with s hs
    exact ftCofactorAlong_eq_ftCritical_div hr hs.1 hs.2
  have hstep : dS / ftCofactorAlong Q r z τ θ = logDeriv (ftCofactorAlong Q r z τ) θ := by
    rw [logDeriv_apply, hSd.deriv]
  rw [hstep, logDeriv_congr_of_eventuallyEq hfeq,
    logDeriv_div (f := ftCriticalAlong Q r τ) (g := ftPrincipal τ) θ hE hγ0
      (hasDerivAt_ftCriticalAlong hγ).differentiableAt hγ.differentiableAt,
    Complex.sub_im]
  congr 1
  rw [logDeriv_apply, hγ.deriv]
  exact im_logDeriv_ftPrincipal hτd hτ0 hγ

/-- **The fourth region family, reduced.**  `∂_t D = E(γ)/γ`, and the `1/γ` costs exactly
one, so the whole of `hbd` is a bound on `Im` of the logarithmic derivative of `E` along
the arc — a polynomial composition carrying neither the weight nor the spectral
parameter. -/
theorem abs_im_logDeriv_ftCofactorAlong_le (hr : 1 ≤ r) {θ dτ κ : ℝ} {dγ dS : ℂ}
    (hev : ∀ᶠ s in nhds θ, ftPrincipal τ s ≠ 0
      ∧ (ftDen Q r ((z s : ℝ) : ℂ)).eval (ftPrincipal τ s) = 0)
    (hτd : HasDerivAt τ dτ θ) (hτ0 : τ θ ≠ 0)
    (hγ : HasDerivAt (ftPrincipal τ) dγ θ)
    (hE : ftCriticalAlong Q r τ θ ≠ 0)
    (hSd : HasDerivAt (ftCofactorAlong Q r z τ) dS θ)
    (hbd : |(logDeriv (ftCriticalAlong Q r τ) θ).im| ≤ κ) :
    |(dS / ftCofactorAlong Q r z τ θ).im| ≤ κ + 1 := by
  rw [im_logDeriv_ftCofactorAlong_eq hr hev hτd hτ0 hγ hE hSd]
  calc |(logDeriv (ftCriticalAlong Q r τ) θ).im - 1|
      ≤ |(logDeriv (ftCriticalAlong Q r τ) θ).im| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ κ + 1 := by rw [abs_one]; linarith

/-- **Away from a collision, the bound is continuity and nothing else.** -/
theorem abs_im_logDeriv_ftCriticalAlong_le {θ : ℝ} {dγ : ℂ}
    (hγ : HasDerivAt (ftPrincipal τ) dγ θ) :
    |(logDeriv (ftCriticalAlong Q r τ) θ).im|
      ≤ ‖dγ‖ * ‖(derivative (ftCritical Q r)).eval (ftPrincipal τ θ)‖
          / ‖ftCriticalAlong Q r τ θ‖ := by
  refine le_trans (abs_im_logDeriv_le (ftCriticalAlong Q r τ) θ) (le_of_eq ?_)
  rw [(hasDerivAt_ftCriticalAlong hγ).deriv, norm_mul]

/-- The order to which `E` vanishes where the arc meets the collision. -/
noncomputable def ftCollisionOrder (Q : Polynomial ℂ) (r : ℕ) (τ : ℝ → ℝ) (θ₀ : ℝ) : ℕ :=
  rootMultiplicity (ftPrincipal τ θ₀) (ftCritical Q r)

/-- `E` with the collision's zero divided out. -/
noncomputable def ftCriticalReduced (Q : Polynomial ℂ) (r : ℕ) (τ : ℝ → ℝ) (θ₀ : ℝ) :
    Polynomial ℂ :=
  ftCritical Q r /ₘ (X - C (ftPrincipal τ θ₀)) ^ ftCollisionOrder Q r τ θ₀

theorem eval_ftCriticalReduced_ne_zero (hE : ftCritical Q r ≠ 0) (θ₀ : ℝ) :
    (ftCriticalReduced Q r τ θ₀).eval (ftPrincipal τ θ₀) ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero _ hE

theorem deriv_comp_const_sub {F : ℝ → ℂ} {dF : ℂ} {c δ : ℝ}
    (h : HasDerivAt F dF (c - δ)) : deriv (fun s : ℝ => F (c - s)) δ = -dF := by
  have hs : HasDerivAt (fun s : ℝ => c - s) (-1 : ℝ) δ := by
    simpa using (hasDerivAt_id δ).const_sub c
  have := h.scomp δ hs
  simpa [Function.comp_def, smul_eq_mul] using this.deriv

/-- **Reflecting the arc negates the logarithmic derivative and nothing else.**
`ftPrincipal` does not reflect — the phase factor travels with the parameter — so the
endpoint estimate at the far end is taken at the reflected branch as an abstract path, and
this is what carries its bound back.  The absolute value makes the sign immaterial. -/
theorem abs_im_logDeriv_comp_const_sub {F : ℝ → ℂ} {dF : ℂ} {c δ : ℝ}
    (h : HasDerivAt F dF (c - δ)) :
    |(deriv (fun s : ℝ => F (c - s)) δ / F (c - δ)).im| = |(dF / F (c - δ)).im| := by
  rw [deriv_comp_const_sub h, neg_div, Complex.neg_im, abs_neg]

/-- **`∂_t D` at a collision endpoint, factored.**  The twin of
`ArcPhaseBound.ftAmp_eq_endpoint_factorization` with the weight removed: `E` degenerates
to order `m`, the divided difference splits that into a real power and a cofactor, and
what is left is `H(γ)/γ` — a quotient of two polynomials along the branch, neither
vanishing.  The exponent is a natural number here rather than the amplitude's `ν - (k-1)`,
because no numerator is present to raise it. -/
theorem ftCofactorEval_eq_endpoint_factorization {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {γ zf : ℝ → ℂ} {te : ℂ} {H : Polynomial ℂ} {m : ℕ} {δ : ℝ}
    (hEfac : ftCritical Q r = (X - C te) ^ m * H)
    (hδ : δ ≠ 0) (hγ : γ δ ≠ 0)
    (hroot : (ftDen Q r (zf δ)).eval (γ δ) = 0) :
    (ftCofactor Q r (zf δ) (γ δ)).eval (γ δ)
      = 1 * ((δ : ℂ) - (((0 : ℝ)) : ℂ)) ^ ((m : ℕ) : ℤ)
          * (endpointCofactor (fun s : ℝ => γ s - te) δ) ^ ((m : ℕ) : ℤ)
          * (H.eval (γ δ) / (X : Polynomial ℂ).eval (γ δ)) := by
  have hδne : ((δ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ
  have hsub : γ δ - te
      = ((δ : ℂ) - (((0 : ℝ)) : ℂ)) * endpointCofactor (fun s : ℝ => γ s - te) δ := by
    rw [endpointCofactor]
    simp only [Complex.ofReal_zero, sub_zero]
    field_simp
  have hEev : (ftCritical Q r).eval (γ δ) = (γ δ - te) ^ m * H.eval (γ δ) := by
    rw [hEfac]; simp
  rw [← eval_derivative_ftDen hroot, eval_derivative_ftDen_eq_ftCritical_div hr hγ hroot,
    hEev, hsub, mul_pow, zpow_natCast, zpow_natCast, eval_X]
  field_simp

/-- **The collar at a collision endpoint, for `∂_t D`.**  The twin of
`ArcPhaseBound.exists_bound_im_logDeriv_ftAmp_endpoint`, weight-free, and the binders are
one-sided at `0` for the same reason: the parameter is an angular distance, so a two-sided
derivative at the endpoint asks for the negation of the phenomenon.  `hte` is what
confines it to a **collision**: at the endpoint where the branch runs into the origin the
outer factor's `1/‖γ‖` diverges, and that end is covered by
`abs_im_logDeriv_ftCofactorAlong_le_of_bounds` instead. -/
theorem exists_bound_im_logDeriv_ftCofactor_endpoint {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    {γ dγ zf : ℝ → ℂ} {te : ℂ} {H : Polynomial ℂ} {m : ℕ} {b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L)
    (hEfac : ftCritical Q r = (X - C te) ^ m * H) (hH0 : H.eval te ≠ 0)
    (hte : te ≠ 0) (hγ0 : γ 0 = te)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ)
    (h0 : dγ 0 ≠ 0)
    (hroot : ∀ δ ∈ Ioc (0 : ℝ) b, (ftDen Q r (zf δ)).eval (γ δ) = 0) :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ C ∧
      ∀ δ ∈ Ioc (0 : ℝ) b',
        |(deriv (fun s : ℝ => (ftCofactor Q r (zf s) (γ s)).eval (γ s)) δ
            / (ftCofactor Q r (zf δ) (γ δ)).eval (γ δ)).im| ≤ C := by
  classical
  set g : ℝ → ℂ := fun s : ℝ => γ s - te with hg
  set A : ℝ → ℂ := fun s => H.eval (γ s) / (X : Polynomial ℂ).eval (γ s) with hA
  obtain ⟨b₁, hb₁0, hb₁b, hune, hudiff, hubd⟩ :=
    exists_bound_im_logDeriv_endpointCofactor (γ := g) (dγ := dγ) hb hL
      (by simp [hg, hγ0]) (by simpa [hg] using hd0.sub_const te)
      (fun θ hθ => by simpa [hg] using (hd θ hθ).sub_const te) hlip h0
  set D : ℝ := ‖dγ 0‖ + L * b with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set Ψ : ℝ → ℝ := fun s => ‖(derivative H).eval (γ s)‖ / ‖H.eval (γ s)‖
    + ‖(derivative (X : Polynomial ℂ)).eval (γ s)‖ / ‖(X : Polynomial ℂ).eval (γ s)‖ with hΨ
  have hΨnn : ∀ s, 0 ≤ Ψ s := fun s => by rw [hΨ]; positivity
  have hγc : ContinuousWithinAt γ (Ici (0 : ℝ)) 0 := hd0.continuousWithinAt
  have hγc' : ContinuousWithinAt γ (Ioi (0 : ℝ)) 0 := hγc.mono Ioi_subset_Ici_self
  have hγ0ne : γ 0 ≠ 0 := by rw [hγ0]; exact hte
  have hp : ∀ P : Polynomial ℂ, ContinuousWithinAt (fun s : ℝ => P.eval (γ s))
      (Ioi (0 : ℝ)) 0 := fun P =>
    ((Polynomial.continuous P).continuousAt).comp_continuousWithinAt hγc'
  have hH0' : H.eval (γ 0) ≠ 0 := by rw [hγ0]; exact hH0
  have hX0' : (X : Polynomial ℂ).eval (γ 0) ≠ 0 := by simpa using hγ0ne
  have hΨc : ContinuousWithinAt Ψ (Ioi (0 : ℝ)) 0 :=
    ((hp _).norm.div (hp H).norm (norm_ne_zero_iff.mpr hH0')).add
      ((hp _).norm.div (hp X).norm (norm_ne_zero_iff.mpr hX0'))
  set K : ℝ := Ψ 0 + 1 with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith [hΨnn 0]
  have hγev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), γ δ ≠ 0 := hγc'.eventually_ne hγ0ne
  have hHev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), H.eval (γ δ) ≠ 0 :=
    (hp H).eventually_ne hH0'
  have hΨev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), Ψ δ < K :=
    hΨc.eventually_lt_const (by rw [hK]; linarith)
  obtain ⟨b₂, hb₂mem, hb₂⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp (hγev.and hHev |>.and hΨev)
  have hb₂0 : (0 : ℝ) < b₂ := hb₂mem
  set bb : ℝ := min b₁ b₂ with hbb
  have hbb0 : 0 < bb := lt_min hb₁0 hb₂0
  refine ⟨bb / 2, (m : ℝ) * (3 * L / ‖dγ 0‖) + D * K, by linarith, by
      have : bb ≤ b₁ := min_le_left _ _
      linarith [hb₁b],
    add_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (by linarith) (norm_nonneg _))) (mul_nonneg hD0 hK0), ?_⟩
  intro δ hδ
  have hδlt : δ < bb := by linarith [hδ.2]
  have hδ0 : δ ≠ 0 := ne_of_gt hδ.1
  have hδ₁ : δ ∈ Icc (0 : ℝ) b₁ := ⟨hδ.1.le, le_trans hδlt.le (min_le_left _ _)⟩
  have hδ₂ : δ ∈ Ioc (0 : ℝ) b₂ := ⟨hδ.1, le_trans hδlt.le (min_le_right _ _)⟩
  obtain ⟨⟨hγn, hHn⟩, hΨδ⟩ := hb₂ hδ₂
  have hδb : δ ∈ Ioc (0 : ℝ) b :=
    ⟨hδ.1, le_trans (le_trans hδlt.le (min_le_left _ _)) hb₁b⟩
  have hγd : HasDerivAt γ (dγ δ) δ := hd δ hδb
  have hXn : (X : Polynomial ℂ).eval (γ δ) ≠ 0 := by simpa using hγn
  have hfac : (fun s : ℝ => (ftCofactor Q r (zf s) (γ s)).eval (γ s)) =ᶠ[nhds δ]
      fun s : ℝ => 1 * ((s : ℂ) - (((0 : ℝ)) : ℂ)) ^ ((m : ℕ) : ℤ)
        * (endpointCofactor g s) ^ ((m : ℕ) : ℤ) * A s := by
    filter_upwards [Ioo_mem_nhds hδ.1 hδlt] with x hx
    have hx₂ : x ∈ Ioc (0 : ℝ) b₂ := ⟨hx.1, le_trans hx.2.le (min_le_right _ _)⟩
    have hxb : x ∈ Ioc (0 : ℝ) b :=
      ⟨hx.1, le_trans (le_trans hx.2.le (min_le_left _ _)) hb₁b⟩
    obtain ⟨⟨hxγ, -⟩, -⟩ := hb₂ hx₂
    exact ftCofactorEval_eq_endpoint_factorization hr hEfac (ne_of_gt hx.1) hxγ (hroot x hxb)
  have hHd := hasDerivAt_eval_comp H hγd
  have hXd := hasDerivAt_eval_comp (X : Polynomial ℂ) hγd
  have hAd : DifferentiableAt ℝ A δ := by
    rw [hA]; exact hHd.differentiableAt.div hXd.differentiableAt hXn
  have hA0 : A δ ≠ 0 := by rw [hA]; exact div_ne_zero hHn hXn
  have houter : |(logDeriv A δ).im| ≤ D * K := by
    have hdb : ‖dγ δ‖ ≤ D := by
      have hnb : ‖dγ δ‖ ≤ ‖dγ 0‖ + ‖dγ δ - dγ 0‖ := by
        simpa using norm_add_le (dγ 0) (dγ δ - dγ 0)
      have hl := hlip δ ⟨hδ.1.le, hδb.2⟩
      have hLb : L * δ ≤ L * b := by nlinarith [hδb.2]
      rw [hD]; linarith
    calc |(logDeriv A δ).im| ≤ ‖dγ δ‖ * Ψ δ := by
          rw [hA, hΨ]
          exact abs_im_logDeriv_polyRatio_le H X hγd hHn hXn
      _ ≤ D * K := mul_le_mul hdb hΨδ.le (hΨnn δ) hD0
  have hkey := abs_im_logDeriv_le_of_local_factorization_outer (θ₀ := (0 : ℝ))
    (m := ((m : ℕ) : ℤ)) (p := ((m : ℕ) : ℤ)) hδ0 (one_ne_zero) hfac
    (hudiff δ hδ₁ hδ0) (hune δ hδ₁ hδ0) hAd hA0 (hubd δ hδ₁ hδ0) houter
  have hcast : |(((m : ℕ) : ℤ) : ℝ)| = (m : ℝ) := by
    push_cast; exact abs_of_nonneg (Nat.cast_nonneg m)
  rwa [hcast] at hkey

/-- **The collar at the collision the arc starts from**, in the arc's own parameter. -/
theorem exists_bound_im_logDeriv_ftCofactorAlong_lower {Q : Polynomial ℂ} {r : ℕ}
    {z τ : ℝ → ℝ} {dγ dS : ℝ → ℂ} {H : Polynomial ℂ} {m : ℕ} {b L : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) (hL : 0 ≤ L)
    (hEfac : ftCritical Q r = (X - C (ftPrincipal τ 0)) ^ m * H)
    (hH0 : H.eval (ftPrincipal τ 0) ≠ 0) (hte : ftPrincipal τ 0 ≠ 0)
    (hd0 : HasDerivWithinAt (ftPrincipal τ) (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt (ftPrincipal τ) (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ) (h0 : dγ 0 ≠ 0)
    (hroot : ∀ δ ∈ Ioc (0 : ℝ) b,
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    (hSd : ∀ δ ∈ Ioc (0 : ℝ) b, HasDerivAt (ftCofactorAlong Q r z τ) (dS δ) δ) :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ C ∧
      ∀ θ ∈ Ioo (0 : ℝ) b', |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C := by
  obtain ⟨b', C, hb'0, hb'b, hC0, hbd⟩ :=
    exists_bound_im_logDeriv_ftCofactor_endpoint (γ := ftPrincipal τ)
      (zf := fun s : ℝ => ((z s : ℝ) : ℂ)) (te := ftPrincipal τ 0) (H := H) (m := m)
      hr hb hL hEfac hH0 hte rfl hd0 hd hlip h0 hroot
  refine ⟨b', C, hb'0, hb'b, hC0, fun θ hθ => ?_⟩
  have hθb : θ ∈ Ioc (0 : ℝ) b' := ⟨hθ.1, hθ.2.le⟩
  have hθbb : θ ∈ Ioc (0 : ℝ) b := ⟨hθ.1, le_trans hθ.2.le hb'b⟩
  have h : |(deriv (ftCofactorAlong Q r z τ) θ
      / ftCofactorAlong Q r z τ θ).im| ≤ C := hbd θ hθb
  rwa [(hSd θ hθbb).deriv] at h

/-- **The collar at a collision the arc ENDS at.**  The reflected branch is what the
endpoint estimate sees, because `ftPrincipal` does not reflect; the bound comes back
through `abs_im_logDeriv_comp_const_sub`. -/
theorem exists_bound_im_logDeriv_ftCofactorAlong_upper {Q : Polynomial ℂ} {r : ℕ}
    {z τ : ℝ → ℝ} {dγ dS : ℝ → ℂ} {H : Polynomial ℂ} {m : ℕ} {c b L : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) (hL : 0 ≤ L)
    (hEfac : ftCritical Q r = (X - C (ftPrincipal τ c)) ^ m * H)
    (hH0 : H.eval (ftPrincipal τ c) ≠ 0) (hte : ftPrincipal τ c ≠ 0)
    (hd0 : HasDerivWithinAt (fun s : ℝ => ftPrincipal τ (c - s)) (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ δ ∈ Ioc (0 : ℝ) b,
      HasDerivAt (fun s : ℝ => ftPrincipal τ (c - s)) (dγ δ) δ)
    (hlip : ∀ δ ∈ Icc (0 : ℝ) b, ‖dγ δ - dγ 0‖ ≤ L * δ) (h0 : dγ 0 ≠ 0)
    (hroot : ∀ δ ∈ Ioc (0 : ℝ) b,
      (ftDen Q r ((z (c - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (c - δ)) = 0)
    (hSd : ∀ δ ∈ Ioc (0 : ℝ) b,
      HasDerivAt (ftCofactorAlong Q r z τ) (dS (c - δ)) (c - δ)) :
    ∃ b' C : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ C ∧
      ∀ θ ∈ Ioo (c - b') c, |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C := by
  obtain ⟨b', C, hb'0, hb'b, hC0, hbd⟩ :=
    exists_bound_im_logDeriv_ftCofactor_endpoint
      (γ := fun s : ℝ => ftPrincipal τ (c - s))
      (zf := fun s : ℝ => ((z (c - s) : ℝ) : ℂ)) (te := ftPrincipal τ c) (H := H) (m := m)
      hr hb hL hEfac hH0 hte (by simp) hd0 hd hlip h0 hroot
  refine ⟨b', C, hb'0, hb'b, hC0, fun θ hθ => ?_⟩
  have hδ : c - θ ∈ Ioc (0 : ℝ) b' := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hδb : c - θ ∈ Ioc (0 : ℝ) b := ⟨hδ.1, le_trans hδ.2 hb'b⟩
  have hcs : c - (c - θ) = θ := by ring
  have h : |(deriv (fun s : ℝ => ftCofactorAlong Q r z τ (c - s)) (c - θ)
      / ftCofactorAlong Q r z τ (c - (c - θ))).im| ≤ C := hbd (c - θ) hδ
  rw [abs_im_logDeriv_comp_const_sub (hSd (c - θ) hδb)] at h
  rwa [hcs] at h

/-- **`hEfac` and `hH0` at the canonical factorization.**  `ArcPhaseBound`'s endpoint
estimates take the degeneracy of `E` as `E = (X - t_e)^m H` with `H(t_e) ≠ 0`; the
multiplicity supplies both. -/
theorem ftCritical_eq_pow_mul_ftCriticalReduced (Q : Polynomial ℂ) (r : ℕ) (τ : ℝ → ℝ)
    (θ₀ : ℝ) :
    ftCritical Q r = (X - C (ftPrincipal τ θ₀)) ^ ftCollisionOrder Q r τ θ₀
      * ftCriticalReduced Q r τ θ₀ :=
  (pow_mul_divByMonic_rootMultiplicity_eq _ _).symm

/-- **Away from a collision, the bound is continuity and the constant one.**  `E(γ)` is
bounded away from zero on the region, `γ'` is bounded on it, and the whole of the `1/γ`
factor of `∂_t D = E(γ)/γ` costs exactly one — which is what lets this cover the endpoint
at which the branch runs into the **origin**, where `1/‖γ‖` diverges and no bound through
the modulus survives. -/
theorem abs_im_logDeriv_ftCofactorAlong_le_of_bounds (hr : 1 ≤ r) {dγ dS : ℝ → ℂ}
    {dτ : ℝ → ℝ} {a c D K : ℝ}
    (hstate : ∀ s ∈ Ioo a c, ftPrincipal τ s ≠ 0
      ∧ (ftDen Q r ((z s : ℝ) : ℂ)).eval (ftPrincipal τ s) = 0
      ∧ ftCriticalAlong Q r τ s ≠ 0)
    (hτd : ∀ s ∈ Ioo a c, HasDerivAt τ (dτ s) s)
    (hγd : ∀ s ∈ Ioo a c, HasDerivAt (ftPrincipal τ) (dγ s) s)
    (hSd : ∀ s ∈ Ioo a c, HasDerivAt (ftCofactorAlong Q r z τ) (dS s) s)
    (hD : ∀ s ∈ Ioo a c, ‖dγ s‖ ≤ D)
    (hK : ∀ s ∈ Ioo a c,
      ‖(derivative (ftCritical Q r)).eval (ftPrincipal τ s)‖
        / ‖ftCriticalAlong Q r τ s‖ ≤ K) :
    ∀ θ ∈ Ioo a c, |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ D * K + 1 := by
  intro θ hθ
  obtain ⟨hγ0, -, hEne⟩ := hstate θ hθ
  have hτ0 : τ θ ≠ 0 := fun h => hγ0 (by rw [ftPrincipal, h]; simp)
  have hnbhd : ∀ᶠ s in nhds θ, ftPrincipal τ s ≠ 0
      ∧ (ftDen Q r ((z s : ℝ) : ℂ)).eval (ftPrincipal τ s) = 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with s hs
    exact ⟨(hstate s hs).1, (hstate s hs).2.1⟩
  have hbd : |(logDeriv (ftCriticalAlong Q r τ) θ).im| ≤ D * K := by
    refine le_trans (abs_im_logDeriv_ftCriticalAlong_le (hγd θ hθ)) ?_
    rw [mul_div_assoc]
    exact mul_le_mul (hD θ hθ) (hK θ hθ) (by positivity) (le_trans (norm_nonneg _) (hD θ hθ))
  exact abs_im_logDeriv_ftCofactorAlong_le hr hnbhd (hτd θ hθ) hτ0 (hγd θ hθ) hEne
    (hSd θ hθ) hbd

/-- **The three regions over the OPEN arc.**  `abs_le_of_cover_three_of_ne_zero` covers a
closed interval under a nonvanishing guard; the fixed factor's angle is pinned on the open
arc and nowhere else, so the cover is taken there and the two outer pieces are open. -/
theorem exists_bound_im_logDeriv_ftCofactorAlong_of_cover {dS : ℝ → ℂ}
    {b₁ b₂ C₁ C₂ C₃ : ℝ}
    (hlo : ∀ θ ∈ Ioo (0 : ℝ) b₁, |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C₁)
    (hmid : ∀ θ ∈ Icc b₁ b₂, |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C₂)
    (hhi : ∀ θ ∈ Ioo b₂ (π / r), |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C₃) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ κ := by
  refine ⟨max 0 (max C₁ (max C₂ C₃)), le_max_left _ _, fun θ hθ => ?_⟩
  rcases lt_or_ge θ b₁ with h | h
  · exact le_trans (hlo θ ⟨hθ.1, h⟩)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · rcases le_or_gt θ b₂ with h' | h'
    · refine le_trans (hmid θ ⟨h, h'⟩) ?_
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    · refine le_trans (hhi θ ⟨h', hθ.2⟩) ?_
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

/-- **The middle region, by compactness.**  Nothing analytic: `Im((∂_t D)'/∂_t D)` is
continuous where the cofactor does not vanish, and a closed sub-interval of the open arc
is compact. -/
theorem exists_bound_im_logDeriv_ftCofactorAlong_mid {dS : ℝ → ℂ} {b₁ b₂ : ℝ}
    (hSd : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt (ftCofactorAlong Q r z τ) (dS s) s)
    (hSc : ContinuousOn dS (Ioo (0 : ℝ) (π / r)))
    (hS0 : ∀ s ∈ Ioo (0 : ℝ) (π / r), ftCofactorAlong Q r z τ s ≠ 0)
    (hsub : Icc b₁ b₂ ⊆ Ioo (0 : ℝ) (π / r)) :
    ∃ C : ℝ, ∀ θ ∈ Icc b₁ b₂, |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C := by
  have hScont : ContinuousOn (ftCofactorAlong Q r z τ) (Ioo (0 : ℝ) (π / r)) :=
    fun s hs => (hSd s hs).continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun θ : ℝ => (dS θ / ftCofactorAlong Q r z τ θ).im)
      (Ioo (0 : ℝ) (π / r)) :=
    Complex.continuous_im.comp_continuousOn (hSc.div hScont hS0)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := b₁) (b := b₂)).exists_bound_of_continuousOn
    (hg.mono hsub)
  exact ⟨C, fun θ hθ => by simpa [Real.norm_eq_abs] using hC θ hθ⟩

/-- **`hS0` in the shape `exists_ftBranchSupply` takes it.**  The cofactor along the arc
vanishes only where the arc meets a zero of `E`, and those are the collisions at the two
ends. -/
theorem ftCofactorAlong_ne_zero_on {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} (hr : 1 ≤ r)
    (hstate : ∀ s ∈ Ioo (0 : ℝ) (π / r), ftPrincipal τ s ≠ 0
      ∧ (ftDen Q r ((z s : ℝ) : ℂ)).eval (ftPrincipal τ s) = 0
      ∧ ftCriticalAlong Q r τ s ≠ 0) :
    ∀ s ∈ Ioo (0 : ℝ) (π / r), ftCofactorAlong Q r z τ s ≠ 0 := fun s hs =>
  ftCofactorAlong_ne_zero hr (hstate s hs).1 (hstate s hs).2.1 (hstate s hs).2.2

end CofactorAlong

/-- **`hlip` from a bounded second derivative on the collar.**  The collar's Lipschitz
hypothesis is awkward to supply directly; what a branch actually carries is `γ''`,
continuous up to the endpoint.  Compactness turns one into the other, and the derivative
at the endpoint is asked for **within `Ici 0`** only — which is all an arc endpoint has. -/
theorem exists_lipschitz_of_continuousOn_deriv2 {f f' : ℝ → ℂ} {b : ℝ} (hb0 : 0 < b)
    (hd0 : HasDerivWithinAt f (f' 0) (Ici 0) 0)
    (hd : ∀ x ∈ Ioc (0 : ℝ) b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Icc 0 b)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ ∈ Icc (0 : ℝ) b, ‖f θ - f 0‖ ≤ L * θ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have hderiv : ∀ x ∈ Icc (0 : ℝ) b, HasDerivWithinAt f (f' x) (Icc (0 : ℝ) b) x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hd0.mono (fun y hy => hy.1)
    · exact (hd x ⟨h, hx.2⟩).hasDerivWithinAt
  have hbound : ∀ x ∈ Icc (0 : ℝ) b, ‖f' x‖ ≤ max C 0 :=
    fun x hx => le_trans (hC x hx) (le_max_left _ _)
  have h := (convex_Icc (0 : ℝ) b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound ⟨le_rfl, hb0.le⟩ hθ
  simpa [Real.norm_eq_abs, abs_of_nonneg hθ.1] using h

/-! **A derivative bound gives the variation bound, on the OPEN arc.**  This is why `h0`
is stated there: `ftFixedAngle` is differentiable on `Ioo 0 (π/r)` and nowhere else, so a
bound on `|Im((∂_t D)'/∂_t D)|` — `ArcPhaseBound`'s own shape, one region at a time —
reaches `κ₀` there and could not reach it on the closed arc. -/

export Shields (eVariationOn_le_of_abs_deriv_le)

/-- **`h0` from a derivative bound on the cofactor's logarithmic derivative.**  The last
weight-free input of `exists_uniform_ftBranchSupply`, reduced to the shape
`ArcPhaseBound` already produces for the amplitude. -/
theorem eVariationOn_ftFixedAngle_le {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {dS : ℝ → ℂ}
    {c₀ κ : ℝ} (hκ : 0 ≤ κ)
    (hSd : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt (ftCofactorAlong Q r z τ) (dS s) s)
    (hSc : ContinuousOn dS (Ioo (0 : ℝ) (π / r)))
    (hS0 : ∀ s ∈ Ioo (0 : ℝ) (π / r), ftCofactorAlong Q r z τ s ≠ 0)
    (hc₀ : c₀ ∈ Ioo (0 : ℝ) (π / r))
    (hbd : ∀ x ∈ Ioo (0 : ℝ) (π / r),
      |(dS x / ftCofactorAlong Q r z τ x).im| ≤ κ) :
    eVariationOn (ftFixedAngle Q r z τ dS c₀) (Ioo (0 : ℝ) (π / r))
      ≤ ENNReal.ofReal (κ * (π / r)) := by
  have h := eVariationOn_le_of_abs_deriv_le (a := 0) (b := π / r)
    (f := ftFixedAngle Q r z τ dS c₀)
    (f' := fun x => -(dS x / ftCofactorAlong Q r z τ x).im) hκ
    (fun x hx => hasDerivAt_ftFixedAngle isOpen_Ioo Set.ordConnected_Ioo hSd hSc hS0 hc₀ hx)
    (fun x hx => by rw [abs_neg]; exact hbd x hx)
  simpa using h

/-- **`κ₀`, from the cover.**  The last weight-free input of
`exists_uniform_ftBranchSupply`, produced from a bound on each of the three regions. -/
theorem exists_kappaZero_of_cover {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {dS : ℝ → ℂ} {c₀ b₁ b₂ C₁ C₂ C₃ : ℝ} (harc : (0 : ℝ) ≤ π / r)
    (hSd : ∀ s ∈ Ioo (0 : ℝ) (π / r),
      HasDerivAt (ftCofactorAlong Q r z τ) (dS s) s)
    (hSc : ContinuousOn dS (Ioo (0 : ℝ) (π / r)))
    (hS0 : ∀ s ∈ Ioo (0 : ℝ) (π / r), ftCofactorAlong Q r z τ s ≠ 0)
    (hc₀ : c₀ ∈ Ioo (0 : ℝ) (π / r))
    (hlo : ∀ θ ∈ Ioo (0 : ℝ) b₁, |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C₁)
    (hmid : ∀ θ ∈ Icc b₁ b₂, |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C₂)
    (hhi : ∀ θ ∈ Ioo b₂ (π / r), |(dS θ / ftCofactorAlong Q r z τ θ).im| ≤ C₃) :
    ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧
      eVariationOn (ftFixedAngle Q r z τ dS c₀) (Ioo (0 : ℝ) (π / r))
        ≤ ENNReal.ofReal κ₀ := by
  obtain ⟨κ, hκ0, hbd⟩ :=
    exists_bound_im_logDeriv_ftCofactorAlong_of_cover hlo hmid hhi
  exact ⟨κ * (π / r), mul_nonneg hκ0 harc,
    eVariationOn_ftFixedAngle_le hκ0 hSd hSc hS0 hc₀ hbd⟩

theorem ftFixedAngle_of_zero_deriv (Q : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (c₀ : ℝ) :
    ftFixedAngle Q r z τ 0 c₀
      = fun _ => -(Complex.log (ftCofactorAlong Q r z τ c₀)).im := by
  funext θ
  simp [ftFixedAngle, polarAngle, logLift]

theorem eVariationOn_ftFixedAngle_of_zero_deriv (Q : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ)
    (c₀ : ℝ) (s : Set ℝ) : eVariationOn (ftFixedAngle Q r z τ 0 c₀) s = 0 := by
  refine eVariationOn.constant_on ?_
  rw [ftFixedAngle_of_zero_deriv]
  rintro x ⟨a, -, rfl⟩ y ⟨b, -, rfl⟩
  rfl

theorem ftCofactorAlong_X_zero (r : ℕ) :
    ftCofactorAlong Polynomial.X r (fun _ => 0) (fun _ => 0) = fun _ => (1 : ℂ) := by
  funext θ
  have hden : ftDen (Polynomial.X : Polynomial ℂ) r 0 = Polynomial.X := by simp [ftDen]
  have hroot : (ftDen (Polynomial.X : Polynomial ℂ) r 0).eval 0 = 0 := by rw [hden]; simp
  have hprin : ftPrincipal (fun _ => (0 : ℝ)) θ = 0 := by simp [ftPrincipal]
  rw [ftCofactorAlong, hprin]
  have : (((0 : ℝ) : ℂ)) = 0 := by norm_num
  rw [this, ← eval_derivative_ftDen hroot, hden]
  simp

/-- **The weight-free bundle is satisfiable.**  `Q = X`, `z = 0`, `τ = 0` collapses the
cofactor along the arc to the constant `1`, so `dS = 0`, `κ₀ = 0`, and every hypothesis
of `exists_uniform_ftBranchSupply` that carries `κ₀` holds.  Not a statement about the
paper's pencil — a check that the bundle is not a vacuous strengthening. -/
theorem kappaZero_bundle_witness (r : ℕ) (c₀ : ℝ) :
    (∀ s ∈ Ioo (0 : ℝ) (π / r),
        HasDerivAt (ftCofactorAlong Polynomial.X r (fun _ => 0) (fun _ => 0)) ((0 : ℝ → ℂ) s) s)
      ∧ ContinuousOn (0 : ℝ → ℂ) (Ioo (0 : ℝ) (π / r))
      ∧ (∀ s ∈ Ioo (0 : ℝ) (π / r),
          ftCofactorAlong Polynomial.X r (fun _ => 0) (fun _ => 0) s ≠ 0)
      ∧ eVariationOn (ftFixedAngle Polynomial.X r (fun _ => 0) (fun _ => 0) 0 c₀)
          (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal 0 := by
  refine ⟨fun s _ => ?_, continuousOn_const, fun s _ => ?_, ?_⟩
  · rw [ftCofactorAlong_X_zero]
    simpa using hasDerivAt_const s (1 : ℂ)
  · rw [ftCofactorAlong_X_zero]; exact one_ne_zero
  · rw [eVariationOn_ftFixedAngle_of_zero_deriv]; exact zero_le

/-- **`κ₀` and `κ₁` bound ahead of `∀ B`.**  `eq:linear-phase-variation`'s uniformity is
that its two constants are constants of the pencil and the arc, not of the weight;
`AngularDiscrepancyFT.ftAngularDiscrepancy_of_supply` reads them off in that order, and
`thm:main` clause 3 is exactly what a `B`-dependent `κ₀` would cost.

Every hypothesis of the branch supply that carries a constant is discharged **before**
`B` is introduced: `h0` is about `ftFixedAngle`, `hKvar` about the tangent's own angle,
and neither mentions the weight.  The weight-dependent hypotheses — the amplitude's
derivative data, the three region bounds, the root states — are bound after it, where
they belong. -/
theorem exists_uniform_ftBranchSupply
    {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {dS dγ d2γ : ℝ → ℂ}
    {c₀ κ₀ Kγ : ℝ}
    (_harc : (0 : ℝ) < π / r)
    (hγd : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt (ftPrincipal τ) (dγ s) s)
    (hd2 : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt dγ (d2γ s) s)
    (hc2 : ContinuousOn d2γ (Ioo (0 : ℝ) (π / r)))
    (hreg : ∀ s ∈ Ioo (0 : ℝ) (π / r), dγ s ≠ 0)
    (hKγ : 0 ≤ Kγ)
    (hKvar : ∀ c ∈ Ioo (0 : ℝ) (π / r),
      eVariationOn (polarAngle dγ d2γ 0 c) (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal Kγ)
    (hSd : ∀ s ∈ Ioo (0 : ℝ) (π / r), HasDerivAt (ftCofactorAlong Q r z τ) (dS s) s)
    (hSc : ContinuousOn dS (Ioo (0 : ℝ) (π / r)))
    (hS0 : ∀ s ∈ Ioo (0 : ℝ) (π / r), ftCofactorAlong Q r z τ s ≠ 0)
    (hc₀ : c₀ ∈ Ioo (0 : ℝ) (π / r)) (hκ₀ : 0 ≤ κ₀)
    (h0 : eVariationOn (ftFixedAngle Q r z τ dS c₀) (Ioo (0 : ℝ) (π / r))
      ≤ ENNReal.ofReal κ₀) :
    ∃ κ₀' κ₁' : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧
      ∀ B : Polynomial ℂ, B ≠ 0 → ∀ (U : Set ℝ) (dW : ℝ → ℂ) (b₁ b₂ c₁ c₂ c₃ : ℝ),
        IsOpen U → Ioo (0 : ℝ) (π / r) ⊆ U →
        (∀ s ∈ U,
          HasDerivAt (fun x => ftAmp Q B r ((z x : ℝ) : ℂ) (ftPrincipal τ x)) (dW s) s) →
        ContinuousOn dW U →
        (∀ s ∈ Ioc (0 : ℝ) b₁, ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
          |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₁) →
        (∀ s ∈ Icc b₁ b₂, ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
          |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₂) →
        (∀ s ∈ Ico b₂ (π / r), ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s) ≠ 0 →
          |(dW s / ftAmp Q B r ((z s : ℝ) : ℂ) (ftPrincipal τ s)).im| ≤ c₃) →
        (∀ (a' b' : ℝ), a' ≤ b' → Icc a' b' ⊆ Ioo (0 : ℝ) (π / r) →
          ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
          (∀ i, Lb i ∈ Icc a' b') → (∀ i, Rb i ∈ Icc a' b') →
          (∀ i j, i < j → Rb i ≤ Lb j) →
          (∀ i, ∀ θ ∈ Icc (Lb i) (Rb i),
            ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
          ∀ β ∈ B.roots, ∃ ψ : Fin k → ℝ → ℝ,
            RootBranchState (ftPrincipal τ) dγ d2γ β a' b' Lb Rb ψ) →
        ∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
          (∀ i, Lb i ∈ Icc (0 : ℝ) (π / r)) → (∀ i, Rb i ∈ Icc (0 : ℝ) (π / r)) →
          (∀ i j, i < j → Rb i ≤ Lb j) →
          (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / r)) →
          (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
            ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) →
          ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
              ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
                = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ)
                  * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
            (∀ i, 0 ≤ varψ i) ∧
            (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
            ∑ i, varψ i ≤ κ₀' + κ₁' * B.natDegree :=
  ⟨κ₀, Kγ + π, hκ₀, by linarith [Real.pi_pos],
    fun B hB0 U dW b₁ b₂ c₁ c₂ c₃ hU hsub hWd hWc h₁ h₂ h₃ hstates =>
      exists_ftBranchSupply_of_rootStates hB0 hU hsub hWd hWc h₁ h₂ h₃
        hγd hd2 hc2 hreg hKvar hSd hSc hS0 hc₀ hκ₀ hKγ h0 hstates⟩

end ForgacsTran
