/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.CubicWitness
import ForgacsTran.ConsequencesComposition

/-!
# The cubic witness's nonprincipal cluster

Builds the enumeration `weighted_dominance_of_branch`'s cluster binders take, at
the pencil `CubicWitness` fixes: `Q(t) = (1-t)^3`, `r = 1`.

This is a separate module rather than a third `_block` beside the two in
`CubicWitness` only because that file has another writer; nothing here depends on
being outside it.

**The nonprincipal cluster is a singleton, and that is the point of the pencil.**
`cubicRootSet` is `{t₊, conj t₊, 1/τ²}`, so erasing the principal
pair leaves one element and `n₀ = ρ - 2 = 1`.  At the quadratic pencil the
pair exhausts the zeros, `n₀ = 0`, and every cluster binder would hold
vacuously — which is why the witness is cubic.
`scripts/check_cubic_witness_cluster.py` confirms the count at the real objects
before any of this is built.

**Branch selection is not automatic here**; the reality condition
`2τ³cos θ = 3τ² - 1` has two positive roots for small `θ` and
only `τ < 1` is the Forgács--Tran branch.  That belongs in `CubicWitness`'s own
docstring and has been sent to its owner rather than written here.

## Implementation notes

Sorry-free.

## Tags

witness, cubic pencil, nonprincipal cluster, Vieta formulas
-/

namespace ForgacsTran

open Polynomial Complex

/-- The nonprincipal cluster member at the lower endpoint: the third denominator
zero `1/τ(δ)²`, which Vieta puts on the real axis because the three
zeros of `(1-t)^3 + zt` have product `1`. -/
noncomputable def cubicNonprincipal (δ : ℝ) : Fin 1 → ℂ :=
  fun _ => ((cubicThird δ : ℝ) : ℂ)

/-- The third zero is neither member of the principal pair, by modulus:
`τ < 1/τ²` on the arc. -/
theorem cubicThird_ne_principal {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 Real.pi) :
    ((cubicThird δ : ℝ) : ℂ)
      ≠ ((cubicTau δ : ℝ) : ℂ) * Complex.exp (((δ : ℝ) : ℂ) * Complex.I) := by
  intro h
  have hgap : cubicTau δ < cubicThird δ := cubicTau_lt_cubicThird hδ
  have h1 : ‖((cubicThird δ : ℝ) : ℂ)‖ = cubicThird δ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_trans (cubicTau_pos δ) hgap)]
  have h2 : ‖((cubicTau δ : ℝ) : ℂ) * Complex.exp (((δ : ℝ) : ℂ) * Complex.I)‖
      = cubicTau δ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (cubicTau_pos δ)]
  rw [← h1, h, h2] at hgap
  exact lt_irrefl _ hgap

theorem cubicThird_ne_principal_conj {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 Real.pi) :
    ((cubicThird δ : ℝ) : ℂ)
      ≠ (starRingEnd ℂ) (((cubicTau δ : ℝ) : ℂ)
          * Complex.exp (((δ : ℝ) : ℂ) * Complex.I)) := by
  intro h
  have hgap : cubicTau δ < cubicThird δ := cubicTau_lt_cubicThird hδ
  have h1 : ‖((cubicThird δ : ℝ) : ℂ)‖ = cubicThird δ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_trans (cubicTau_pos δ) hgap)]
  have h2 : ‖(starRingEnd ℂ) (((cubicTau δ : ℝ) : ℂ)
      * Complex.exp (((δ : ℝ) : ℂ) * Complex.I))‖ = cubicTau δ := by
    rw [RCLike.norm_conj, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cubicTau_pos δ)]
  rw [← h1, h, h2] at hgap
  exact lt_irrefl _ hgap

/-- **The nonprincipal cluster, as a `Finset`.**  Erasing the principal pair from
the retained set leaves exactly the third zero. -/
theorem cubicRootSet_erase_pair {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 Real.pi) :
    ((cubicRootSet δ).erase
        (((cubicTau δ : ℝ) : ℂ) * Complex.exp (((δ : ℝ) : ℂ) * Complex.I))).erase
      ((starRingEnd ℂ) (((cubicTau δ : ℝ) : ℂ)
        * Complex.exp (((δ : ℝ) : ℂ) * Complex.I)))
      = {((cubicThird δ : ℝ) : ℂ)} := by
  classical
  ext w
  simp only [Finset.mem_erase, cubicRootSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hp, h | h | h⟩
    · exact absurd h hp
    · exact absurd h hc
    · exact h
  · rintro rfl
    exact ⟨cubicThird_ne_principal_conj hδ, cubicThird_ne_principal hδ, by tauto⟩

/-- **`hginj₀`, `hgmem₀` and `hgcard₀` at the witness, as one block.**  The
nonprincipal cluster is enumerated by `cubicNonprincipal` over `Fin 1`, and
`n₀ = 1` is *derived* from the retained set rather than posited — which is what
makes the cluster binders non-vacuous here.

The remaining cluster binder, `hexp₀`, is not in this block: at this pencil its
content is `|1/τ(δ)³ - 1 - √3·δ| ≤ C·δ²`, since the
third zero is `1/τ²` and the cluster direction is `ω₂ = -1`, giving
`(cos(π/3) - Re ω₂)/sin(π/3) = √3`.
`scripts/check_cubic_witness_cluster.py` measures that limit and finds it, to
`1.732051` monotonically. -/
theorem cubicWitness_nonprincipalCluster_block :
    ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ < Real.pi ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (cubicNonprincipal δ)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i : Fin 1, cubicNonprincipal δ i ∈
        ((cubicRootSet δ).erase
            (((cubicTau δ : ℝ) : ℂ) * Complex.exp (((δ : ℝ) : ℂ) * Complex.I))).erase
          ((starRingEnd ℂ) (((cubicTau δ : ℝ) : ℂ)
            * Complex.exp (((δ : ℝ) : ℂ) * Complex.I)))) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
        (((cubicRootSet δ).erase
            (((cubicTau δ : ℝ) : ℂ) * Complex.exp (((δ : ℝ) : ℂ) * Complex.I))).erase
          ((starRingEnd ℂ) (((cubicTau δ : ℝ) : ℂ)
            * Complex.exp (((δ : ℝ) : ℂ) * Complex.I)))).card = 1) := by
  refine ⟨Real.pi / 2, by positivity, by linarith [Real.pi_pos], ?_, ?_, ?_⟩
  · intro δ _ _ i j _
    exact Subsingleton.elim i j
  · intro δ hδ hδe i
    have hmem : δ ∈ Set.Ioo 0 Real.pi := ⟨hδ, by linarith [Real.pi_pos]⟩
    rw [cubicRootSet_erase_pair hmem, cubicNonprincipal]
    exact Finset.mem_singleton_self _
  · intro δ hδ hδe
    have hmem : δ ∈ Set.Ioo 0 Real.pi := ⟨hδ, by linarith [Real.pi_pos]⟩
    rw [cubicRootSet_erase_pair hmem, Finset.card_singleton]

/-! ### `hexp₀`'s content at this pencil

`cubicTau_closed_form` makes the whole binder elementary.  The nonprincipal zero
is `1/τ²`, so the normalized quantity `hexp₀` bounds is
`(1/τ²)/τ = 1/τ³`, and the closed form turns that into

`1/τ(δ)³ = 8cos³((π - δ)/3)`,

an explicit smooth function of `δ` alone.  The cluster direction at the
nonprincipal index is `ω₂ = -1`, so `eq:endpoint-linear-gap`'s coefficient
is `(cos(π/3) - (-1))/sin(π/3) = √3` — and `hexp₀` is a second-order
Taylor bound on that function at `0`, nothing more.

`scripts/check_cubic_witness_cluster.py` measures the residual ratio and finds it
rising to `5/6`; the constant proved here is `3`, from `|f''| ≤ 8/3` over the whole arc.  `2`
is *false*: `f'' = (8/3)·c·(2 - 3c²)` with `c = cos((π - δ)/3)`, which
reaches `-8/3` at `c = 1`, i.e. at `δ = π`.  Near the endpoint itself
`f''(0) = 5/3` and the sharp constant is `5/6`, which is what the script
measures — the gap is the price of a bound valid on the whole arc rather than a
window. -/

/-- `1/τ³` at the cubic witness, as an explicit function of the angle.
Written as a product rather than a power: `HasDerivAt.pow` lands in a different
`AddCommGroup` instance than the rest of the chain, and the products compose
without that friction. -/
noncomputable def cubicClusterRatio (δ : ℝ) : ℝ :=
  8 * (Real.cos ((Real.pi - δ) / 3) * Real.cos ((Real.pi - δ) / 3)
    * Real.cos ((Real.pi - δ) / 3))

/-- Its derivative. -/
noncomputable def cubicClusterRatioDeriv (δ : ℝ) : ℝ :=
  8 * (Real.cos ((Real.pi - δ) / 3) * Real.cos ((Real.pi - δ) / 3)
    * Real.sin ((Real.pi - δ) / 3))

/-- And its second derivative. -/
noncomputable def cubicClusterRatioDeriv2 (δ : ℝ) : ℝ :=
  8 / 3 * (Real.cos ((Real.pi - δ) / 3)
    * (2 * (Real.sin ((Real.pi - δ) / 3) * Real.sin ((Real.pi - δ) / 3))
      - Real.cos ((Real.pi - δ) / 3) * Real.cos ((Real.pi - δ) / 3)))

private theorem hasDerivAt_shift (δ : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.pi - s) / 3) (-(1 / 3)) δ := by
  have h : HasDerivAt (fun s : ℝ => Real.pi - s) (-1) δ := by
    simpa using (hasDerivAt_id δ).const_sub Real.pi
  exact (h.div_const 3).congr_deriv (by norm_num)

private theorem hasDerivAt_ccos (δ : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos ((Real.pi - s) / 3))
      (Real.sin ((Real.pi - δ) / 3) / 3) δ :=
  (((Real.hasDerivAt_cos _).comp δ (hasDerivAt_shift δ))).congr_deriv (by ring)

private theorem hasDerivAt_csin (δ : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin ((Real.pi - s) / 3))
      (-(Real.cos ((Real.pi - δ) / 3) / 3)) δ :=
  (((Real.hasDerivAt_sin _).comp δ (hasDerivAt_shift δ))).congr_deriv (by ring)

/-! ### Two normalizer traps in the derivative and limit plumbing

Both cost a rewritten block, and in both the thing a reader tries first does not
work.

**`HasDerivAt.mul` on lambdas leaves `((fun s => …) * fun s => …) δ`** rather
than a product of values, so `ring` cannot see it.  `simp only [Pi.mul_apply]`
before `ring` fixes it, and that is why the `congr_deriv` blocks below carry it.

**`Filter.Tendsto.div` leaves `Pi.div` rather than a pointwise quotient, and
`simp` cannot reach it** — it sits inside the *function argument* of a `Tendsto`,
where simp does not rewrite.  **Adding `Pi.div_apply` to the simp set does
nothing**, which is the natural thing to try and the reason this note exists.
What works is `have h := …; rw […] at h; exact h`, relying on `f / g` and
`fun x => f x / g x` being definitionally equal.  **The `.mul` fix does not
transfer**, and assuming it does is what cost the rewrite.

A third of the same kind: `(Complex.continuous_ofReal.tendsto _).comp f` yields
`ofReal ∘ f` where the goal wants `fun δ => ↑(f δ)`.  There `Function.comp_def`
in the `simpa` is enough, because the mismatch is in the term rather than under
a binder simp will not enter. -/

theorem hasDerivAt_cubicClusterRatio (δ : ℝ) :
    HasDerivAt cubicClusterRatio (cubicClusterRatioDeriv δ) δ := by
  have hc := hasDerivAt_ccos δ
  exact (((hc.mul hc).mul hc).const_mul 8).congr_deriv (by
    rw [cubicClusterRatioDeriv]; simp only [Pi.mul_apply]; ring)

theorem hasDerivAt_cubicClusterRatioDeriv (δ : ℝ) :
    HasDerivAt cubicClusterRatioDeriv (cubicClusterRatioDeriv2 δ) δ := by
  have hc := hasDerivAt_ccos δ
  have hs := hasDerivAt_csin δ
  exact (((hc.mul hc).mul hs).const_mul 8).congr_deriv (by
    rw [cubicClusterRatioDeriv2]; simp only [Pi.mul_apply]; ring)

/-- The second derivative is bounded by `8/3` outright, since `cos ≤ 1/2` on
the arc's image and the bracket never exceeds `2` in modulus. -/
theorem abs_cubicClusterRatioDeriv2_le {δ : ℝ} (hδ : δ ∈ Set.Icc 0 Real.pi) :
    |cubicClusterRatioDeriv2 δ| ≤ 3 := by
  set u : ℝ := (Real.pi - δ) / 3 with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith [hδ.2]
  have huπ : u ≤ Real.pi / 3 := by rw [hu]; linarith [hδ.1]
  have hcos_le : Real.cos u ≤ 1 := Real.cos_le_one u
  have hcos_ge : (1 : ℝ) / 2 ≤ Real.cos u := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hu0 (by linarith [Real.pi_pos]) huπ
  have hsin2 : Real.sin u ^ 2 = 1 - Real.cos u ^ 2 := by
    have := Real.sin_sq_add_cos_sq u; linarith
  have hc2 : Real.cos u ^ 2 ≤ 1 := by nlinarith
  have hc2' : (1 : ℝ) / 4 ≤ Real.cos u ^ 2 := by nlinarith
  rw [cubicClusterRatioDeriv2, ← hu, abs_le]
  constructor <;> nlinarith [hcos_ge, hcos_le, hc2, hc2']

/-- **`hexp₀`'s inequality at the cubic witness.**  A second-order Taylor bound on
`1/τ³` at the endpoint, with the linear coefficient `√3` that
`eq:endpoint-linear-gap` predicts from `ω₂ = -1`.

`phase_taylor_bound` does the work: the mean value theorem twice, once on the
derivative and once on the function minus its tangent — the same lemma the strong
clock's `htaylor` runs on, which is why no new analysis appears here. -/
theorem cubicCluster_taylor {e₀ : ℝ} (he₀ : 0 < e₀) (heπ : e₀ ≤ Real.pi)
    {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ e₀) :
    |cubicClusterRatio δ - cubicClusterRatio 0 - cubicClusterRatioDeriv 0 * δ|
      ≤ 3 * δ ^ 2 := by
  have hsub : Set.Icc (0 : ℝ) e₀ ⊆ Set.Icc (0 : ℝ) Real.pi :=
    Set.Icc_subset_Icc le_rfl heπ
  have h := phase_taylor_bound (ψ := cubicClusterRatio) (dψ := cubicClusterRatioDeriv)
    (ddψ := cubicClusterRatioDeriv2) (a := 0) (b := e₀) (κ₂ := 3)
    (fun θ _ => hasDerivAt_cubicClusterRatio θ)
    (fun θ _ => hasDerivAt_cubicClusterRatioDeriv θ)
    (fun θ hθ => abs_cubicClusterRatioDeriv2_le (hsub hθ))
    ⟨le_rfl, he₀.le⟩ ⟨hδ.le, hδe⟩ hδ.le
  simpa using h

/-- The endpoint values: `1/τ(0)³ = 1` and the linear coefficient is
`√3`, which is `(cos(π/3) - Re ω₂)/sin(π/3)` at `ω₂ = -1`. -/
theorem cubicClusterRatio_zero : cubicClusterRatio 0 = 1 := by
  rw [cubicClusterRatio]
  rw [show (Real.pi - 0) / 3 = Real.pi / 3 by ring, Real.cos_pi_div_three]
  norm_num

theorem cubicClusterRatioDeriv_zero : cubicClusterRatioDeriv 0 = Real.sqrt 3 := by
  rw [cubicClusterRatioDeriv]
  rw [show (Real.pi - 0) / 3 = Real.pi / 3 by ring, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  ring

/-! ### `hexp₀` in the binder's own shape, and the four binders together -/

/-- **The nonprincipal cluster direction at `ρ = 3` is `ω₂ = -1`.**  Proved, not
matched: `clusterAngle 3 2 = (2·2-1)π/3 = π`, so `ω₂ = e^{iπ} = -1`.

This is the index check the block depends on.  The principal directions are
`j = 1, 3`, both nonreal; if `idx₀` landed on one of those the coefficient would
be different and `hexp₀` would still be *true*, with the linear term wrong —
true and empty, which no build catches. -/
theorem clusterOmega_three_two : clusterOmega 3 2 = -1 := by
  rw [clusterOmega, clusterAngle]
  norm_num

/-- `eq:endpoint-linear-gap`'s coefficient at the witness is `√3`, which is
`cubicClusterRatioDeriv 0`. -/
theorem cubicCluster_coeff :
    ((((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) - clusterOmega 3 2)
        / ((Real.sin (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ))
      = ((Real.sqrt 3 : ℝ) : ℂ) := by
  rw [clusterOmega_three_two]
  norm_num
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    simp
  field_simp
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- `1/τ³` is the normalized nonprincipal zero: `(1/τ²)/τ`. -/
theorem cubicThird_div_cubicTau {δ : ℝ} (hδ : δ ∈ Set.Icc 0 Real.pi) :
    cubicThird δ / cubicTau δ = cubicClusterRatio δ := by
  have hc : (0 : ℝ) < Real.cos ((Real.pi - δ) / 3) := by
    have hw : (Real.pi - δ) / 3 ∈ Set.Icc 0 (Real.pi / 3) := by
      constructor <;> [linarith [hδ.2]; linarith [hδ.1]]
    have : (1 : ℝ) / 2 ≤ Real.cos ((Real.pi - δ) / 3) := by
      rw [← Real.cos_pi_div_three]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hw.1 (by linarith [Real.pi_pos]) hw.2
    linarith
  rw [cubicThird, cubicTau_closed_form hδ, cubicClusterRatio]
  field_simp
  ring

/-- **`hexp₀` at the witness, in the binder's own shape.**  The complex norm
reduces to the real absolute value because every quantity is real here: the
nonprincipal zero is `1/τ²`, `τ` is real, and `ω₂ = -1` makes the linear
coefficient `√3` real too.  So no complex-to-real transfer lemma is needed —
which is worth saying, because reaching for one would have been the natural
move. -/
theorem cubicCluster_hexp {e₀ : ℝ} (he₀ : 0 < e₀) (heπ : e₀ ≤ Real.pi)
    (i : Fin 1) {δ : ℝ} (hδ : 0 < δ) (hδe : δ ≤ e₀) :
    ‖cubicNonprincipal δ i / ((cubicTau δ : ℝ) : ℂ)
        - (1 + ((((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) - clusterOmega 3 2)
            / ((Real.sin (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ)) * ((δ : ℝ) : ℂ))‖
      ≤ 3 * δ ^ 2 := by
  have hmem : δ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hδ.le, le_trans hδe heπ⟩
  have hτ0 : ((cubicTau δ : ℝ) : ℂ) ≠ 0 := by
    simpa using (cubicTau_pos δ).ne'
  have hreal : cubicNonprincipal δ i / ((cubicTau δ : ℝ) : ℂ)
      - (1 + ((((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) - clusterOmega 3 2)
          / ((Real.sin (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ)) * ((δ : ℝ) : ℂ))
      = (((cubicClusterRatio δ - cubicClusterRatio 0
            - cubicClusterRatioDeriv 0 * δ : ℝ)) : ℂ) := by
    rw [cubicCluster_coeff, cubicNonprincipal, ← Complex.ofReal_div,
      cubicThird_div_cubicTau hmem, cubicClusterRatio_zero, cubicClusterRatioDeriv_zero]
    push_cast
    ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  exact cubicCluster_taylor he₀ heπ hδ hδe

/-- **All four cluster binders of `weighted_dominance_of_branch`, on one `e₀`.**
`hginj₀`, `hgmem₀`, `hgcard₀` and `hexp₀` together, at the cubic witness.

Four theorems on four windows prove four things; one theorem on one window
proves they hold *together*, which is the only form that answers joint
satisfiability.  The `e₀` is taken inside rather than left to the caller.

`n₀ = 1`, not `0`: the `hgcard₀` clause forces it, since a retained set with the
principal pair removed has one element and the enumeration is over `Fin 1`.  At
the quadratic pencil that clause would read `card = 0` and every other clause
would hold for nothing. -/
theorem cubicWitness_cluster_block :
    ∃ e₀ Cexp₀ : ℝ, 0 < e₀ ∧ e₀ < Real.pi ∧ 0 ≤ Cexp₀ ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (cubicNonprincipal δ)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i : Fin 1, cubicNonprincipal δ i ∈
        ((cubicRootSet δ).erase
            (((cubicTau δ : ℝ) : ℂ) * Complex.exp (((δ : ℝ) : ℂ) * Complex.I))).erase
          ((starRingEnd ℂ) (((cubicTau δ : ℝ) : ℂ)
            * Complex.exp (((δ : ℝ) : ℂ) * Complex.I)))) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
        (((cubicRootSet δ).erase
            (((cubicTau δ : ℝ) : ℂ) * Complex.exp (((δ : ℝ) : ℂ) * Complex.I))).erase
          ((starRingEnd ℂ) (((cubicTau δ : ℝ) : ℂ)
            * Complex.exp (((δ : ℝ) : ℂ) * Complex.I)))).card = 1) ∧
      (∀ i : Fin 1, ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
        ‖cubicNonprincipal δ i / ((cubicTau δ : ℝ) : ℂ)
            - (1 + ((((Real.cos (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ) - clusterOmega 3 2)
                / ((Real.sin (Real.pi / ((3 : ℕ) : ℝ)) : ℝ) : ℂ)) * ((δ : ℝ) : ℂ))‖
          ≤ Cexp₀ * δ ^ 2) := by
  obtain ⟨e₁, he₁, he₁π, hinj, hmem, hcard⟩ := cubicWitness_nonprincipalCluster_block
  refine ⟨e₁, 3, he₁, he₁π, by norm_num, hinj, hmem, hcard, ?_⟩
  intro i δ hδ hδe
  exact cubicCluster_hexp he₁ he₁π.le i hδ hδe

end ForgacsTran
