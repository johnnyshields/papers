/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperPackage

/-!
# The retained cluster, and the upper residue ratio

The vocabulary both endpoint blocks are stated in, and the one limit the upper
block's residue group rests on.
`EndpointUpperGap.exists_upper_endpoint_block` is where the latter is consumed and
is the only place the upper binders are stated: it produces the retained-set group,
the cluster group and the residue group **against one enumeration**, which is what
a consumer needs.

This module used to also carry those groups as two separate theorems, each opening
its own existential over the enumeration.  Nothing identified the two, so a
consumer pairing the cardinality constraints of one with the value constraints of
the other type-checked and built green — the "which index" failure with the index
question moved out to *which cluster*.  Both were strictly weaker than the block
that replaced them, so they were removed rather than documented around.

`RetainedCluster` is the other half of that same concern.  The two endpoint blocks
each returned the same eleven-clause conjunction, spelled out in full and named
nowhere, so the fields had names in the prose (`hroot₀`, `hginj₁`, …) and none in
the Lean.  Naming the conjunction is definitionally transparent — a caller still
destructures it with `obtain` — and it is what makes the two blocks visibly the
same statement at two different angles rather than two long formulas that happen
to agree.

## Main statements

* `ClusterEnumeration` — the members left when the principal pair is erased.
* `RetainedCluster` — the retained cluster at one angle: the radius, the zero set
  inside the separating circle, the principal pair, and the enumeration of what is
  left after the pair is erased.
* `eventually_of_window` — a window `(0, e]` as an eventual statement along `0⁺`.
* `tendsto_upper_amp_ratio` — `𝒜(g)/𝒜(t_+) → μ` for two zeros colliding at the
  origin.  At the upper endpoint the amplitude ratio is a ratio of *normalized
  roots*: `𝒜 = -tB(t)/E(t)` at a nonzero simple zero, and neither `B` nor
  `E = XQ' - rQ` vanishes at the origin — `B(0) ≠ 0` by hypothesis and
  `E(0) = -rQ(0) ≠ 0` — so the two nonlinear factors tend to `1` and only `g/t_+`
  survives.  Its limit is an `r`-th root of unity, whose modulus is `1`; that is
  `hL₁`.

  Stating this at `clusterAlpha` instead would not be a mislabelling but the wrong
  object, and it would be *unsatisfiable* rather than false: `∂_tD ≍ 1/τ` diverges
  here.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:upper-residue-ratio`.

## Tags

upper endpoint, residue ratio, normalized root, weighted dominance
-/
namespace ForgacsTran

open Complex Filter Topology Polynomial
open scoped Topology

/-- A window `(0, e]` as an eventual statement along `0⁺`. -/
theorem eventually_of_window {p : ℝ → Prop} {e : ℝ} (he : 0 < e)
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ e → p δ) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), p δ := by
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT he] with δ hδ hδe
  exact h δ hδ (le_of_lt hδe.2)

/-! ### The retained cluster at one angle

`thm:weighted-dominance` reads its endpoint data off a separating circle: inside it
sit the principal point `t_+ = τe^{iθ}`, its conjugate, and the members that are
retained after those two are erased.  Eleven facts say so, and both endpoint blocks
return all eleven — `EndpointLowerBlock.exists_lower_endpoint_block` at the angle
`δ` and the radius `ftSepRadius`, `EndpointUpperGap.exists_upper_endpoint_block` at
the angle `π/r - δ` and a radius the upper circle supplies.

They are the same eleven, and the difference between the two endpoints is entirely
in what is substituted for `zf`, `τf`, `θ`, `R` and `τmax`. -/

/-- **The enumeration of what is left when the principal pair is erased.**  `g`
lists the members of `S` other than `p` and `q`, once each and all of them: it is
injective, it lands in the doubly-erased set, and that set has exactly `m`
elements.

The three clauses are `hginj`, `hgmem` and `hgcard` in the prose of both endpoint
blocks, and all three constrain the map's *cardinality* rather than its values —
which is why a consumer that obtains them from a different existential than the one
supplying the residue asymptotics type-checks and still describes the wrong points.
That is the "which index" failure, and it is why the blocks return this alongside
the cluster rather than separately. -/
def ClusterEnumeration (S : Finset ℂ) (p q : ℂ) {m : ℕ} (g : Fin m → ℂ) : Prop :=
  Function.Injective g
  ∧ (∀ i : Fin m, g i ∈ (S.erase p).erase q)
  ∧ ((S.erase p).erase q).card = m

/-- **The retained cluster of `thm:weighted-dominance`, at one angle.**  With `zf`
the spectral parameter, `τf` the branch radius, `θ` the angle, `R` the separating
radius and `τmax` the bound the contour ratio is taken against:

* the radius is positive and at most `τmax`;
* `S` is exactly the zero set of the pencil in the closed disk of radius `R`, every
  member simple and strictly inside;
* the principal point is one of those zeros, and is not its own conjugate;
* `g` enumerates the retained members — `S` with the principal pair erased —
  injectively and exhaustively.

The conjugate point is written out as `τ(θ)e^{-iθ}` rather than as
`starRingEnd ℂ (ftPrincipal τf θ)`: the two agree, but only the first is a
*hypothesis* about the radius, and the erasure below has to match what the blocks'
own callers erase.

`m` is the retained count — `ρ - 2` below the arc and `r - 2` above it — and it is
the last clause, not a hypothesis, so a caller learns the count from the block
rather than having to supply it. -/
def RetainedCluster (Q : Polynomial ℂ) (r : ℕ) (zf τf : ℝ → ℝ) (θ : ℝ)
    (R τmax : ℝ) (S : Finset ℂ) {m : ℕ} (g : Fin m → ℂ) : Prop :=
  0 < τf θ
  ∧ τf θ ≤ τmax
  ∧ (∀ t ∈ S, (ftDen Q r ((zf θ : ℝ) : ℂ)).eval t = 0)
  ∧ (∀ t ∈ S, (Polynomial.derivative (ftDen Q r ((zf θ : ℝ) : ℂ))).eval t ≠ 0)
  ∧ (∀ t ∈ S, ‖t‖ < R)
  ∧ (∀ t : ℂ, ‖t‖ ≤ R → (ftDen Q r ((zf θ : ℝ) : ℂ)).eval t = 0 → t ∈ S)
  ∧ (ftDen Q r ((zf θ : ℝ) : ℂ)).eval (ftPrincipal τf θ) = 0
  ∧ ftPrincipal τf θ ≠ ((τf θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)
  ∧ ClusterEnumeration S (ftPrincipal τf θ)
      (((τf θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) g

/-! ### `hratio₁` and `hL₁`: the upper residue ratio

At the upper endpoint the amplitude ratio is a ratio of *normalized roots*, not the
lower endpoint's cluster ratio through `clusterAlpha`.  `𝒜 = -tB(t)/E(t)` at a
nonzero simple zero, and both `B` and `E = XQ' - rQ` are nonvanishing at the origin
— `B(0) ≠ 0` by hypothesis and `E(0) = -rQ(0) ≠ 0` — so the two nonlinear factors
tend to `1` and only `g/t_+` survives.  Its limit is an `r`-th root of unity, whose
modulus is `1`; that is `hL₁`.

Stating this at `clusterAlpha` instead would not be a mislabelling but the wrong
object, and it would be *unsatisfiable* rather than false: `∂_tD ≍ 1/τ` diverges
here. -/

/-- **The amplitude ratio along two colliding zeros.**  `𝒜(g)/𝒜(t_+) → μ` whenever
`g/t_+ → μ` and both run into the origin, because the amplitude's other two factors
are continuous and nonzero there. -/
theorem tendsto_upper_amp_ratio {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.eval 0 ≠ 0) (hB0 : B.eval 0 ≠ 0)
    {g p zf : ℝ → ℂ} {μ : ℂ}
    (hp0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), p δ ≠ 0)
    (hg0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), g δ ≠ 0)
    (hproot : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ftDen Q r (zf δ)).eval (p δ) = 0)
    (hgroot : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ftDen Q r (zf δ)).eval (g δ) = 0)
    (hptend : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgtend : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hq : Tendsto (fun δ => g δ / p δ) (𝓝[>] (0 : ℝ)) (𝓝 μ)) :
    Tendsto (fun δ => ftAmp Q B r (zf δ) (g δ) / ftAmp Q B r (zf δ) (p δ))
      (𝓝[>] (0 : ℝ)) (𝓝 μ) := by
  have hE0 : (ftCritical Q r).eval 0 ≠ 0 := eval_ftCritical_zero_ne_zero hr hQ0
  -- the two continuous factors
  have hBg : Tendsto (fun δ => B.eval (g δ)) (𝓝[>] (0 : ℝ)) (𝓝 (B.eval 0)) :=
    ((B.continuous_aeval).tendsto 0).comp hgtend
  have hBp : Tendsto (fun δ => B.eval (p δ)) (𝓝[>] (0 : ℝ)) (𝓝 (B.eval 0)) :=
    ((B.continuous_aeval).tendsto 0).comp hptend
  have hEg : Tendsto (fun δ => (ftCritical Q r).eval (g δ)) (𝓝[>] (0 : ℝ))
      (𝓝 ((ftCritical Q r).eval 0)) :=
    (((ftCritical Q r).continuous_aeval).tendsto 0).comp hgtend
  have hEp : Tendsto (fun δ => (ftCritical Q r).eval (p δ)) (𝓝[>] (0 : ℝ))
      (𝓝 ((ftCritical Q r).eval 0)) :=
    (((ftCritical Q r).continuous_aeval).tendsto 0).comp hptend
  have hBratio : Tendsto (fun δ => B.eval (g δ) / B.eval (p δ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have := hBg.div hBp hB0
    rwa [div_self hB0] at this
  have hEratio : Tendsto (fun δ => (ftCritical Q r).eval (p δ)
      / (ftCritical Q r).eval (g δ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have := hEp.div hEg hE0
    rwa [div_self hE0] at this
  have hprod := (hq.mul hBratio).mul hEratio
  rw [mul_one, mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [hp0, hg0, hproot, hgroot, hBp.eventually_ne hB0, hEg.eventually_ne hE0,
    hEp.eventually_ne hE0] with δ hpne hgne hpr hgr hBpne hEgne hEpne
  rw [ftAmp_eq_ftCritical hr hgne hgr, ftAmp_eq_ftCritical hr hpne hpr]
  field_simp

end ForgacsTran
