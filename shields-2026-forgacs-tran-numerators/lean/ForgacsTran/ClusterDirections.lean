/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Cluster

/-!
# The cluster directions

The `ρ` members of an endpoint cluster sit at the `ρ`-th roots of **unity**.
These are `clusterDir`, and they are a different family from
`Cluster.clusterOmega`, whose `ρ`-th power is `-1`: the bridge between them is
`clusterAlpha_mul_clusterDir`, an identity rather than a matching.

Nothing here mentions an endpoint, a chart or the pencil.  The roots of unity
were first needed at the lower endpoint, where a chart labels the cluster by
`ρ`-th roots of its own choosing; `EndpointUpperPackage` consumes the same facts
at the *upper* endpoint, where no chart is built at all.

The second half is the statement that `j ↦ ζ^j` factors through `ZMod ρ`, which
is what lets the manuscript's label `(j + ρ - j_p) \bmod ρ` be read off a chart
index.

## Main statements

* `clusterDir` — the `j`-th `ρ`-th root of unity.
* `clusterAlpha_mul_clusterDir` — the `ρ` cluster directions carry `clusterAlpha`
  onto itself, so the family of slopes is the orbit of the principal one.
* `clusterOmega_inj` — the cluster directions are distinct.
* `clusterSlope_shift` — a chart's member `j` has slope `α_{(j + ρ - j_p) mod ρ}`,
  not `α_j`.

## References

* `shields-2026-forgacs-tran-numerators.tex`, `eq:lower-cluster-expansion`.

## Tags

roots of unity, cluster directions, index arithmetic
-/

namespace ForgacsTran

open Polynomial Complex Filter Topology

/-- The `j`-th `ρ`-th root of unity, the direction of the `j`-th cluster member in
the chart variable. -/
noncomputable def clusterDir (ρ j : ℕ) : ℂ :=
  (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (ρ : ℂ))) ^ j

theorem clusterDir_pow {ρ : ℕ} (hρ : ρ ≠ 0) (j : ℕ) : (clusterDir ρ j) ^ ρ = 1 := by
  rw [clusterDir, ← pow_mul, mul_comm j ρ, pow_mul,
    (Complex.isPrimitiveRoot_exp ρ hρ).pow_eq_one, one_pow]

theorem clusterDir_ne_zero (ρ j : ℕ) : clusterDir ρ j ≠ 0 :=
  pow_ne_zero _ (Complex.exp_ne_zero _)

theorem clusterDir_inj {ρ : ℕ} (hρ : ρ ≠ 0) {i j : ℕ} (hi : i < ρ) (hj : j < ρ)
    (h : clusterDir ρ i = clusterDir ρ j) : i = j :=
  (Complex.isPrimitiveRoot_exp ρ hρ).pow_inj hi hj h

/-- The cluster directions rotate the chart directions: `ω_0·ζ_j = ω_j`. -/
theorem clusterOmega_mul_clusterDir {ρ : ℕ} (hρ : ρ ≠ 0) (j : ℕ) :
    clusterOmega ρ 0 * clusterDir ρ j = clusterOmega ρ j := by
  have hρC : ((ρ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hρ
  have hdir : clusterDir ρ j
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (ρ : ℂ)) := by
    rw [clusterDir, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [clusterOmega, clusterOmega, hdir, ← Complex.exp_add]
  congr 1
  rw [clusterAngle, clusterAngle]
  push_cast
  field

/-- **The cluster directions are distinct.**  `ω` is `ω_0` times a chart direction,
so the indices separate exactly as the chart's do.  This is what carries
`idx₀ i ≠ 0, 1` — an arithmetic fact about the enumeration — over to
`ω_{idx₀ i} ≠ ω_0, ω_1`, which is what `Geometry.endpoint_linear_coeff_pos`
asks for. -/
theorem clusterOmega_inj {ρ : ℕ} (hρ : ρ ≠ 0) {i j : ℕ} (hi : i < ρ) (hj : j < ρ)
    (h : clusterOmega ρ i = clusterOmega ρ j) : i = j := by
  have h0 : clusterOmega ρ 0 ≠ 0 := by
    rw [clusterOmega]; exact Complex.exp_ne_zero _
  rw [← clusterOmega_mul_clusterDir hρ i, ← clusterOmega_mul_clusterDir hρ j] at h
  exact clusterDir_inj hρ hi hj (mul_left_cancel₀ h0 h)

/-- `ω_1 = e^{iπ/ρ}` and `ω_0 = e^{-iπ/ρ}`, in the spelling
`Geometry.endpoint_linear_coeff_pos` takes. -/
theorem clusterOmega_one_eq {ρ : ℕ} :
    clusterOmega ρ 1 = Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * Complex.I) := by
  rw [clusterOmega, clusterAngle]
  push_cast
  ring_nf

theorem clusterOmega_zero_eq {ρ : ℕ} :
    clusterOmega ρ 0 = Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * Complex.I) := by
  rw [clusterOmega, clusterAngle]
  push_cast
  ring_nf

/-- **The orbit identity.**  The `ρ` cluster directions carry `clusterAlpha` onto
itself: `α_0·ζ_j = α_j`.  This is what pins the enumeration index — the family of
slopes is the orbit of the principal one, so no asymptotic has to be matched
against an index by hand. -/
theorem clusterAlpha_mul_clusterDir (x₁ : ℝ) {ρ : ℕ} (hρ : ρ ≠ 0) (j : ℕ) :
    clusterAlpha x₁ ρ 0 * clusterDir ρ j = clusterAlpha x₁ ρ j := by
  have hρC : ((ρ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hρ
  have hdir : clusterDir ρ j
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (ρ : ℂ)) := by
    rw [clusterDir, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  have homega : clusterOmega ρ 0 * clusterDir ρ j = clusterOmega ρ j := by
    rw [clusterOmega, clusterOmega, hdir, ← Complex.exp_add]
    congr 1
    rw [clusterAngle, clusterAngle]
    push_cast
    field
  rw [clusterAlpha, clusterAlpha, ← homega]
  ring


/-! ### The index arithmetic -/

/-- The chart directions add in the exponent. -/
theorem clusterDir_add (ρ a b : ℕ) :
    clusterDir ρ (a + b) = clusterDir ρ a * clusterDir ρ b := by
  rw [clusterDir, clusterDir, clusterDir, pow_add]

theorem clusterDir_self {ρ : ℕ} (hρ : ρ ≠ 0) : clusterDir ρ ρ = 1 := by
  have h := clusterDir_pow hρ 1
  rw [clusterDir, pow_one] at h
  rw [clusterDir]
  exact h

theorem clusterDir_mul_left {ρ : ℕ} (hρ : ρ ≠ 0) (k : ℕ) : clusterDir ρ (ρ * k) = 1 := by
  have h : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (ρ : ℂ))) ^ ρ = 1 :=
    clusterDir_self hρ
  rw [clusterDir, pow_mul, h, one_pow]

/-- The chart directions are periodic in the index, since `ζ^ρ = 1`.  This is what
lets a chart index be reduced mod `ρ`, and it is the whole content of the shift
between a chart's own labelling of the cluster and the manuscript's. -/
theorem clusterDir_mod {ρ : ℕ} (hρ : ρ ≠ 0) (m : ℕ) :
    clusterDir ρ (m % ρ) = clusterDir ρ m := by
  conv_rhs => rw [← Nat.div_add_mod m ρ]
  rw [clusterDir_add, clusterDir_mul_left hρ, one_mul]

/-- **The manuscript's index of a chart member.**  A chart labels the cluster by
`ρ`-th roots of unity of its own choosing, and there is no reason for its index
`0` to be the principal branch: if the principal branch is the chart's `j_p`, the
chart's member `j` has slope `α_{(j + ρ - j_p) \bmod ρ}`, not `α_j`.

Identifying the two labellings is a wrong statement of the residue asymptotics at
every member at once, and it is invisible to the binders that only ask for an
injection into a set of the right size.  `scripts/check_cluster_slope_set.py`
checks the fact this rests on — that the slope set is exactly the `α` set — at
four pencils. -/
theorem clusterSlope_shift {ρ : ℕ} (hρ : ρ ≠ 0) {γe : ℂ} {L : ℝ} {x₁ : ℝ} {jp : ℕ}
    (hjp : jp ≤ ρ) (hAp : γe * (clusterDir ρ jp * ((L : ℝ) : ℂ)) = clusterAlpha x₁ ρ 0)
    (j : ℕ) :
    γe * (clusterDir ρ j * ((L : ℝ) : ℂ)) = clusterAlpha x₁ ρ ((j + ρ - jp) % ρ) := by
  have hsplit : j + ρ - jp = j + (ρ - jp) := by omega
  have hone : clusterDir ρ jp * clusterDir ρ (ρ - jp) = 1 := by
    rw [← clusterDir_add, Nat.add_sub_cancel' hjp, clusterDir_self hρ]
  rw [← clusterAlpha_mul_clusterDir x₁ hρ, clusterDir_mod hρ, hsplit, clusterDir_add,
    ← hAp]
  linear_combination (-(γe * clusterDir ρ j * ((L : ℝ) : ℂ))) * hone

end ForgacsTran
