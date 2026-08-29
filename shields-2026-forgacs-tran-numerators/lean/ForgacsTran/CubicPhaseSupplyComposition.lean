/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.DominanceSupplyClosure
import ForgacsTran.CubicBranchBridge
import ForgacsTran.CubicWitnessInterior
import ForgacsTran.PencilIndex

/-!
# `FTPhaseSupply` at a named pencil, end to end

The producer table is a claim; the composition is the check.  Every hypothesis of
`PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` now has a named supplier,
but naming one per hypothesis shows something *shaped like* a supplier exists, not
that they compose.  This module composes them at a pencil with nothing abstract
left in it.

The pencil is `Q = (1-t)^3` with `r = 1` and `B = 3t^2 + 1`.  It is admissible:
`n = 3` clears `thm:FT-geometry`'s exclusion of `(deg Q, r) = (2,1)`, the smallest
zero is `x₁ = 1` with fiber `ρ = 3 ≥ 2`, so it lands in the `ρ ≥ 2, r = 1` cell of
the corner grid.  `CubicBranchBridge.ftRootPoly_one_eq_cubicQ` identifies
`ftRootPoly 1 ![1,1,1]` with `cubicQ`, so the conclusion really is about that
pencil and not merely about something of its shape.

**Why not the semicircle.**  `SimpleWitness`'s pencil has `RootBranchState`
already inhabited, which is the scarcer input — but it is `deg Q = 2` with
`r = 1`, exactly the case `thm:FT-geometry` excludes, so it does not satisfy the
binders of any cell of the dominance grid and cannot reach `FTPhaseSupply` by this
route at all.  That is a fact about the paper's hypotheses, not about the tree.

## What this shows, and what it does not

`hbranch` is the **only** hypothesis left, and it is left explicit.  Everything
else — the pencil's coefficients, the band, the geometry group, `hband`, and
`eq:dominance-bound` across the retained range — is discharged, at a named `Q`,
`r` and `B`.

It does **not** show `hbranch` is satisfiable here.  `RootBranchState` is
inhabited at the semicircle and not at this pencil, and the three region bounds on
`|Im(W'/W)|` are not built for this `B` either.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `subsec:proof`,
  `cor:linear-phase-variation`.

## Tags

phase supply, composition, witness, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

theorem cubicPencil_ha : ∀ k, 0 < (![1, 1, 1] : Fin 3 → ℝ) k := by
  intro k; fin_cases k <;> norm_num

theorem cubicPencil_hmin : ∀ k, (1 : ℝ) ≤ (![1, 1, 1] : Fin 3 → ℝ) k := by
  intro k; fin_cases k <;> norm_num

/-- The smallest zero has full fiber: all three zeros of `(1-t)^3` are `1`. -/
theorem cubicPencil_hcard :
    (Finset.univ.filter fun k => (![1, 1, 1] : Fin 3 → ℝ) k = 1).card = 3 := by
  have hall : (Finset.univ.filter fun k => (![1, 1, 1] : Fin 3 → ℝ) k = 1)
      = Finset.univ := by
    refine Finset.filter_true_of_mem fun k _ => ?_
    fin_cases k <;> norm_num
  rw [hall]
  simp

/-- **`FTPhaseSupply` at `Q = (1-t)^3`, `r = 1`, `B = 3t^2 + 1`, with `hbranch`
the only hypothesis.**

Nothing here is abstract: the pencil, the numerator and the index are named, and
every other hypothesis of the producer is discharged through the `ρ ≥ 2, r = 1`
cell of the dominance grid. -/
theorem cubic_ftPhaseSupply_of_branchSupply {κ₀ κ₁ : ℝ}
    (hbranch : ∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc 0 (π / ((1 : ℕ) : ℝ))) →
      (∀ i, Rb i ∈ Icc 0 (π / ((1 : ℕ) : ℝ))) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ))) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp (ftRootPoly 1 ![1, 1, 1]) witB 1
          ((ftBranchZLower ![1, 1, 1] 1 1 2 θ : ℝ) : ℂ)
          (ftPrincipal (ftTauArc ![1, 1, 1] 1 2 1) θ) ≠ 0) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          ftAmp (ftRootPoly 1 ![1, 1, 1]) witB 1
            ((ftBranchZLower ![1, 1, 1] 1 1 2 θ : ℝ) : ℂ)
            (ftPrincipal (ftTauArc ![1, 1, 1] 1 2 1) θ)
            = ((ftPrincipalAmp (ftRootPoly 1 ![1, 1, 1]) witB 1
                (ftBranchZLower ![1, 1, 1] 1 1 2)
                (ftTauArc ![1, 1, 1] 1 2 1) θ : ℝ) : ℂ)
              * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀ + κ₁ * witB.natDegree) :
    ∃ hcol : ℝ, 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply (ftRootPoly 1 ![1, 1, 1]) witB 1
        (ftBranchZLower ![1, 1, 1] 1 1 2) (ftTauArc ![1, 1, 1] 1 2 1) hcol κ₀ κ₁ M :=
  exists_ftPhaseSupply_at_branch_one_of_branchSupply (n := 3) (ρ := 3)
    (a := ![1, 1, 1]) (c := 1) (x₁ := 1) (by omega) cubicPencil_ha one_pos one_pos
    cubicPencil_hmin cubicPencil_hcard (by omega) witB hasRealCoeffs_witB
    (by rw [witB_eval]; norm_num) hbranch

/-- The same conclusion read at `cubicQ` rather than at `ftRootPoly 1 ![1,1,1]`,
so that the pencil the statement is about is the one `CubicWitness` names. -/
theorem cubic_ftPhaseSupply_pencil_eq :
    ftRootPoly 1 ![1, 1, 1] = cubicQ := ftRootPoly_one_eq_cubicQ

/-! ### The `ftTauArc` / `cubicTau` bridge, and where it stops

Two lanes need the cubic's derivative machinery — which is stated for `cubicTau` —
at `ftTauArc ![1,1,1] 1 2 1`.  On the **open** arc the two are the same function,
so everything transfers.  At the **upper endpoint** they are not, and that is not
a matter of spelling. -/

/-- **The bridge on the open arc.**  `ftTauArc` is `ftTauLower` below `π/r`,
`ftTauLower` is `ftTau` above `0`, and `cubicTau_eq_ftTau` identifies that with
the witness branch.  So anything proved of `cubicTau` on `(0,π)` holds of
`ftTauArc ![1,1,1] 1 2 1` verbatim. -/
theorem ftTauArc_eq_cubicTau_of_mem {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    ftTauArc ![1, 1, 1] 1 2 1 θ = cubicTau θ := by
  have h1 : θ < π / ((1 : ℕ) : ℝ) := by rw [pi_div_natCast_one]; exact hθ.2
  rw [ftTauArc_agree ![1, 1, 1] 1 2 1 hθ.1 h1]
  exact (cubicTau_eq_ftTau hθ).symm

/-- They agree at the **lower** endpoint too: `ftTauArc` is `x₁ = 1` there and
`cubicTau 0 = 1`. -/
theorem ftTauArc_eq_cubicTau_zero : ftTauArc ![1, 1, 1] 1 2 1 0 = cubicTau 0 := by
  have hlt : (0 : ℝ) < π / ((1 : ℕ) : ℝ) := by rw [pi_div_natCast_one]; exact pi_pos
  rw [ftTauArc_eq_lower _ _ _ _ hlt, ftTauLower, if_neg (lt_irrefl 0), cubicTau_zero]

/-- **`τ ≥ 1/2` on the open arc**, from the closed form: `cos ψ ≤ 1`. -/
theorem half_le_ftTauArc_cubic {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) π) :
    1 / 2 ≤ ftTauArc ![1, 1, 1] 1 2 1 θ := by
  rw [ftTauArc_eq_cubicTau_of_mem hθ,
    cubicTau_closed_form ⟨hθ.1.le, hθ.2.le⟩]
  have hc : 0 < Real.cos ((π - θ) / 3) := cos_third_pos ⟨hθ.1.le, hθ.2.le⟩
  have hle : Real.cos ((π - θ) / 3) ≤ 1 := Real.cos_le_one _
  have h2 : (0 : ℝ) < 2 * Real.cos ((π - θ) / 3) := by linarith
  have := one_div_le_one_div_of_le h2 (by linarith : 2 * Real.cos ((π - θ) / 3) ≤ 2)
  simpa using this

/-- **The bridge FAILS at the upper endpoint, and the gap is not small.**
`ftTauArc` is defined to be `0` at and beyond `π/r`, which is the upper endpoint's
limit when the branch runs into the origin — the `r ≥ 2` picture.  At `r = 1` the
upper endpoint is **finite**: `cubicTau π = 1/2`. -/
theorem ftTauArc_ne_cubicTau_pi : ftTauArc ![1, 1, 1] 1 2 1 π ≠ cubicTau π := by
  have h0 : ftTauArc ![1, 1, 1] 1 2 1 π = 0 := by
    have hπ : (π : ℝ) = π / ((1 : ℕ) : ℝ) := by push_cast; ring
    rw [hπ]
    exact ftTauArc_arc_end _ _ _ _
  rw [h0, cubicTau_pi]
  norm_num

/-- **Hence `ftTauArc` is discontinuous at the upper endpoint at this pencil.**  It
is at least `1/2` throughout `(0,π)` and `0` at `π`.

This is a fact about `ftTauArc` at `r = 1`, not about the cubic: the definition
extends by the origin, which is the upper endpoint's limit only when `2 ≤ r`.  Any
hypothesis asking for `τ` — or `ftPrincipal τ` — to be continuous, let alone
differentiable, on a neighbourhood of the **closed** arc is therefore unsatisfiable
at every `r = 1` pencil with this `τ`.  `BranchSupply`'s `hγd`, `hd2` and `hc2` ask
exactly that, on an open `Uγ ⊇ Icc 0 (π/r)`. -/
theorem not_continuousAt_ftTauArc_cubic_pi :
    ¬ ContinuousAt (ftTauArc ![1, 1, 1] 1 2 1) π := by
  intro hcont
  have hval : ftTauArc ![1, 1, 1] 1 2 1 π = 0 := by
    have hπ : (π : ℝ) = π / ((1 : ℕ) : ℝ) := by push_cast; ring
    rw [hπ]; exact ftTauArc_arc_end _ _ _ _
  have hmem : Ioo (0 : ℝ) π ∈ nhdsWithin π (Iio π) := by
    refine Filter.mem_of_superset
      (Filter.inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds pi_pos))
        (self_mem_nhdsWithin (a := π) (s := Iio π))) ?_
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx1, hx2⟩
  have htend : Filter.Tendsto (ftTauArc ![1, 1, 1] 1 2 1) (nhdsWithin π (Iio π))
      (nhds (ftTauArc ![1, 1, 1] 1 2 1 π)) := hcont.continuousWithinAt.tendsto
  have hle : (1 : ℝ) / 2 ≤ ftTauArc ![1, 1, 1] 1 2 1 π := by
    refine ge_of_tendsto htend ?_
    filter_upwards [hmem] with x hx using half_le_ftTauArc_cubic hx
  rw [hval] at hle
  norm_num at hle

end ForgacsTran
