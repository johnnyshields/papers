/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.AngularBookkeeping
import ForgacsTran.PhaseCount

/-!
# `eq:angular-distinct-lower`, summed across the retained blocks

`PhaseCount.exists_interiorZeros_of_dominance` counts on **one** component of
`Ω_M ∩ (α,β)`.  `subsec:proof` sums those counts, and the arithmetic of that sum
is what this module carries: no analysis, only the bookkeeping that turns
per-block counts into `((M+1)/π)(β-α) - C₀ - C₁K`.

**The summation of the phase variation is the trap here, and it is made
structural rather than warned about.**  `hvar` below bounds `∑ᵢ Var_ℐᵢ ψ` — one
number for the whole family — and there is no way to feed the theorem a
per-component cap instead.  That is deliberate: a family of `J+1` components each
bounded by `κ₀ + κ₁ deg B` sums to `(J+1)(κ₀ + κ₁ deg B)`, and with `J ≤ deg B`
that is **quadratic** in `deg B`, which destroys exactly the numerator-uniformity
`thm:main` clause 3 exists to state.  `cor:linear-phase-variation` is not a
per-component cap; `PhaseVariation.linear_phase_variation_components_regular`
bounds the summed variation over an ordered family directly, and
`Shields.eVariationOn_finsetSum_le` is what makes the refinement to a finer family
cost nothing.

## Main statements

* `angular_count_lower_of_components` — the sum itself: per-block counts, the
  retained length, and one bound on the summed variation.
* `angular_count_lower_uniform` — the same with the deleted length and the
  variation priced, producing `C₀ + C₁K` with **neither constant seeing `B`**.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and
proof of the main theorem» (`subsec:proof`, `eq:Omega-M`,
`eq:angular-distinct-lower`).

## Tags

angular discrepancy, zero counting, numerator uniformity
-/

namespace ForgacsTran

open Real

/-- **The per-block counts summed.**  Each retained block contributes at least
`(M+1)|ℐ|/π - Var_ℐψ/π - 2`; adding them turns the block lengths into the retained
length and the block variations into their sum.

`hvar` takes the **summed** variation.  A per-component cap cannot be substituted:
that is the quadratic-in-`deg B` route, and it is excluded by the shape of the
binder rather than by a comment. -/
theorem angular_count_lower_of_components {k : ℕ} {n : Fin k → ℕ}
    {len varψ : Fin k → ℝ} {M : ℕ} {α β deleted V : ℝ}
    (hn : ∀ i, ((M : ℝ) + 1) * len i / π - varψ i / π - 2 ≤ (n i : ℝ))
    (hlen : β - α - deleted ≤ ∑ i, len i)
    (hvar : ∑ i, varψ i ≤ V) :
    ((M : ℝ) + 1) * (β - α) / π - (((M : ℝ) + 1) * deleted + V) / π - 2 * k
      ≤ ∑ i, (n i : ℝ) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hM : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have hsum : ∑ i, (((M : ℝ) + 1) * len i / π - varψ i / π - 2) ≤ ∑ i, (n i : ℝ) :=
    Finset.sum_le_sum fun i _ => hn i
  refine le_trans ?_ hsum
  have hexp : ∑ i, (((M : ℝ) + 1) * len i / π - varψ i / π - 2)
      = ((M : ℝ) + 1) * (∑ i, len i) / π - (∑ i, varψ i) / π - 2 * k := by
    have hpt : ∀ i : Fin k, ((M : ℝ) + 1) * len i / π - varψ i / π - 2
        = (((M : ℝ) + 1) / π) * len i - (1 / π) * varψ i - 2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    try ring
  rw [hexp]
  have h1 : ((M : ℝ) + 1) * (β - α - deleted) / π
      ≤ ((M : ℝ) + 1) * (∑ i, len i) / π := by
    gcongr
  have h2 : (∑ i, varψ i) / π ≤ V / π := by gcongr
  have h3 : ((M : ℝ) + 1) * (β - α - deleted) / π
      = ((M : ℝ) + 1) * (β - α) / π - (((M : ℝ) + 1) * deleted) / π := by
    field_simp
  have h4 : (((M : ℝ) + 1) * deleted + V) / π
      = (((M : ℝ) + 1) * deleted) / π + V / π := by ring
  rw [h4]
  linarith [h1, h2, h3]

/-- **`eq:angular-distinct-lower` with the correction priced.**  The deleted
length is the endpoint collar `2h/M` plus the amplitude windows, and
`eq:amplitude-window-negligible` (`AngularBookkeeping.eventually_deletedLength_le_one`)
caps the windows' contribution at `1` however heavy `B` is.  With `J ≤ K` blocks
and the summed variation at `κ₀ + κ₁K`, the whole correction is

  `C₀ + C₁K`,   `C₀ = (4h + 1 + κ₀)/π + 2`,   `C₁ = κ₁/π + 2`.

**This lemma does not by itself carry the uniformity, and should not be read as
if it did.**  `h`, `κ₀` and `κ₁` are parameters here, so nothing stops a caller
instantiating them at quantities that see `B`; the statement stays true and says
less.  What makes `C₀` and `C₁` independent of `B` is *where they are built* — `h`
from `thm:weighted-dominance` and `κ₀`, `κ₁` from `cor:linear-phase-variation`,
all constants of `Q` and `r` — and that is discharged at the producer of
`ConsequencesComposition.FTAngularDiscrepancy`, whose binder order (`C₀`, `C₁`
before `∀ B`; `M₀` after) is the actual claim.  What this lemma contributes is
that the correction assembles into the shape `C₀ + C₁K` at all, with `K`
appearing only as a multiplier.

**Containment.**  The conclusion relates the zero count to `deg B`; no hypothesis
mentions both.  `hn` sees only one block, `hlen` and `hwin` only lengths, `hvar`
only the variation, `hk` only the block count. -/
theorem angular_count_lower_uniform {k : ℕ} {n : Fin k → ℕ}
    {len varψ : Fin k → ℝ} {M K : ℕ} {α β h κ₀ κ₁ collar windows : ℝ}
    (hh : 0 ≤ h) (hM : 1 ≤ M)
    (hn : ∀ i, ((M : ℝ) + 1) * len i / π - varψ i / π - 2 ≤ (n i : ℝ))
    (hlen : β - α - (collar + windows) ≤ ∑ i, len i)
    (hcollar : collar ≤ 2 * h / M) (_hwinnn : 0 ≤ windows)
    (hwin : ((M : ℝ) + 1) * windows ≤ 1)
    (hvar : ∑ i, varψ i ≤ κ₀ + κ₁ * K)
    (hk : (k : ℝ) ≤ (K : ℝ) + 1) :
    ((M : ℝ) + 1) * (β - α) / π - ((4 * h + 1 + κ₀) / π + 2)
        - (κ₁ / π + 2) * K
      ≤ ∑ i, (n i : ℝ) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le one_pos hMR
  have hbase := angular_count_lower_of_components (n := n) (len := len) (varψ := varψ)
    (α := α) (β := β) (deleted := collar + windows) (V := κ₀ + κ₁ * K) hn hlen hvar
  refine le_trans ?_ hbase
  -- the collar: `(M+1)·2h/M ≤ 4h` once `M ≥ 1`
  have hcol : ((M : ℝ) + 1) * collar ≤ 4 * h := by
    have hstep : ((M : ℝ) + 1) * collar ≤ ((M : ℝ) + 1) * (2 * h / M) := by
      gcongr
    refine le_trans hstep ?_
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hMpos]
    nlinarith [hh, hMR]
  have hdel : ((M : ℝ) + 1) * (collar + windows) + (κ₀ + κ₁ * K)
      ≤ 4 * h + 1 + κ₀ + κ₁ * K := by
    have : ((M : ℝ) + 1) * (collar + windows)
        = ((M : ℝ) + 1) * collar + ((M : ℝ) + 1) * windows := by ring
    rw [this]; linarith
  have hdiv : (((M : ℝ) + 1) * (collar + windows) + (κ₀ + κ₁ * K)) / π
      ≤ (4 * h + 1 + κ₀ + κ₁ * K) / π := by gcongr
  have hkR : 2 * (k : ℝ) ≤ 2 * ((K : ℝ) + 1) := by linarith
  have hsplit : (4 * h + 1 + κ₀ + κ₁ * K) / π
      = (4 * h + 1 + κ₀) / π + (κ₁ / π) * K := by field_simp
  linarith [hdiv, hkR, hsplit]


/-! ### The blocks add rather than overlap

`PhaseCount.exists_interiorZeros_of_dominance` returns a `Finset` of distinct
roots per retained block.  Turning `∑ᵢ nᵢ` into a single count needs those sets to
be pairwise disjoint, and they are — for a reason that is geometric and not
combinatorial: the blocks are disjoint angular sets, `z` is injective across the
arc, so the windows `z(ℐᵢ)` are pairwise disjoint and a root cannot be produced
by two blocks.

This is the second place the "sum, don't multiply" discipline has to hold.  The
first was the phase variation; here the failure would be the opposite direction —
counting one root twice and *overstating* the total — and it is excluded by
`hdisj`, which is about the windows rather than about the root sets, so a caller
cannot satisfy it by accident. -/

/-- **The per-block root sets add.**  Distinct roots supplied on pairwise disjoint
windows are distinct from each other, so their counts sum to a lower bound for the
multiplicity-counted number of roots in any window containing them all. -/
theorem sum_card_le_count_filter {P : Polynomial ℂ} (hP : P ≠ 0) (W : Set ℂ)
    [DecidablePred (· ∈ W)] {k : ℕ} {Z : Fin k → Finset ℂ} {A : Fin k → Set ℂ}
    (hroot : ∀ i, ∀ w ∈ Z i, P.IsRoot w)
    (hmem : ∀ i, ∀ w ∈ Z i, w ∈ A i)
    (hsub : ∀ i, A i ⊆ W)
    (hdisj : ∀ i j, i ≠ j → ∀ w ∈ A i, w ∉ A j) :
    ∑ i, (Z i).card ≤ Multiset.card (P.roots.filter (· ∈ W)) := by
  classical
  have hpd : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j → Disjoint (Z i) (Z j) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 fun w hwi hwj => ?_
    exact hdisj i j hij w (hmem i w hwi) (hmem j w hwj)
  have hcard : (Finset.univ.biUnion Z).card = ∑ i, (Z i).card := Finset.card_biUnion hpd
  rw [← hcard]
  refine card_le_count_filter hP W (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.1 hw
    exact hroot i w hwi
  · obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.1 hw
    exact hsub i (hmem i w hwi)

/-- The same over `ℝ`, chained with the per-block counts, which is the form
`angular_count_lower_of_components` hands on. -/
theorem sum_count_le_count_filter {P : Polynomial ℂ} (hP : P ≠ 0) (W : Set ℂ)
    [DecidablePred (· ∈ W)] {k : ℕ} {n : Fin k → ℕ} {Z : Fin k → Finset ℂ}
    {A : Fin k → Set ℂ}
    (hn : ∀ i, n i ≤ (Z i).card)
    (hroot : ∀ i, ∀ w ∈ Z i, P.IsRoot w)
    (hmem : ∀ i, ∀ w ∈ Z i, w ∈ A i)
    (hsub : ∀ i, A i ⊆ W)
    (hdisj : ∀ i j, i ≠ j → ∀ w ∈ A i, w ∉ A j) :
    ∑ i, (n i : ℝ) ≤ (Multiset.card (P.roots.filter (· ∈ W)) : ℝ) := by
  have hnat : ∑ i, n i ≤ Multiset.card (P.roots.filter (· ∈ W)) :=
    le_trans (Finset.sum_le_sum fun i _ => hn i)
      (sum_card_le_count_filter hP W hroot hmem hsub hdisj)
  calc ∑ i, (n i : ℝ) = ((∑ i, n i : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (Multiset.card (P.roots.filter (· ∈ W)) : ℝ) := by exact_mod_cast hnat

/-- **`eq:angular-distinct-lower` as a statement about the window count.**  The
summation of `angular_count_lower_of_components` composed with the disjointness:
the multiplicity-counted zeros of `F_M` inside the window are at least the uniform
prediction less `C₀ + C₁K`. -/
theorem angular_window_count_lower {P : Polynomial ℂ} (hP : P ≠ 0) (W : Set ℂ)
    [DecidablePred (· ∈ W)] {k : ℕ} {n : Fin k → ℕ} {Z : Fin k → Finset ℂ}
    {A : Fin k → Set ℂ} {len varψ : Fin k → ℝ} {M K : ℕ}
    {α β h κ₀ κ₁ collar windows : ℝ}
    (hh : 0 ≤ h) (hM : 1 ≤ M)
    (hcount : ∀ i, ((M : ℝ) + 1) * len i / π - varψ i / π - 2 ≤ (n i : ℝ))
    (hlen : β - α - (collar + windows) ≤ ∑ i, len i)
    (hcollar : collar ≤ 2 * h / M) (hwinnn : 0 ≤ windows)
    (hwin : ((M : ℝ) + 1) * windows ≤ 1)
    (hvar : ∑ i, varψ i ≤ κ₀ + κ₁ * K)
    (hk : (k : ℝ) ≤ (K : ℝ) + 1)
    (hn : ∀ i, n i ≤ (Z i).card)
    (hroot : ∀ i, ∀ w ∈ Z i, P.IsRoot w)
    (hmem : ∀ i, ∀ w ∈ Z i, w ∈ A i)
    (hsub : ∀ i, A i ⊆ W)
    (hdisj : ∀ i j, i ≠ j → ∀ w ∈ A i, w ∉ A j) :
    ((M : ℝ) + 1) * (β - α) / π - ((4 * h + 1 + κ₀) / π + 2) - (κ₁ / π + 2) * K
      ≤ (Multiset.card (P.roots.filter (· ∈ W)) : ℝ) :=
  le_trans
    (angular_count_lower_uniform hh hM hcount hlen hcollar hwinnn hwin hvar hk)
    (sum_count_le_count_filter hP W hn hroot hmem hsub hdisj)


/-! ### The upper half, by complementation

`subsec:proof` gets the upper bound from the lower one: apply
`eq:angular-distinct-lower` to the two complementary angular intervals `(0,α)` and
`(β,π/r)`, and the distinct zeros they supply are zeros of `F_M` that the window
does not contain.  `count_add_card_le_natDegree` then caps the window's
own count against the degree.

The geometric input is that the complementary windows really are disjoint from the
inner one — `ConsequencesComposition.notMem_ftWindow`, which is injectivity of `z`
and nothing else.  Without it the complementary zeros could be the same zeros
counted again and the bound would be vacuous. -/

/-- **The window count capped by the degree.**  Distinct zeros outside the window
crowd out zeros inside it. -/
theorem angular_window_count_upper {P : Polynomial ℂ} (hP : P ≠ 0) (W : Set ℂ)
    [DecidablePred (· ∈ W)] {Zout : Finset ℂ} {D lower : ℝ}
    (hout : ∀ w ∈ Zout, P.IsRoot w) (hdisj : ∀ w ∈ Zout, w ∉ W)
    (hdeg : (P.natDegree : ℝ) ≤ D) (hlow : lower ≤ (Zout.card : ℝ)) :
    (Multiset.card (P.roots.filter (· ∈ W)) : ℝ) ≤ D - lower := by
  classical
  have hnat := count_add_card_le_natDegree hP W hout hdisj
  have hR : (Multiset.card (P.roots.filter (· ∈ W)) : ℝ) + (Zout.card : ℝ)
      ≤ (P.natDegree : ℝ) := by exact_mod_cast hnat
  linarith

/-- **`eq:angular-discrepancy`.**  A two-sided bound of the shape
`FTAngularDiscrepancy` asks for, from the lower bound on the window and the upper
bound complementation produces.  Both halves are stated at the *same* constants,
which is what lets the absolute value close. -/
theorem abs_angular_discrepancy_le {x t C₀ C₁ : ℝ} {K : ℕ}
    (hlow : t - C₀ - C₁ * K ≤ x) (hup : x ≤ t + C₀ + C₁ * K) :
    |x - t| ≤ C₀ + C₁ * K := by
  rw [abs_le]
  constructor <;> linarith

/-- The two halves at possibly different constants, reconciled by taking the
larger of each.  A lower bound proved with `C₀, C₁` and an upper bound proved with
`D₀, D₁` give the discrepancy at `max C₀ D₀`, `max C₁ D₁` — which is still a pair
of constants seeing whatever `C` and `D` see and nothing more, so the uniformity
survives the reconciliation. -/
theorem abs_angular_discrepancy_le_max {x t C₀ C₁ D₀ D₁ : ℝ} {K : ℕ}
    (hK : (0 : ℝ) ≤ K)
    (hlow : t - C₀ - C₁ * K ≤ x) (hup : x ≤ t + D₀ + D₁ * K) :
    |x - t| ≤ max C₀ D₀ + max C₁ D₁ * K := by
  refine abs_angular_discrepancy_le ?_ ?_
  · have h1 : C₀ ≤ max C₀ D₀ := le_max_left _ _
    have h2 : C₁ * K ≤ max C₁ D₁ * K :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hK
    linarith
  · have h1 : D₀ ≤ max C₀ D₀ := le_max_right _ _
    have h2 : D₁ * K ≤ max C₁ D₁ * K :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hK
    linarith


/-- **`J ≤ K` from `eq:amplitude-zero-count`, checked rather than assumed.**
`InteriorSupply.ftAmplitudeDivisor_count` bounds the **multiplicity sum**
`∑_j ν_j` by `deg B`, and the block count needs the number of **distinct** divisor
angles.  The two agree only because every `ν_j ≥ 1`; at a divisor point of
multiplicity two the sum is strictly larger than the count, so reading one off the
other is a step and not a rewording.

This is what feeds `hk : (k : ℝ) ≤ K + 1` through
`AngularBookkeeping.card_blocks_le`. -/
theorem card_le_of_one_le_sum {S : Finset ℝ} {ν : ℝ → ℕ} {D : ℕ}
    (hν : ∀ θj ∈ S, 1 ≤ ν θj) (hsum : ∑ θj ∈ S, ν θj ≤ D) : S.card ≤ D := by
  calc S.card = ∑ _θj ∈ S, 1 := by simp
    _ ≤ ∑ θj ∈ S, ν θj := Finset.sum_le_sum hν
    _ ≤ D := hsum

end ForgacsTran
