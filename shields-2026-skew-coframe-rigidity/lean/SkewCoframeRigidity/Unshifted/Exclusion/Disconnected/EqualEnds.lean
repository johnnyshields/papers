/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.EqL
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Congr
import SkewCoframeRigidity.Stationary.MatchingWiring

/-!
# Two end components with the same start are equal

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner, `A = B`).  The equation of the two components
holds at the generic letters; the substitution `H_L ↦ H_L + 1` fixes both complete coframes (they
read only the letters below `L`) and adds one to both top quotients, so the equation also holds at
the shifted series.  `eqL_consequence` then gives equal top quotients and the cap relation
`[Hδ]_{L+1} = δ_1 k`, and component rigidity for the one-cell cap identifies the coframes.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem map_letterSeries_shift (L : ℕ) (hL : 1 ≤ L) :
    PowerSeries.map (shiftField L 1) letterSeries =
      letterSeries + PowerSeries.C 1 * PowerSeries.X ^ L := by
  ext k
  rw [PowerSeries.coeff_map, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  unfold letterSeries seriesOf
  rw [PowerSeries.coeff_mk, shiftField_cohLetters]
  by_cases hk : k = L
  · subst hk; simp
  · simp [Function.update_of_ne hk, hk]

theorem coframe_shift_fixed (L : ℕ) (D : BetaDiagram (n + 1)) (hD : span D = L) :
    (coframe D).map (shiftField L 1) = coframe D := by
  have h1 := coframeOf_map (shiftField L 1) cohLetters D
  have h2 : (fun j => shiftField L 1 (cohLetters j)) = Function.update cohLetters L
      (cohLetters L + 1) := by
    funext j; rw [shiftField_cohLetters]; simp
  rw [h2] at h1
  have h3 := coframeOf_congr (h := Function.update cohLetters L (cohLetters L + 1))
    (h' := cohLetters) D (fun k hk => Function.update_of_ne (by omega) _ _)
  unfold coframe
  rw [← h1, h3]

theorem topQuotient_shift (L : ℕ) (hL : 1 ≤ L) (D : BetaDiagram (n + 1)) (hD : span D = L) :
    shiftField L 1 (topQuotient D) = topQuotient D + 1 := by
  have e : topQuotient D = PowerSeries.coeff L (letterSeries * (coframe D : PowerSeries CohField)) := by
    unfold topQuotient topQuotientOf; rw [hD]; rfl
  rw [e, ← PowerSeries.coeff_map, map_mul, map_letterSeries_shift L hL, ← Polynomial.polynomial_map_coe,
    coframe_shift_fixed L D hD]
  rw [add_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, Polynomial.coeff_coe,
    coframe_coeff_zero]
  simp

/-- Two connected diagrams of the same span `L ≥ 2` whose equation `eqL` holds at precision
`2L + 2` at the generic letters have equal complete coframes. -/
theorem equal_components (hcap : FixedCap.CapVanishing cellCap) {e e' : ℕ}
    (E : BetaDiagram (e + 1)) (F : BetaDiagram (e' + 1)) (hE : E.Connected) (hF : F.Connected)
    (hs : span E = span F) (hL : 2 ≤ span E) (q : ℕ)
    (e0 : ∀ m < 2 * span E + 2, PowerSeries.coeff m (eqL (span E) (q + 2) (coframe E) (coframe F)
      (topQuotient E) (topQuotient F) letterSeries) = 0) :
    coframe E = coframe F := by
  set L := span E with hLdef
  have e1 : ∀ m < 2 * L + 2, PowerSeries.coeff m (eqL L (q + 2) (coframe E) (coframe F)
      (topQuotient E + 1) (topQuotient F + 1) (letterSeries + PowerSeries.C 1 * PowerSeries.X ^ L))
      = 0 := by
    intro m hm
    have := congrArg (PowerSeries.coeff m) (eqL_map (shiftField L 1) L (q + 2) (coframe E)
      (coframe F) (topQuotient E) (topQuotient F) letterSeries)
    rw [PowerSeries.coeff_map, e0 m hm, map_zero, coframe_shift_fixed L E rfl,
      coframe_shift_fixed L F hs.symm, topQuotient_shift L (by omega) E rfl,
      topQuotient_shift L (by omega) F hs.symm, map_letterSeries_shift L (by omega)] at this
    exact this.symm
  obtain ⟨hkk, hrel⟩ := eqL_consequence L q hL (coframe E) (coframe F) (coframe_coeff_zero E)
    (coframe_coeff_zero F) (topQuotient E) (topQuotient F) cohLetters (cohLetters_ne_zero 0)
    e0 e1
  refine component_rigidity_of_cap hcap E F hE hF hs hL hkk ?_
  rw [Polynomial.coe_sub, mul_sub, map_sub, Polynomial.coeff_sub]
  change PowerSeries.coeff (L + 1) (seriesOf cohLetters * (coframe F : PowerSeries CohField)) -
    PowerSeries.coeff (L + 1) (seriesOf cohLetters * (coframe E : PowerSeries CohField)) =
      ((coframe F).coeff 1 - (coframe E).coeff 1) * topQuotient E
  linear_combination -hrel

end SkewCoframeRigidity.Unshifted
