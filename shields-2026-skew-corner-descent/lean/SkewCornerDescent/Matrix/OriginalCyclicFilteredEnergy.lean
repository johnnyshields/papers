/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCyclicCrossSelfCharge
import SkewCornerDescent.Matrix.OriginalClosurePhaseLaurentEnergy
import SkewCornerDescent.CyclicProfilePhaseCharge

/-!
# Actual full cyclic filtered profile energy

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
For explicit incoming-profile discrepancy data and a resolving margin, the
genuine ordinary closure charge is its weighted attaining-phase half-square
sum. Exactly invariant phases cancel as whole polynomials, and negative
Laurent offsets vanish without truncation. No energy identity is an input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete actual closure charge is exactly the weighted energy of
phases attaining the resolving margin. An exactly invariant incoming phase
contributes zero as a whole polynomial, including every negative offset. -/
theorem originalClosure_filtered_cross_self_charge {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b r d : ℕ) [NeZero b] [NeZero r]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hshort : d * r < originalSelectedCount (hD := hD) P)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P))) (J : ℕ+) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    let C := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    let f := fun (i : Fin r) (k : ZMod b) =>
      (C (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1
    let K := fun i : Fin r => ((c.top : ℤ) + c.originalCompletedGap P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
    ∀ W : Fin r → Option ℕ,
    (∀ i, match W i with
      | none => ∀ k, f i k = f i (k + (d : ZMod b))
      | some w => 0 < w ∧ 2 * w < K i ∧
          (∀ k l, l < w → (f i k).coeff l = (f i (k + (d : ZMod b))).coeff l) ∧
          (K i : ℤ) - 2 * (w : ℤ) ≤ (J : ℤ)) →
    c.originalCrossPrefixCharge Q (d * r) J (originalSelectedCount (hD := hD) P) (by omega) -
      c.originalSelfPrefixCharge Q J (originalSelectedCount (hD := hD) P) (by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega) =
      ∑ i : Fin r, match W i with
        | none => 0
        | some w => if (K i : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
            ((1/2 : OtherField c.top) * ∑ k : ZMod b,
              ((f i k).coeff w - (f i (k + (d : ZMod b))).coeff w)^2) *
              (completeResponseCycle (c.originalInternalResidue P) active
                (i.val : ZMod (originalSelectedCount (hD := hD) P)))⁻¹
          else 0 := by
  obtain ⟨hCQ, hcyclic⟩ := c.originalClosure_cross_self_cyclic_charge P Q z hQ active
    (d * r) hshort J
  obtain ⟨_, hfilters⟩ := c.originalClosure_phase_laurent_energy P Q z hQ active
    b r d hB hresponse hgap
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hc := hcyclic hactive
  have hf := hfilters hactive
  -- Keep the genuine full profiles opaque throughout finite coefficient manipulations.
  generalize hC : finiteWordCycle (c.originalInternalEndpointProfiles Q)
    (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega) = C at hc hf ⊢
  dsimp only at hc hf ⊢
  intro W hchoice
  let e := ZMod.ringEquivCongr hB.symm
  let height := fun x : ZMod (originalSelectedCount (hD := hD) P) =>
    (c.top : ℤ) + c.originalCompletedGap P ((ZMod.finEquiv _).symm x)
  let weight := fun x : ZMod (originalSelectedCount (hD := hD) P) =>
    (completeResponseCycle (c.originalInternalResidue P) active x)⁻¹
  have hpH : Function.Periodic height (r : ZMod (originalSelectedCount (hD := hD) P)) := by
    intro x
    exact congrArg (fun t : ℤ => (c.top : ℤ) + t) (hgap x)
  have hpW : Function.Periodic weight (r : ZMod (originalSelectedCount (hD := hD) P)) := by
    intro x
    dsimp only [weight]
    rw [hresponse x]
  have hsplit := cyclic_profile_charge_phases b r d e C height weight hpH hpW (J : ℤ)
  dsimp only [height, weight] at hsplit
  rw [hsplit] at hc
  have hnat (p : Polynomial (OtherField c.top)) (l : ℕ) :
      p.toLaurent.coeff (l : ℤ) = p.coeff l := by
    change (Finsupp.mapDomain (fun n : ℕ => (n : ℤ)) p.toFinsupp.coeff) (l : ℤ) = _
    exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ l
  have hneg (p : Polynomial (OtherField c.top)) (a : ℤ) (ha : a < 0) :
      p.toLaurent.coeff a = 0 := by
    apply Finsupp.notMem_support_iff.mp
    rw [LaurentPolynomial.support_coeff_toLaurent]
    intro hs
    obtain ⟨l, _, hl⟩ := Finset.mem_map.mp hs
    have hl' : (l : ℤ) = a := hl
    have : 0 ≤ a := by rw [← hl']; exact Int.natCast_nonneg l
    omega
  apply hc.trans
  apply Finset.sum_congr rfl
  intro i _
  let f := fun k : ZMod b => (C (e (phaseCycleEquiv b r (i,k)))).1
  let g := fun k : ZMod b => (C (e (phaseCycleEquiv b r (i,k)))).2
  let H0 := height (i.val : ZMod (originalSelectedCount (hD := hD) P))
  let K := H0.toNat
  have hci := hchoice i
  cases hwi : W i with
  | none =>
    have hinv : ∀ k, f k = f (k + (d : ZMod b)) := by
      simpa only [hwi, f, e] using hci
    have hpoly : ∑ k : ZMod b, (f k * g (k + (d : ZMod b)) - f k * g k) = 0 :=
      directed_cross_profile_invariant_sum f g (Equiv.addRight (d : ZMod b)) hinv
    have hzero : (∑ k : ZMod b,
        ((f k * g (k + (d : ZMod b)) - f k * g k).toLaurent).coeff (H0 - (J : ℤ))) = 0 := by
      by_cases ha : H0 - (J : ℤ) < 0
      · apply Finset.sum_eq_zero
        intro k _
        exact hneg _ _ ha
      · let l := (H0 - (J : ℤ)).toNat
        have hdegree : H0 - (J : ℤ) = (l : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
        simp_rw [hdegree, hnat]
        have he := congrArg (fun p : Polynomial (OtherField c.top) => p.coeff l) hpoly
        simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] using he
    change (∑ k : ZMod b,
      ((f k * g (k + (d : ZMod b)) - f k * g k).toLaurent).coeff (H0 - (J : ℤ))) *
        weight (i.val : ZMod (originalSelectedCount (hD := hD) P)) = 0
    rw [hzero, zero_mul]
  | some w =>
    have hdata : 0 < w ∧ 2 * w < K ∧
        (∀ k l, l < w → (f k).coeff l = (f (k + (d : ZMod b))).coeff l) ∧
        (K : ℤ) - 2 * (w : ℤ) ≤ (J : ℤ) := by
      simpa only [hwi, f, e, K, H0, height] using hci
    obtain ⟨hw, hhalf, hm, hmargin⟩ := hdata
    have he := hf i w hw hhalf hm J hmargin
    have he' : (∑ k : ZMod b,
        ((f k * g (k + (d : ZMod b)) - f k * g k).toLaurent).coeff (H0 - (J : ℤ))) =
        if (K : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
          (1/2 : OtherField c.top) * ∑ k : ZMod b,
            ((f k).coeff w - (f (k + (d : ZMod b))).coeff w)^2 else 0 := by
      simpa only [f, g, e, K, H0, height] using he
    change (∑ k : ZMod b,
      ((f k * g (k + (d : ZMod b)) - f k * g k).toLaurent).coeff (H0 - (J : ℤ))) *
        weight (i.val : ZMod (originalSelectedCount (hD := hD) P)) =
      if (K : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
        ((1/2 : OtherField c.top) * ∑ k : ZMod b,
          ((f k).coeff w - (f (k + (d : ZMod b))).coeff w)^2) *
          weight (i.val : ZMod (originalSelectedCount (hD := hD) P)) else 0
    rw [he']
    split_ifs <;> simp only [zero_mul]

end SkewCornerDescent.Matrix.SelectedCoordinate
