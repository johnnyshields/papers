/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosurePhaseEnergy

/-!
# Actual Laurent phase-energy filtering

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual full profile jets give the exact attaining-phase half-square sum.
Earlier natural degrees and negative integer offsets both vanish, without
truncating an invisible offset to the nonzero constant profile degree. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A resolving margin retains exactly the phases attaining their first
profile-energy degree. Earlier and negative integer offsets vanish; no
natural-subtraction convention is used for an invisible Laurent coefficient. -/
theorem originalClosure_phase_laurent_energy {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (b r d : ℕ) [NeZero b] [NeZero r]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hresponse : Function.Periodic (completeResponseCycle (c.originalInternalResidue P) active)
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    let cycle := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    ∀ i : Fin r,
    let f := fun k : ZMod b => (cycle
      (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1
    let g := fun k : ZMod b => (cycle
      (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).2
    let K := ((c.top : ℤ) + c.originalCompletedGap P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))).toNat
    ∀ w : ℕ, 0 < w → 2 * w < K →
    (∀ k l, l < w → (f k).coeff l = (f (k + (d : ZMod b))).coeff l) →
    ∀ J : ℕ+, (K : ℤ) - 2 * (w : ℤ) ≤ (J : ℤ) →
    (∑ k : ZMod b, ((f k * g (k + (d : ZMod b)) - f k * g k).toLaurent).coeff
      ((c.top : ℤ) + c.originalCompletedGap P
        ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P))) - (J : ℤ))) =
      if (K : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
        (1/2 : OtherField c.top) * ∑ k : ZMod b,
          ((f k).coeff w - (f (k + (d : ZMod b))).coeff w)^2
      else 0 := by
  obtain ⟨hCQ, hjets⟩ := c.originalClosure_phase_energy_jets P Q z hQ active b r d hB hresponse hgap
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hp := hjets hactive
  -- Keep the full profile cycle opaque while extracting Laurent coefficients.
  generalize hC : finiteWordCycle (c.originalInternalEndpointProfiles Q)
    (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega) = C at hp ⊢
  dsimp only at hp ⊢
  intro i w hw hhalf hm J hmargin
  have he := hp i w hw hhalf hm
  let f := fun k : ZMod b => (C
    (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1
  let g := fun k : ZMod b => (C
    (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).2
  let H0 := (c.top : ℤ) + c.originalCompletedGap P
    ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))
  let K := H0.toNat
  have hH0 : 0 ≤ H0 := by
    have hg := c.originalCompletedGap_gt_top P
      ((ZMod.finEquiv _).symm (i.val : ZMod (originalSelectedCount (hD := hD) P)))
    have hN : 0 < (c.top : ℤ) := by exact_mod_cast c.top.pos
    dsimp only [H0]
    omega
  have hK0 : (K : ℤ) = H0 := Int.toNat_of_nonneg hH0
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
  change (∑ k : ZMod b,
    ((f k * g (k + (d : ZMod b)) - f k * g k).toLaurent).coeff (H0 - (J : ℤ))) =
      if (K : ℤ) - 2 * (w : ℤ) = (J : ℤ) then
        (1/2 : OtherField c.top) * ∑ k : ZMod b,
          ((f k).coeff w - (f (k + (d : ZMod b))).coeff w)^2
      else 0
  by_cases htop : (K : ℤ) - 2 * (w : ℤ) = (J : ℤ)
  · rw [ite_eq_left htop]
    have hdegree : H0 - (J : ℤ) = ((2 * w : ℕ) : ℤ) := by omega
    simp_rw [hdegree, hnat]
    simpa only [f, g] using he.2
  · rw [ite_eq_right htop]
    have hbelow : H0 - (J : ℤ) < ((2 * w : ℕ) : ℤ) := by omega
    by_cases hnonneg : 0 ≤ H0 - (J : ℤ)
    · let l := (H0 - (J : ℤ)).toNat
      have hdegree : H0 - (J : ℤ) = (l : ℤ) := (Int.toNat_of_nonneg hnonneg).symm
      have hl : l < 2 * w := by omega
      simp_rw [hdegree, hnat]
      simpa only [f, g] using he.1 l hl
    · apply Finset.sum_eq_zero
      intro k _
      exact hneg _ _ (by omega)

end SkewCornerDescent.Matrix.SelectedCoordinate
