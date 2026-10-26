/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralParentStrips
import SkewCornerDescent.Matrix.OriginalProfileWordPeriods
import SkewCornerDescent.CyclicPhaseFiberPeriod

/-!
# Complete incoming-profile periods on every genuine ordinary closure state

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The coprime no-discrepancy cycle gives the selected phase period. Full
ordinary source-copy locality then extends it to every actual interval
in the doubled closure, including crossing its true source splice.
No wrapped state replaces an original endpoint. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- No discrepancy gives the smaller incoming-profile period on the entire actual doubled word. -/
theorem originalClosure_no_discrepancy_incoming_period {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (b r d : ℕ) [NeZero b] [NeZero r] (hc : Nat.Coprime d b)
    (hB : originalSelectedCount (hD := hD) P = b * r) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    let cycle := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    (∀ (i : Fin r) (k : ZMod b),
      (cycle (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k)))).1 =
        (cycle (ZMod.ringEquivCongr hB.symm
          (phaseCycleEquiv b r (i,k+(d : ZMod b))))).1) →
    ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1), j.val = i.val+r →
      (c.originalInternalEndpointProfiles Q i).1 = (c.originalInternalEndpointProfiles Q j).1 := by
  obtain ⟨hCQ, hword⟩ := c.originalClosure_profile_word_period P Q z hQ
  refine ⟨hCQ, ?_⟩
  have hlen : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 := by
    have := NeZero.pos (originalSelectedCount (hD := hD) P)
    omega
  have hfull : ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1),
      j.val = i.val + originalSelectedCount (hD := hD) P →
        c.originalInternalEndpointProfiles Q i = c.originalInternalEndpointProfiles Q j := by
    simpa only [originalInternalEndpointProfiles] using hword
  dsimp only
  intro hp i j hij
  let C := finiteWordCycle (c.originalInternalEndpointProfiles Q) hlen
  have hper : Function.Periodic (fun z => (C z).1)
      (r : ZMod (originalSelectedCount (hD := hD) P)) :=
    phaseCycle_shift_invariant_periodic b r d (ZMod.ringEquivCongr hB.symm)
      (fun z => (C z).1) hc hp
  have hi := congrArg Prod.fst
    (finiteWordCycle_eq (c.originalInternalEndpointProfiles Q) hlen hfull i)
  have hj := congrArg Prod.fst
    (finiteWordCycle_eq (c.originalInternalEndpointProfiles Q) hlen hfull j)
  rw [hi, hj]
  have hx : (j.val : ZMod (originalSelectedCount (hD := hD) P)) =
      (i.val : ZMod (originalSelectedCount (hD := hD) P)) +
        (r : ZMod (originalSelectedCount (hD := hD) P)) := by rw [hij, Nat.cast_add]
  rw [hx]
  exact (hper _).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
