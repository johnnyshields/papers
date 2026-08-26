/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Combinatorics.Young.LGVOddPaths
import Shields.Combinatorics.Young.LGVTableauTwo

/-!
# The super branching rule at two rows, with the even half discharged

`Shields.sum_nonMeeting_mixed_eq_superSkewSchur` carries two tableau bijections as hypotheses: the
even one, `Shields.NonCrossingIsSkewSchur`, and the odd one,
`Shields.NonMeetingIsSkewSchurTranspose`.  The even one is
`Shields.nonCrossingIsSkewSchur`, so it need not be assumed; this module discharges it and leaves
the odd one open to a caller.

Nothing here is new mathematics.  It is the wiring, isolated so that the hypothesis being
discharged is visible in one place rather than inferred by comparing modules.

## Main results

* `Shields.sum_nonMeeting_mixed_eq_superSkewSchur_of_odd` -- the branching rule at two rows,
  assuming only the odd tableau bijection.
* `Shields.skewJacobiTrudi_two_even` -- the purely even specialization, which needs no hypothesis
  at all: with no odd variables the mixed model is the even one.

## Tags

super Schur function, skew Schur function, branching rule, Jacobi-Trudi
-/

namespace Shields

open Finset

variable {R : Type*} [CommRing R]

/-- **the super branching rule at two rows, with the even half discharged.**

`LGVOdd.sum_nonMeeting_mixed_eq_superSkewSchur` carries `NonCrossingIsSkewSchur b β`; that is
`LGVTableau.nonCrossingIsSkewSchur`, so it need not be assumed.  The hypothesis left here is
`NonMeetingIsSkewSchurTranspose a α`, the odd counterpart: non-meeting odd pairs carry
`skewSchur lam.transpose nu.transpose a α`.  That is `LGVOddTableau`'s
`nonMeetingIsSkewSchurTranspose`, so the fully discharged form is
`LGVOddTableau.sum_nonMeeting_mixed_eq_superSkewSchur_uncond`; this statement is the
intermediate one, with the even half gone and the odd half still open to a caller. -/
theorem sum_nonMeeting_mixed_eq_superSkewSchur_of_odd {b a : ℕ} {β α : ℕ → R}
    (hE : NonMeetingIsSkewSchurTranspose a α)
    (lam mu : YoungDiagram) (hmu : mu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) :
    ∑ x ∈ (mixedPaths b a (mu.rowLen 0 + 1) (lam.rowLen 0 + 1) ×ˢ
            mixedPaths b a (mu.rowLen 1) (lam.rowLen 1)).filter
              fun x => ¬ MixedMeets b a x.1 x.2,
        mixedWeight b a β α x.1 * mixedWeight b a β α x.2
      = superSkewSchur lam mu b a β α :=
  sum_nonMeeting_mixed_eq_superSkewSchur (nonCrossingIsSkewSchur b β) hE lam mu hmu hrow

/-- The purely even specialization needs no hypothesis at all: with no odd variables the
mixed model is the even one, and `LGVTableau.skewJacobiTrudi_two` already gives the identity.
Recorded here so the `a = 0` corner of the super branching rule is not left looking
conditional. -/
theorem skewJacobiTrudi_two_even {b : ℕ} {β α : ℕ → R}
    (lam mu : YoungDiagram) (hmu : mu ≤ lam) (hrow : ∀ i, 2 ≤ i → lam.rowLen i = 0) :
    jacobiTrudiDet (fun m => superHom b 0 m β α) lam mu 2 = superSkewSchur lam mu b 0 β α :=
  skewJacobiTrudi_two lam mu hmu hrow

end Shields
