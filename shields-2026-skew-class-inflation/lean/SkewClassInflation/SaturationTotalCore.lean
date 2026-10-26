/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationContraction
import SkewClassInflation.SaturationPowerRigidity

/-!
# Literal total cores of arbitrary source mates

The total-contraction step of `lem:total-contraction-inverse` in
`shields-2026-skew-class-inflation.tex`.  Actual extreme coefficients
produce the full power function; unrestricted power rigidity identifies
the actual contracted profile up to global rotation.  Positional splitting
of this fixed core is a separate obligation.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewJacobiNegative.Staircase

variable (A : SaturationInner)

/-- Every arbitrary mate's actual total contraction is the source's full power or its rotation. -/
theorem arbitrary_mate_total_core_rigidity {M n : ℕ} (α : Composition M) (hM : 2 ≤ M)
    (P : Profile n)
    (he : P.toBetaDiagram.schur = (A.diagram α (by omega)).2.toBetaDiagram.schur) :
    (contractAllMinimum P A.largeLabel : ConnectedProfile) =
        ⟨M * A.k, A.power M (by omega)⟩ ∨
      (contractAllMinimum P A.largeLabel : ConnectedProfile) =
        ConnectedProfile.rotate ⟨M * A.k, A.power M (by omega)⟩ :=
  A.power_mate_eq_or_rotate M hM (contractAllMinimum P A.largeLabel).2
    (A.arbitrary_mate_total_contraction α (by omega) P he)

/-- The actual total contraction has exactly the full power's number of internal row boundaries. -/
theorem arbitrary_mate_total_core_row_count {M n : ℕ} (α : Composition M) (hM : 2 ≤ M)
    (P : Profile n)
    (he : P.toBetaDiagram.schur = (A.diagram α (by omega)).2.toBetaDiagram.schur) :
    (contractAllMinimum P A.largeLabel).1 = M * A.k := by
  rcases A.arbitrary_mate_total_core_rigidity α hM P he with h | h <;>
    exact congrArg Sigma.fst h

end SkewClassInflation.SaturationInner
