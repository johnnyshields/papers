import SkewGluing.FoldSupplied.Lift
import SkewGluing.FoldSupplied.Basics
import SkewGluing.FoldSupplied.Areas
import SkewGluing.FoldSupplied.Empty
import SkewGluing.FoldSupplied.EmptyLift
import SkewGluing.FoldSupplied.JWords
import SkewGluing.FoldSupplied.OrdinaryEmpty
import SkewGluing.FoldSupplied.OrdinaryPhi
import SkewGluing.FoldSupplied.OrdinaryBlock
import SkewGluing.FoldSupplied.OrdinaryGeneric
import SkewGluing.FoldSupplied.OrdinaryFacts
import SkewGluing.FoldSupplied.OrdinarySlotBig
import SkewGluing.FoldSupplied.OrdinarySlotSmall
import SkewGluing.FoldSupplied.OrdinarySlotBigB
import SkewGluing.FoldSupplied.OrdinaryChart
import SkewGluing.FoldSupplied.Ordinary

/-!
# Residue folds of a supplied inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`, `ge:empty-fold`), «Two ordinary roots»
(`prop:gluing-ordinary-fold`) and «Small-overlap roots» (`lem:gluing-small`): the folds applied to
an actual supplied inner, and their lift to the original parent by aligned composition.

* `FoldSupplied.Lift`: the lift through aligned composition (`exists_lifted_chart`).
* `FoldSupplied.Empty`, `FoldSupplied.EmptyLift`: the empty residue fold and its lift.
* `FoldSupplied.Ordinary*`: the ordinary residue fold (`ordinary_fold`) and its lift.
* `FoldSupplied.Areas`: the inner of a proper chart has strictly fewer cells than its parent.

Sorry-free.
-/
