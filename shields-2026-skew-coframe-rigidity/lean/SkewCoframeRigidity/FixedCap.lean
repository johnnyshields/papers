/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.BoundaryDet
import SkewCoframeRigidity.FixedCap.CapPoly
import SkewCoframeRigidity.FixedCap.SpliceIdentity
import SkewCoframeRigidity.FixedCap.LeftCoframe
import SkewCoframeRigidity.FixedCap.LetterField
import SkewCoframeRigidity.FixedCap.Reduction
import SkewCoframeRigidity.FixedCap.StageOne
import SkewCoframeRigidity.FixedCap.Descent
import SkewCoframeRigidity.FixedCap.CapDescent
import SkewCoframeRigidity.FixedCap.CellExample

/-!
# Rigidity with the same literal cap

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Rigidity with the same literal cap»
(`sec:fixed-caps`): the splice identity `sc:splice-identity`, the coherent form of the two
observations `sc:fcp-observations`, the prefix of zero coefficients `sc:fcp-prefix-zero`,
and the descent that proves `sc:fixed-cap` for every connected normalized cap
(`fixed_cap_rigidity_unconditional`): the derivative of the coframe equations in a letter above the
remaining rows, the next strict block, the recursive cap, and unique factorization of the
connected numerators.
-/
