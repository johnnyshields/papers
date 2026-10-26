/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.AtlasPolynomials
import SkewCoframeRigidity.Stationary.BCell
import SkewCoframeRigidity.Stationary.CellJet
import SkewCoframeRigidity.Stationary.CellPowers
import SkewCoframeRigidity.Stationary.ClippedMem
import SkewCoframeRigidity.Stationary.ComponentColumn
import SkewCoframeRigidity.Stationary.ComponentNonzero
import SkewCoframeRigidity.Stationary.ComponentRemainder
import SkewCoframeRigidity.Stationary.ComponentRemainderThm
import SkewCoframeRigidity.Stationary.Deriv
import SkewCoframeRigidity.Stationary.DerivCoframe
import SkewCoframeRigidity.Stationary.DerivSeries
import SkewCoframeRigidity.Stationary.Endpoints
import SkewCoframeRigidity.Stationary.FieldDescent
import SkewCoframeRigidity.Stationary.FieldIntersection
import SkewCoframeRigidity.Stationary.Incidence
import SkewCoframeRigidity.Stationary.IncidenceBoth
import SkewCoframeRigidity.Stationary.LowerField
import SkewCoframeRigidity.Stationary.LowerSeries
import SkewCoframeRigidity.Stationary.MatchedDeriv
import SkewCoframeRigidity.Stationary.MatchingWiring
import SkewCoframeRigidity.Stationary.NeitherCase
import SkewCoframeRigidity.Stationary.NonnegSeries
import SkewCoframeRigidity.Stationary.PositivePower
import SkewCoframeRigidity.Stationary.PositivePowerFinal
import SkewCoframeRigidity.Stationary.PowerEquation
import SkewCoframeRigidity.Stationary.Ratio
import SkewCoframeRigidity.Stationary.SeriesPower
import SkewCoframeRigidity.Stationary.TerminalExample
import SkewCoframeRigidity.Stationary.TopColumn
import SkewCoframeRigidity.Stationary.TopData
import SkewCoframeRigidity.Stationary.TopGeometry
import SkewCoframeRigidity.Stationary.TopMatching
import SkewCoframeRigidity.Stationary.TopMatchingThm
import SkewCoframeRigidity.Stationary.TopSupport
import SkewCoframeRigidity.Stationary.Transcendence
import SkewCoframeRigidity.Stationary.UnitCase.Algebra
import SkewCoframeRigidity.Stationary.UnitCase.CoreIdentify
import SkewCoframeRigidity.Stationary.UnitCase.Embed
import SkewCoframeRigidity.Stationary.UnitCase.HatCoframe
import SkewCoframeRigidity.Stationary.UnitCase.Main
import SkewCoframeRigidity.Stationary.UnitCase.Masks
import SkewCoframeRigidity.Stationary.UnitCase.Master
import SkewCoframeRigidity.Stationary.UnitCase.MasterDelta
import SkewCoframeRigidity.Stationary.UnitCase.Pair
import SkewCoframeRigidity.Stationary.UnitCase.Reconstruct
import SkewCoframeRigidity.Stationary.UnitCase.Scale
import SkewCoframeRigidity.Stationary.UnitCase.Setup

/-!
# Finite stationary separation

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Finite stationary separation»
(`sec:stationary`): the endpoint identities of the clipped operator, `sc:component-remainder`,
`sc:component-column`, `sc:top-matching`, `sc:top-support`, `ex:terminal-coframes`.
-/
