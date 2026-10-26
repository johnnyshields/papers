/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.OrdinaryMarkCensus

/-!
# Kernel-certified ordinary gauge census through eight cells

Formalizes the exhaustive assertion of
`shields-2026-skew-corner-descent.tex` (`rem:ordinary-gauge`).
The complete actual profile and mark generators are reduced in the kernel.
There are exactly three positive ordinary gauge pairs and six ordinary
marks failing V; their projections are exactly those six marks. Every
pair has the genuine southeast-step displacement difference. Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
-- The kernel exhausts the bounded literal shape and full I--IV mark predicates.
/-- Complete finite classification through eight actual cells. The decision
uses kernel reduction only; no native decision axiom is used. -/
theorem ordinary_gauge_census_eight :
    let G := ordinaryGaugeCensus 8
    let F := ordinaryVFailureCensus 8
    G.card = 3 ∧ F.card = 6 ∧
      G.image Prod.fst ∪ G.image Prod.snd = F ∧
      ∀ p : MarkedInner × MarkedInner, p ∈ G → p.1.v = p.2.v + eCell := by
  decide +kernel

end SkewCornerDescent
