/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Multiplicity.GeneralOrder
import CubicPochhammer.Multiplicity.CentralSlope
import CubicPochhammer.Multiplicity.OrderTwo
import CubicPochhammer.Multiplicity.OrderTwoSchur
import CubicPochhammer.Multiplicity.Classification

/-!
# The sharp multiplicity threshold

Formalizes `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp
multiplicity threshold»: `prop:multiplicity-threshold` and `cor:multiplicity`.
This module only re-exports the five it is split across, in the order
`prop:multiplicity-threshold` states them.

* `Multiplicity.GeneralOrder` — the degree-`m` product coefficient of
  `eq:general-r`, its three structural identities, and `eq:r-degree-three`: the
  closed form of the degree-three Turánian coefficient of the two-term
  sequence, whose `μ`-coefficient carries the factor `r-3`.
* `Multiplicity.CentralSlope` — the degree-three constant-weight kernel in the
  coordinate `q = p(1-p)`, and `eq:r-central-slope`: its slope at the center is
  positive at `r = 2`, zero at `r = 3`, negative for `r ≥ 4`.
* `Multiplicity.OrderTwo` — `thm:kernel` re-proved at multiplicity two, where
  the derivative numerator has a closed form and no Bernstein certificate is
  needed.
* `Multiplicity.OrderTwoSchur` — the reduction of `sec:reduction` repeated at
  `r = 2`, ending in the generalized Turánian.
* `Multiplicity.Classification` — the two halves meeting:
  `UniversalLogConcave r ↔ r ≤ 3`.

## References

* `shields-2026-cubic-pochhammer.tex`, `sec:threshold` «The sharp multiplicity
  threshold»: `prop:multiplicity-threshold`, `cor:multiplicity`,
  `eq:general-r`, `eq:r-degree-three`, `eq:r-central-slope`.
-/
