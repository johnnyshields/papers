/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import CubicPochhammer.Weighting
import CubicPochhammer.ResidueSums
import CubicPochhammer.Snj
import CubicPochhammer.BernsteinBasis
import CubicPochhammer.Bernstein
import CubicPochhammer.Blocks
import CubicPochhammer.Kernel
import CubicPochhammer.CentralProducts
import CubicPochhammer.BetaOrder
import CubicPochhammer.Bridge
import CubicPochhammer.Main
import CubicPochhammer.Multiplicity
import CubicPochhammer.Consequences
import CubicPochhammer.Differential
import CubicPochhammer.AxiomCheck

/-!
# Coefficientwise Schur-concavity of the cubic Pochhammer series

The root of the formalization of `shields-2026-cubic-pochhammer.tex`.  It
imports every module, so `import CubicPochhammer` brings the whole development
into scope and the axiom guard of `AxiomCheck.lean` runs with it.

The development runs in four stages, and the modules are grouped by them.

* **The certificate.**  `ResidueSums` proves the period-6 closed form of the
  residue-class binomial sums; `Snj` turns it into `S_{n,j} ≥ 0`;
  `BernsteinBasis` supplies the division-free Bernstein transform; and
  `Bernstein` assembles `lem:bernstein`, `J_m(t) > 0`.
* **The kernel.**  `Blocks` pairs the summands of `J_m` and proves the single
  sign change; `Weighting` proves the summation-by-parts weighting principle;
  `Kernel` combines them into `thm:kernel`, monotonicity of `G_{m,w}`.
* **The reduction.**  `BetaOrder` proves the likelihood-ratio order of
  `lem:beta-order` without naming a probability law; `CentralProducts` is the
  sequence hypothesis of `lem:central-products`; `Bridge` carries the kernel
  monotonicity across `eq:C-beta` to Schur-concavity of the coefficient
  convolution; `Main` states `thm:main`.
* **Beyond the cubic theorem.**  `Multiplicity` proves
  `prop:multiplicity-threshold`, and `Consequences` with `Differential` proves
  `cor:ordinary` and what is available of `cor:differential`.

## References

* `shields-2026-cubic-pochhammer.tex`.  `lean/README.md` carries the per-item
  status table, and `AxiomCheck.lean` pins the axiom footprint of each result
  it claims.
-/
