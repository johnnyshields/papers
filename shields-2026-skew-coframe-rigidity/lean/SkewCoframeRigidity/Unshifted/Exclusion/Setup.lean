/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Ports

/-!
# The shared setup of the unshifted exclusion

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`sec:unshifted`, `ph:unshifted-exclusion`).  The objects `m = M - 1`, `y = H_m`,
`G = G₀ + y a`, `C = C₀ + y b`, `Δ = G₀ - C₀`, the defect operators `ℰ^M_{A,B}` and the three
coefficients of the expansion of the unshifted identity in `y` are defined in `Exclusion.Defs`
(`ExclusionHyp`, `Eop`, `zeroTop`, `hSer`, `G0`, `C0`, `aVec`, `bVec`, `Delta`, `pDiff`,
`coefY0`, `coefY1`, `coefY2`).  The interface used by the disconnected and connected cases is

* `exclusion_expansion`: the three coefficient identities `[y^k]ℰ = 0` at precision `2M`;
* `exclusion_ports`: a proper row at position `M - 1` and a proper column at position one occur;
* `pDiff_factor`: the factor `p (ϑ^{p-1} - h^{p-1}) z^m` is `z^M` times a unit;
* `eq_zero_of_pDiff_vanish`: a polynomial of degree below `M` killed by that factor is zero.

All are sorry-free.
-/
