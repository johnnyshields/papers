/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.Reduction
import SkewCoframeRigidity.FixedCap.CellExample
import SkewCoframeRigidity.FixedCap.CapDescent

/-!
# Upstream input of the first defect coefficient

`first_defect_coeff_ne_zero` (`ph:first-D`) uses the cell-cap theorem `sc:fixed-cap` for the
one-cell cap, in the form of its descent `CapVanishing cellCap`: two connected normalized
diagrams with the same function and the same function after the `00`-splice with a single cell
are the same diagram.  The one-cell descent is the statement recorded here (a corollary of the unconditional fixed-cap theorem).
-/

namespace SkewCoframeRigidity.Unshifted

/-- `sc:fixed-cap` for the one-cell cap (descent form). -/
theorem cellCap_vanishing : SkewCoframeRigidity.FixedCap.CapVanishing cellCap :=
  SkewCoframeRigidity.FixedCap.capVanishing cellCap cellCap_isNorm cellCap_connected

end SkewCoframeRigidity.Unshifted
