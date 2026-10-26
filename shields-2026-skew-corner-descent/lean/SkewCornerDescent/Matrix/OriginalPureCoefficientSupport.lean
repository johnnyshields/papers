/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPureVisibleUnits
import SkewCornerDescent.Matrix.OriginalEmptyIncomingTop

/-!
# Lower-field support of actual higher pure incoming coefficients

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The actual pure inventory produces a gap-zero unit for every nonzero
visible higher incoming coefficient. Its complete inverse leading term
places that coefficient strictly below any larger protected generator.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A higher visible pure incoming coefficient cannot depend on any generator
strictly above its actual distance, including through the full interval inverse. -/
theorem originalPure_visible_left_coefficient_mem_lower {n : ℕ} (P : Profile n) (k : ℕ)
    (hK : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ k) (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (w : ℕ) (hN : (c.top : ℕ) < w)
    (hw : 2 * (w : ℤ) < originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i))
    (H : ℕ+) (hwH : w < (H : ℕ)) :
    ((c.originalInternalEndpointProfiles P i).1).coeff w ∈ residueLowerField c.top H := by
  classical
  by_cases hzero : ((c.originalInternalEndpointProfiles P i).1).coeff w = 0
  · rw [hzero]
    exact (residueLowerField c.top H).zero_mem
  obtain ⟨p, hempty, hp⟩ :=
    c.originalPure_visible_nonzero_coefficient_unit P k hK i w hN hw hzero
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  obtain ⟨J, hJdist, hJ, R, hR, hcoeff⟩ :=
    c.original_empty_left_profile_top P (E ai) (some (E bi)) p hempty
  have hrow := (originalEmptyBlock_remaining_endpoints P p.val.val.1 hempty p.val.val.2).1
  have hJe : (J : ℤ) = (w : ℤ) := by
    rw [hJdist]
    change _ - P.xi p.val.val.1.val.succ = _
    rw [← hrow]
    exact hp
  have hJw : (J : ℕ) = w := by exact_mod_cast hJe
  have hJH : J < H := by change (J : ℕ) < (H : ℕ); omega
  have hgen : residueGenerator c.top ⟨J, ne_of_gt hJ⟩ ∈ residueLowerField c.top H := by
    simpa only [c.residueMap_other J (ne_of_gt hJ), residueGenerator] using
      c.residue_other_mem_lower H J (ne_of_gt hJ) hJH
  have hmem := (residueLowerField c.top H).add_mem
    ((residueLowerField c.top H).neg_mem hgen)
    (residueLowerField_mono hJH.le hR)
  change (c.originalResidueLeftEndpointPolynomial P (some (E ai)) (some (E bi))).coeff w ∈ _
  rw [← hJw, hcoeff]
  exact hmem

end SkewCornerDescent.Matrix.SelectedCoordinate
