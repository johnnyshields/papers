/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.ProfileInvariant

/-!
# Connected-diagram Jacobi--Trudi functions

Formalizes the connected-diagram/profile bridge for `shields-2026-skew-corner-descent.tex`,
«Corner cofactors and common cores» (`sec:corner`, `eq:jt`).  The value agrees with every profile
presentation and is invariant under translation.  Disconnected component products and the
geometric interior identification are separate obligations.

Sorry-free.
-/

namespace SkewGluing

/-- The unique normalized profile of a connected skew diagram. -/
noncomputable def diagramProfile (D : Diagram) (hD : IsConnectedSkew D) : Σ n, Profile n :=
  ⟨(hD.exists_profile_cells).choose, ((hD.exists_profile_cells).choose_spec).choose⟩

theorem diagramProfile_spec (D : Diagram) (hD : IsConnectedSkew D) :
    ∃ v, D = translate v (diagramProfile D hD).2.cells := by
  exact ((hD.exists_profile_cells).choose_spec).choose_spec

/-- Every profile presentation computes the same normalized profile. -/
theorem diagramProfile_eq {D : Diagram} (hD : IsConnectedSkew D) {n : ℕ}
    (P : Profile n) (v : ℤ × ℤ) (h : D = translate v P.cells) :
    diagramProfile D hD = ⟨n, P⟩ := by
  obtain ⟨w, hw⟩ := diagramProfile_spec D hD
  exact Profile.presentation_sigma_unique (hw.symm.trans h)

/-- The skew Schur function of a connected cell diagram, computed by Jacobi--Trudi. -/
noncomputable def connectedSchur (D : Diagram) (hD : IsConnectedSkew D) : Lambda :=
  (diagramProfile D hD).2.schur

/-- The diagram-level function agrees with any translated profile Jacobi--Trudi determinant. -/
theorem connectedSchur_eq_profile {D : Diagram} (hD : IsConnectedSkew D) {n : ℕ}
    (P : Profile n) (v : ℤ × ℤ) (h : D = translate v P.cells) :
    connectedSchur D hD = P.schur := by
  unfold connectedSchur
  rw [diagramProfile_eq hD P v h]

/-- Translation leaves the normalized profile unchanged. -/
theorem diagramProfile_translate (D : Diagram) (hD : IsConnectedSkew D) (v : ℤ × ℤ) :
    diagramProfile (translate v D) (isConnectedSkew_translate v hD) = diagramProfile D hD := by
  obtain ⟨w, hw⟩ := diagramProfile_spec D hD
  exact diagramProfile_eq (isConnectedSkew_translate v hD) (diagramProfile D hD).2 (v + w)
    ((congrArg (translate v) hw).trans (translate_translate v w))

/-- Translation leaves the connected diagram's skew Schur function unchanged. -/
theorem connectedSchur_translate (D : Diagram) (hD : IsConnectedSkew D) (v : ℤ × ℤ) :
    connectedSchur (translate v D) (isConnectedSkew_translate v hD) = connectedSchur D hD := by
  unfold connectedSchur
  rw [diagramProfile_translate]

end SkewGluing
