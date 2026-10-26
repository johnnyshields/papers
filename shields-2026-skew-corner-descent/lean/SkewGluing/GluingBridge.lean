/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.TransportCoefficient
import GluingCore.CellSchurTableau
import GluingCore.Composition

/-!
# Identification with the copied composition substrate

Supports `shields-2026-skew-corner-descent.tex`, «Corner transport» (`eq:homomorphism`).
The copied substrate has a total Schur function; the paper-facing API requires a skew witness.
They agree on actual skew diagrams, proved through profile presentations rather than assumed
from their names.  Mark conversion preserves the actual four-case composition cell set.

Sorry-free.
-/

namespace SkewGluing

/-- The same row/gap data in the copied composition substrate. -/
def Profile.toGluing {n : ℕ} (P : Profile n) : GluingCore.Profile n where
  r := P.r
  g := P.g
  r_pos := P.r_pos
  g_lt_castSucc := P.g_lt_castSucc
  g_lt_succ := P.g_lt_succ

theorem Profile.toGluing_cells {n : ℕ} (P : Profile n) : P.toGluing.cells = P.cells := rfl

theorem Profile.toGluing_schur {n : ℕ} (P : Profile n) : P.toGluing.schur = P.schur := rfl

/-- Connected Schur functions agree at a proved common profile presentation. -/
theorem connectedSchur_eq_gluing {D : Diagram} (hD : IsConnectedSkew D) :
    connectedSchur D hD = GluingCore.connectedSchur D := by
  let P := (diagramProfile D hD).2
  obtain ⟨v, hv⟩ := diagramProfile_spec D hD
  rw [connectedSchur_eq_profile hD P v hv]
  have hv' : D = GluingCore.translate v P.toGluing.cells := hv
  conv_rhs => rw [hv', GluingCore.connectedSchur_translate,
    GluingCore.connectedSchur_of_isConnectedSkew P.toGluing.isConnectedSkew_cells,
    GluingCore.cellProfile_cells]
  exact P.toGluing_schur.symm

/-- The proof-parameterized component product agrees with the copied total function on its domain. -/
theorem cellSchur_eq_gluing (D : Diagram) (hD : IsSkew D) :
    cellSchur D hD = GluingCore.cellSchur D := by
  unfold cellSchur GluingCore.cellSchur
  rw [← Finset.prod_attach (GluingCore.edgeComponents D) GluingCore.connectedSchur]
  apply Finset.prod_congr rfl
  intro C _
  exact connectedSchur_eq_gluing (isConnectedSkew_component hD C.2)

/-- Transfer the four attachment cases without changing their meaning. -/
def AttachCase.toGluing : AttachCase → GluingCore.AttachCase
  | .a => .a
  | .b => .b
  | .c => .c
  | .d => .d

/-- The copied mark has exactly the same cells, displacement, and attachment reading. -/
def MarkedInner.toGluing (ω : MarkedInner) : GluingCore.MarkedInner :=
  ⟨ω.E, ω.W, ω.v, ω.case.toGluing⟩

/-- Legality is preserved, including the empty-mark convention. -/
theorem MarkedInner.IsLegal.toGluing {ω : MarkedInner} (hω : ω.IsLegal) :
    ω.toGluing.IsLegal := by
  have hi : ω.toGluing.IsLegal ↔ ω.IsLegal := by
    cases ω with
    | mk E W v ac =>
      cases ac <;>
        simp [MarkedInner.IsLegal, GluingCore.MarkedInner.IsLegal,
          MarkedInner.IsWellFormed, GluingCore.MarkedInner.IsWellFormed,
          MarkedInner.IsEmptyMark, GluingCore.MarkedInner.IsEmptyMark,
          MarkedInner.IsNonemptyMark, GluingCore.MarkedInner.IsNonemptyMark,
          MarkedInner.AttachmentMatches, GluingCore.MarkedInner.AttachmentMatches,
          MarkedInner.toGluing, AttachCase.toGluing] <;> rfl
  exact hi.mpr hω

/-- The copied composition and the paper-facing composition have the same cells in every case. -/
theorem MarkedInner.toGluing_compose (ω : MarkedInner) (D : Diagram) :
    ω.toGluing.compose D = ω.compose D := by
  cases ω with
  | mk E W v ac => cases ac <;> rfl

end SkewGluing
