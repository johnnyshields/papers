/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationRowComposition
import SkewClassInflation.SaturationMarkLegality
import SkewClassInflation.SaturationColumnResidues
import SkewClassInflation.SaturationPrepend
import SkewClassInflation.RibbonCellChains

/-!
# Literal legal marked presentations of all repeated-block sources

Formalizes `prop:saturation-chart` of
`shields-2026-skew-class-inflation.tex`.  Horizontal outer steps produce
actual merged powers; north steps produce the actual larger-seam joins.
The affine composition therefore agrees cell for cell with the complete
source, in a specified translation.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative SkewGluing

variable (A : SaturationInner)

private theorem translate_union (v : ℤ × ℤ) (D E : Diagram) :
    translate v (D ∪ E) = translate v D ∪ translate v E := Finset.image_union _ _

/-- Each actual positive outer row word gives the literal complete source in a fixed origin. -/
theorem chain_compose_eq_source (a : ℕ) (ha : 0 < a)
    (l : List ℕ) (hl : ∀ b ∈ l, 0 < b) :
    A.markedInner.compose (profileCells (ribbonChain a ha l hl).2) =
      translate (((1 - ((a + l.sum : ℕ) : ℤ)) * A.k), -((a + l.sum : ℕ) : ℤ) * A.k)
        (profileCells (A.chain a ha l hl).2) := by
  induction l generalizing a with
  | nil =>
    change A.markedInner.compose (profileCells (ribbonRow a ha)) = _
    rw [profileCells_ribbonRow, A.row_compose_eq_power a ha]
    rfl
  | cons b l ih =>
    let htail : ∀ j ∈ l, 0 < j := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    let hb : 0 < b := hl b List.mem_cons_self
    let R := ribbonChain b hb l htail
    let S := A.chain b hb l htail
    have hR : (profileCells R.2).Nonempty := (profileCells_connected R.2).2.1
    have hrow : (rowCells 0 a).Nonempty := rowCells_nonempty (by exact_mod_cast ha)
    have hleft : (translate (0, R.2.xi 0) (rowCells 0 a)).Nonempty := hrow.image _
    have hright : (translate (1, 1) (profileCells R.2)).Nonempty := hR.image _
    have hp : A.d < (A.power a ha).r (Fin.last (a * A.k)) := A.power_rows_above_seam a ha _
    have hq : A.d < S.2.r 0 := by rw [A.chain_first]; have := A.first_bound; omega
    change A.markedInner.compose
      (profileCells (Profile.zeroJoin (ribbonRow a ha) R.2)) =
      translate (((1 - ((a + (b :: l).sum : ℕ) : ℤ)) * A.k),
        -((a + (b :: l).sum : ℕ) : ℤ) * A.k)
        (profileCells (Profile.join (A.power a ha) S.2 A.d hp hq))
    rw [Profile.zeroJoin, profileCells_join, profileCells_ribbonRow]
    simp only [Nat.cast_zero, zero_add, sub_zero]
    rw [ordinary_compose_union _ rfl _ _ hleft hright,
      ordinary_compose_translate _ rfl _ hrow,
      ordinary_compose_translate _ rfl _ hR,
      A.row_compose_eq_power a ha, ih b hb htail, profileCells_join, translate_union,
      translate_translate, translate_translate, translate_translate, translate_translate]
    have hr : R.2.xi 0 = (b + l.sum : ℕ) := ribbonChain_span b hb l htail
    have hs : S.2.xi 0 = ((b + l.sum : ℕ) : ℤ) * A.spanIncrement + A.d :=
      A.chain_span b hb l htail
    have hbase := congrArg (fun D : ConnectedProfile => D.2.xi 0) A.power_one_profile
    rw [A.power_span] at hbase
    simp only [Nat.cast_one, one_mul] at hbase
    have hinc : A.spanIncrement = A.profile.xi 0 - A.d := by omega
    have ho1 : A.markedInner.origin (rowCells 0 a) (0, R.2.xi 0) =
        (-((b + l.sum : ℕ) : ℤ) * A.k,
          ((b + l.sum : ℕ) : ℤ) * (A.profile.xi 0 - A.k - A.d)) := by
      simp [MarkedInner.origin, markedInner, content, eCell, hr]
      ring
    have ho2 : A.markedInner.origin (profileCells R.2) (1, 1) = (1, 1) := by
      simp [MarkedInner.origin, markedInner, content, eCell]
    rw [ho1, ho2, hs, hinc]
    congr 2 <;> ext <;> simp only [Prod.fst_add, Prod.snd_add, List.sum_cons,
      Nat.cast_add, Nat.cast_mul] <;> ring

/-- The canonical outer composition has the exact literal marked-cell presentation of its source. -/
theorem diagram_compose_eq_source {M : ℕ} (α : Composition M) (hM : 0 < M) :
    A.markedInner.compose (profileCells (outerRibbon α hM).2) =
      translate (((1 - (M : ℤ)) * A.k), -(M : ℤ) * A.k) (profileCells (A.diagram α hM).2) := by
  have hex : ∃ a l, α.blocks = a :: l := by
    cases he : α.blocks with
    | nil =>
      have hs := α.blocks_sum
      rw [he, List.sum_nil] at hs
      omega
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨a, l, he⟩ := hex
  let ha : 0 < a := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
  let hl : ∀ b ∈ l, 0 < b :=
    fun b hb => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hb)
  have houter := outerRibbon_eq_chain α hM a ha l hl he
  have hsource := A.diagram_eq_chain α hM a ha l hl he
  have hsum : a + l.sum = M := by
    have hh := α.blocks_sum
    rw [he, List.sum_cons] at hh
    exact hh
  calc
    _ = A.markedInner.compose (profileCells (ribbonChain a ha l hl).2) :=
      congrArg (fun D : ConnectedProfile => A.markedInner.compose (profileCells D.2)) houter
    _ = translate (((1 - ((a + l.sum : ℕ) : ℤ)) * A.k), -((a + l.sum : ℕ) : ℤ) * A.k)
        (profileCells (A.chain a ha l hl).2) := A.chain_compose_eq_source a ha l hl
    _ = translate (((1 - (M : ℤ)) * A.k), -(M : ℤ) * A.k)
        (profileCells (A.chain a ha l hl).2) := by rw [hsum]
    _ = _ := congrArg (fun D : ConnectedProfile =>
      translate (((1 - (M : ℤ)) * A.k), -(M : ℤ) * A.k) (profileCells D.2)) hsource.symm

/-- The actual general chart satisfies I--V and gives its complete source literally. -/
theorem literal_legal_chart {M : ℕ} (α : Composition M) (hM : 0 < M) :
    IsConnectedSkew (profileCells (outerRibbon α hM).2) ∧
      List.ofFn (outerRibbon α hM).2.r = α.blocks ∧
      (outerRibbon α hM).2.toBetaDiagram.schur = ribbonWord α.blocks ∧
      A.markedInner.IsLegal ∧
      (attachmentCells A.markedInner.W A.markedInner.middle).card = 1 ∧
      (attachmentCells A.markedInner.upper A.markedInner.middle).card = 1 ∧
      A.markedInner.compose (profileCells (outerRibbon α hM).2) =
        translate (((1 - (M : ℤ)) * A.k), -(M : ℤ) * A.k) (profileCells (A.diagram α hM).2) :=
  ⟨profileCells_connected _, outerRibbon_word α hM, outerRibbon_schur α hM,
    A.markedInner_legal, A.markedInner_hypothesisV.1, A.markedInner_hypothesisV.2,
    A.diagram_compose_eq_source α hM⟩

end SkewClassInflation.SaturationInner
