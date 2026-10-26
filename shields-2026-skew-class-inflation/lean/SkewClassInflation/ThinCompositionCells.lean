/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonCellChains
import SkewClassInflation.OrdinaryComposition
import SkewClassInflation.ThinRowComposition
import SkewClassInflation.ThinBetaSets
import SkewClassInflation.ThinMarkAttachments
import SkewClassInflation.ThinMarkLegality

/-!
# Literal outer composition for the full thin family

The literal chart equality in `lem:subthreshold-transport` in
`shields-2026-skew-class-inflation.tex`.  Every positive outer row word
is assembled in order; inflation is applied to the complete source
profile, including every zero seam.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewGluing

variable (B : ThinParameters)

private theorem translate_union (v : ℤ × ℤ) (D E : Diagram) :
    translate v (D ∪ E) = translate v D ∪ translate v E := Finset.image_union _ _

/-- An arbitrary positive outer ribbon presents the actual inflated thin source literally. -/
theorem chain_compose_eq_inflation (a : ℕ) (ha : 0 < a)
    (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) (t : ℕ) :
    (B.inflationMark t).compose (profileCells (ribbonChain a ha l hl).2) =
      translate (1 - ((a + l.sum : ℕ) : ℤ), -((a + l.sum : ℕ) : ℤ))
        (profileCells (Profile.inflate t (B.chain a ha l hl).2)) := by
  induction l generalizing a with
  | nil =>
    change (B.inflationMark t).compose (profileCells (ribbonRow a ha)) = _
    rw [profileCells_ribbonRow, B.row_compose_eq_innerPower a t ha]
    rfl
  | cons b l ih =>
    let htail : ∀ k ∈ l, 0 < k := fun k hk => hl k (List.mem_cons_of_mem _ hk)
    let hb : 0 < b := hl b List.mem_cons_self
    let R := ribbonChain b hb l htail
    let S := B.chain b hb l htail
    have hR : (profileCells R.2).Nonempty := (profileCells_connected R.2).2.1
    have hrow : (rowCells 0 a).Nonempty := rowCells_nonempty (by exact_mod_cast ha)
    have hleft : (translate (0, R.2.xi 0) (rowCells 0 a)).Nonempty := hrow.image _
    have hright : (translate (1, 1) (profileCells R.2)).Nonempty := hR.image _
    change (B.inflationMark t).compose
      (profileCells (Profile.zeroJoin (ribbonRow a ha) R.2)) =
      translate (1 - ((a + (b :: l).sum : ℕ) : ℤ), -((a + (b :: l).sum : ℕ) : ℤ))
        (profileCells (Profile.inflate t (Profile.zeroJoin (B.innerPower a ha) S.2)))
    rw [Profile.zeroJoin, profileCells_join, profileCells_ribbonRow]
    simp only [Nat.cast_zero, zero_add, sub_zero]
    rw [ordinary_compose_union _ rfl _ _ hleft hright,
      ordinary_compose_translate _ rfl _ hrow,
      ordinary_compose_translate _ rfl _ hR,
      B.row_compose_eq_innerPower a t ha, ih b hb htail,
      profileCells_inflate_zeroJoin, translate_union,
      translate_translate, translate_translate, translate_translate, translate_translate]
    have hr : R.2.xi 0 = (b + l.sum : ℕ) := ribbonChain_span b hb l htail
    have hs : S.2.xi 0 = ((b + l.sum : ℕ) : ℤ) * B.boundary.q :=
      B.chain_span b hb l htail
    have ho1 : (B.inflationMark t).origin (rowCells 0 a) (0, R.2.xi 0) =
        (-((b + l.sum : ℕ) : ℤ), ((b + l.sum : ℕ) : ℤ) * (B.boundary.q - 1)) := by
      simp [MarkedInner.origin, inflationMark, content, eCell, hr]
    have ho2 : (B.inflationMark t).origin (profileCells R.2) (1, 1) = (1, 1) := by
      simp [MarkedInner.origin, inflationMark, content, eCell]
    rw [ho1, ho2, hs]
    congr 2 <;> ext <;> simp only [Prod.fst_add, Prod.snd_add, List.sum_cons,
      Nat.cast_add] <;> ring

/-- The identity holds on the canonical ribbon profile, not only a recursive model. -/
theorem ribbonRows_compose_eq_inflation (a : ℕ) (ha : 0 < a)
    (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) (t : ℕ) :
    (B.inflationMark t).compose (profileCells (ribbonRows a ha l hl)) =
      translate (1 - ((a + l.sum : ℕ) : ℤ), -((a + l.sum : ℕ) : ℤ))
        (profileCells (Profile.inflate t (B.chain a ha l hl).2)) := by
  have he := congrArg (fun D : ConnectedProfile => profileCells D.2)
    (ribbonChain_eq_ribbonRows a ha l hl)
  rw [← he]
  exact B.chain_compose_eq_inflation a ha l hl t

/-- The literal identity in `lem:subthreshold-transport`, at every inflation amount. -/
theorem diagram_compose_eq_inflation {M : ℕ} (α : Composition M) (hM : 0 < M) (t : ℕ) :
    (B.inflationMark t).compose (profileCells (outerRibbon α hM).2) =
      translate (1 - (M : ℤ), -(M : ℤ))
        (profileCells (Profile.inflate t (B.diagram α hM).2)) := by
  cases he : α.blocks with
  | nil =>
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  | cons a l =>
    have hs := α.blocks_sum
    rw [he, List.sum_cons] at hs
    have ha := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    have hl : ∀ k ∈ l, 0 < k := fun _ hk =>
      α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hk)
    unfold outerRibbon diagram
    split
    · rename_i hn
      have hh := hn.symm.trans he
      cases hh
    · rename_i a' l' he'
      have hh := List.cons.inj (he'.symm.trans he)
      obtain ⟨rfl, rfl⟩ := hh
      dsimp only
      split
      · rename_i hn
        have hh := hn.symm.trans he
        cases hh
      · rename_i a' l' he'
        have hh := List.cons.inj (he'.symm.trans he)
        obtain ⟨rfl, rfl⟩ := hh
        dsimp only
        simpa only [hs] using B.chain_compose_eq_inflation _ ha _ hl t

/-- The complete literal subthreshold chart, with every geometric hypothesis supplied. -/
theorem subthreshold_literal_chart {M : ℕ} (α : Composition M) (hM : 0 < M)
    (t : ℕ) (ht : 0 < t) (htp : t < B.boundary.p) :
    IsConnectedSkew (profileCells (outerRibbon α hM).2) ∧
      List.ofFn (outerRibbon α hM).2.r = α.blocks ∧
      (outerRibbon α hM).2.toBetaDiagram.schur = ribbonWord α.blocks ∧
      (B.inflationMark t).IsLegal ∧
      (attachmentCells (B.inflationMark t).W (B.inflationMark t).middle).card = 1 ∧
      (attachmentCells (B.inflationMark t).upper (B.inflationMark t).middle).card = 1 ∧
      (B.inflationMark t).compose (profileCells (outerRibbon α hM).2) =
        translate (1 - (M : ℤ), -(M : ℤ))
          (profileCells (Profile.inflate t (B.diagram α hM).2)) := by
  obtain ⟨hW, hU⟩ := B.inflationMark_hypothesisV t ht htp
  exact ⟨profileCells_connected _, outerRibbon_word α hM, outerRibbon_schur α hM,
    B.inflationMark_legal t htp, hW, hU, B.diagram_compose_eq_inflation α hM t⟩

end SkewClassInflation.ThinParameters
