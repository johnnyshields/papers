/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Composition

/-!
# Translation of actual positive marked inners

Supports `shields-2026-skew-corner-descent.tex` (`rem:ordinary-gauge`).
The existing marked-inner translation moves the entire inner and lower
copy together, retaining the displacement and attachment case. All finite
and periodic legality conditions are transported, including maximality
and every hatted adjacency. Sorry-free.
-/

namespace SkewGluing.MarkedInner

private theorem translated_difference (t : ℤ × ℤ) (A B : Diagram) :
    translate t (A \ B) = translate t A \ translate t B := by
  ext x
  simp only [mem_translate, Finset.mem_sdiff]

/-- Both actual marked copies move by the same translation. -/
theorem upper_translateBy (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.translateBy t).upper = translate t ω.upper := by
  simp only [upper, translateBy, translate_translate]
  congr 1
  exact add_comm _ _

/-- The complete middle moves together with the two marked copies. -/
theorem middle_translateBy (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.translateBy t).middle = translate t ω.middle := by
  unfold middle
  rw [upper_translateBy]
  ext x
  simp only [translateBy, mem_translate, Finset.mem_sdiff, Finset.mem_union]

private theorem exists_boundary_translate (O S : Diagram) (t : ℤ × ℤ)
    (bound : Diagram → ℤ)
    (hbound : O.Nonempty → bound (translate t O) = bound O + content t)
    (f : ℤ × ℤ → ℤ × ℤ) (hf : ∀ x, f (x + t) = f x + t) :
    (∃ x ∈ translate t O, content x = bound (translate t O) ∧ f x ∈ translate t S) ↔
      ∃ x ∈ O, content x = bound O ∧ f x ∈ S := by
  by_cases hO : O.Nonempty
  · constructor
    · rintro ⟨x, hx, hc, hfx⟩
      refine ⟨x-t, mem_translate.mp hx, ?_, ?_⟩
      · rw [hbound hO] at hc
        rw [content_sub]
        omega
      · have he : f x-t = f (x-t) := by
          have h := congrArg (fun z => z-t) (hf (x-t))
          simpa only [sub_add_cancel, add_sub_cancel_right] using h
        rw [← he]
        exact mem_translate.mp hfx
    · rintro ⟨x, hx, hc, hfx⟩
      refine ⟨x+t, mem_translate.mpr (by simpa using hx), ?_, ?_⟩
      · rw [hbound hO, content_add, hc]
      · rw [hf]
        exact mem_translate.mpr (by simpa using hfx)
  · have he : O = ∅ := Finset.not_nonempty_iff_eq_empty.mp hO
    simp [he, translate]

/-- Translation preserves the actual lower horizontal attachment. -/
theorem lowerH_translateBy (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.translateBy t).LowerH ↔ ω.LowerH := by
  unfold LowerH
  rw [middle_translateBy]
  exact exists_boundary_translate ω.middle ω.W t minContent
    (fun h => minContent_translate h t) (fun x => (x.1, x.2-1))
    (by
      intro x
      apply Prod.ext
      · rfl
      · change x.2+t.2-1 = x.2-1+t.2
        omega)

/-- Translation preserves the actual lower vertical attachment. -/
theorem lowerV_translateBy (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.translateBy t).LowerV ↔ ω.LowerV := by
  unfold LowerV
  rw [middle_translateBy]
  exact exists_boundary_translate ω.middle ω.W t minContent
    (fun h => minContent_translate h t) (fun x => (x.1+1, x.2))
    (by
      intro x
      apply Prod.ext
      · change x.1+t.1+1 = x.1+1+t.1
        omega
      · rfl)

/-- Translation preserves the actual upper horizontal attachment. -/
theorem upperH_translateBy (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.translateBy t).UpperH ↔ ω.UpperH := by
  unfold UpperH
  rw [middle_translateBy, upper_translateBy]
  exact exists_boundary_translate ω.middle ω.upper t maxContent
    (fun h => maxContent_translate h t) (fun x => (x.1, x.2+1))
    (by
      intro x
      apply Prod.ext
      · rfl
      · change x.2+t.2+1 = x.2+1+t.2
        omega)

/-- Translation preserves the actual upper vertical attachment. -/
theorem upperV_translateBy (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.translateBy t).UpperV ↔ ω.UpperV := by
  unfold UpperV
  rw [middle_translateBy, upper_translateBy]
  exact exists_boundary_translate ω.middle ω.upper t maxContent
    (fun h => maxContent_translate h t) (fun x => (x.1-1, x.2))
    (by
      intro x
      apply Prod.ext
      · change x.1+t.1-1 = x.1-1+t.1
        omega
      · rfl)

/-- The complete attachment case is unchanged by literal translation. -/
theorem attachmentMatches_translateBy (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.translateBy t).AttachmentMatches ↔ ω.AttachmentMatches := by
  unfold AttachmentMatches
  rw [lowerH_translateBy, lowerV_translateBy, upperH_translateBy, upperV_translateBy]
  rfl

/-- A positive well-formed mark remains the same positive attachment after translation. -/
theorem isNonemptyMark_translateBy {ω : MarkedInner} (hE : IsConnectedSkew ω.E)
    (h : ω.IsNonemptyMark) (t : ℤ × ℤ) : (ω.translateBy t).IsNonemptyMark := by
  obtain ⟨hne, hW, hWE, hUE, hsw, hneU, hatt⟩ := h
  refine ⟨?_, isConnectedSkew_translate t hW, ?_, ?_, ?_, ?_,
    (attachmentMatches_translateBy ω t).mpr hatt⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x+t, mem_translate.mpr (by simpa using hx)⟩
  · intro x hx
    exact mem_translate.mpr (hWE (mem_translate.mp hx))
  · rw [upper_translateBy]
    intro x hx
    exact mem_translate.mpr (hUE (mem_translate.mp hx))
  · change sw (translate t ω.E) ∈ translate t ω.W
    rw [sw_translate hE.2.1 t]
    exact mem_translate.mpr (by simpa using hsw)
  · rw [upper_translateBy]
    change ne (translate t ω.E) ∈ translate t ω.upper
    rw [ne_translate hE.2.1 t]
    exact mem_translate.mpr (by simpa using hneU)

/-- Maximality at the actual displacement moves with the whole marked inner. -/
theorem isMaximalAtDisplacement_translateBy {ω : MarkedInner}
    (h : ω.IsMaximalAtDisplacement) (t : ℤ × ℤ) :
    (ω.translateBy t).IsMaximalAtDisplacement := by
  intro X hX hlt hsk hc hsub
  let Y := translate (-t) X
  have hXE := Finset.mem_powerset.mp hX
  have hYE : Y ⊆ ω.E := by
    have hm : translate (-t) X ⊆ translate (-t) (translate t ω.E) :=
      Finset.image_subset_image hXE
    simpa only [Y, translate_translate, neg_add_cancel, translate_zero] using hm
  have hltY : ω.W ⊂ Y := by
    have hm := translate_ssubset (-t) hlt
    simpa only [translateBy, translate_translate, neg_add_cancel, translate_zero] using hm
  have hskY : IsSkew Y := isSkew_translate (-t) hsk
  have hcY : contents Y = contents ω.W := by
    change contents X = contents (translate t ω.W) at hc
    change contents (translate (-t) X) = contents ω.W
    rw [contents_translate, hc, contents_translate, Finset.image_image]
    have ht : content (-t) = -content t := by
      simp only [content, Prod.fst_neg, Prod.snd_neg]
      ring
    simp only [ht, Function.comp_def, add_neg_cancel_right]
    exact Finset.image_id'
  have hsubY : translate ω.v Y ⊆ ω.E := by
    have hm := Finset.image_subset_image hsub (f := fun x : ℤ × ℤ => x-t)
    change translate (-t) (translate ω.v X) ⊆ translate (-t) (translate t ω.E) at hm
    simpa only [Y, translate_translate, neg_add_cancel, add_neg_cancel, translate_zero,
      add_comm] using hm
  exact h Y (Finset.mem_powerset.mpr hYE) hltY hskY hcY hsubY

/-- The infinite periodic union moves as a whole. -/
theorem mem_periodicUnion_translateBy (ω : MarkedInner) (t x : ℤ × ℤ) :
    x ∈ (ω.translateBy t).periodicUnion ↔ x-t ∈ ω.periodicUnion := by
  simp only [periodicUnion, translateBy, Set.mem_ofPred_eq, mem_translate]
  have he (k : ℤ) : x-k • ω.v-t = x-t-k • ω.v := by abel
  simp only [he]

/-- Every periodic copy of the finite middle moves with the source. -/
theorem mem_middle_copy_translateBy (ω : MarkedInner) (t x : ℤ × ℤ) (k : ℤ) :
    x ∈ translate (k • (ω.translateBy t).v) (ω.translateBy t).middle ↔
      x-t ∈ translate (k • ω.v) ω.middle := by
  rw [middle_translateBy]
  simp only [translateBy, mem_translate]
  abel_nf

private theorem mem_mark_copy_translateBy (ω : MarkedInner) (t x : ℤ × ℤ) (k : ℤ) :
    x ∈ translate (k • (ω.translateBy t).v) (ω.translateBy t).W ↔
      x-t ∈ translate (k • ω.v) ω.W := by
  simp only [translateBy, mem_translate]
  abel_nf

/-- Condition IV retains every actual periodic and hatted cell under translation. -/
theorem noHatAdjacency_translateBy {ω : MarkedInner} (h : ω.NoHatAdjacency) (t : ℤ × ℤ) :
    (ω.translateBy t).NoHatAdjacency := by
  intro k m x hx y hy hadj
  have hxe : x+eCell-t = x-t+eCell := by abel
  have hye : y+eCell-t = y-t+eCell := by abel
  have hxback : x-t ∈ hatMiddle (translate (k • ω.v) ω.middle) := by
    exact ⟨(mem_middle_copy_translateBy ω t x k).mp hx.1,
      hxe ▸ (mem_middle_copy_translateBy ω t (x+eCell) k).mp hx.2⟩
  have hyback : y-t ∈ ω.hatMark (translate (m • ω.v) ω.W) := by
    rcases hy with hy | hy
    · exact Or.inl ⟨(mem_periodicUnion_translateBy ω t y).mp hy.1,
        hye ▸ (mem_mark_copy_translateBy ω t (y+eCell) m).mp hy.2⟩
    · exact Or.inr ⟨(mem_mark_copy_translateBy ω t y m).mp hy.1,
        hye ▸ (mem_periodicUnion_translateBy ω t (y+eCell)).mp hy.2⟩
  exact h k m (x-t) hxback (y-t) hyback (cellAdj_sub t hadj)

/-- Every positive legal mark remains legal after literal translation. -/
theorem isLegal_translateBy_nonempty {ω : MarkedInner} (h : ω.IsLegal)
    (hW : ω.W.Nonempty) (t : ℤ × ℤ) : (ω.translateBy t).IsLegal := by
  have hnon : ω.IsNonemptyMark := by
    rcases h.1.2 with hemp | hnon
    · exact False.elim (hW.ne_empty hemp.1)
    · exact hnon
  have hEt := isConnectedSkew_translate t h.1.1
  have hnont := isNonemptyMark_translateBy h.1.1 hnon t
  have hmax := isMaximalAtDisplacement_translateBy
    (h.2.1.atDisplacement hnon.2.2.2.2.2.1) t
  refine ⟨⟨hEt, Or.inr hnont⟩, hmax.isMaximal hEt hnont, ?_, ?_,
    noHatAdjacency_translateBy h.2.2.2.2 t⟩
  · simpa only [IsNarrow, width, period, translateBy, span_translate] using h.2.2.1
  · obtain ⟨hleft, hright⟩ := h.2.2.2.1
    constructor
    · change IsConnectedSkew (translate t ω.E \ translate t ω.W)
      rw [← translated_difference]
      exact isConnectedSkew_translate t hleft
    · rw [upper_translateBy]
      change IsConnectedSkew (translate t ω.E \ translate t ω.upper)
      rw [← translated_difference]
      exact isConnectedSkew_translate t hright

/-- Whole marked-inner translations compose by adding their actual vectors. -/
theorem translateBy_add (ω : MarkedInner) (t u : ℤ × ℤ) :
    (ω.translateBy t).translateBy u = ω.translateBy (t+u) := by
  cases ω
  simp only [translateBy, translate_translate, add_comm]

/-- The zero whole-mark translation changes no cell or attachment data. -/
theorem translateBy_zero (ω : MarkedInner) : ω.translateBy 0 = ω := by
  cases ω
  simp only [translateBy, translate_zero]

end SkewGluing.MarkedInner
