-- TODO-COPIED (trimmed): skew-factor-gluing/lean/SkewGluing/Invariance.lean
import Mathlib.Data.Int.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import SkewGluing.Composition
import SkewGluing.Mark

/-!
# Translation of marked inners

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`.  `MarkedInner.translate u ω`
translates `E` and `W₋`, keeping `v` and the case; it preserves well-formedness, conditions I–IV
and legality in both directions.

Sorry-free.
-/

namespace SkewGluing

/-- Translating by `w` and then by `-w` is the identity. -/
theorem translate_neg_translate_cancel (w : ℤ × ℤ) (D : Diagram) :
    translate (-w) (translate w D) = D := by
  rw [translate_translate, neg_add_cancel, translate_zero]

namespace Invariance

theorem translate_union (u : ℤ × ℤ) (A B : Diagram) :
    translate u (A ∪ B) = translate u A ∪ translate u B := by
  ext y
  simp only [mem_translate, Finset.mem_union]

theorem translate_sdiff (u : ℤ × ℤ) (A B : Diagram) :
    translate u (A \ B) = translate u A \ translate u B := by
  ext y
  simp only [mem_translate, Finset.mem_sdiff]

theorem translate_subset_iff (u : ℤ × ℤ) {A B : Diagram} :
    translate u A ⊆ translate u B ↔ A ⊆ B := by
  constructor
  · intro h x hx
    have := h (mem_translate.mpr (by simpa using hx) : x + u ∈ translate u A)
    simpa [mem_translate] using this
  · intro h x hx
    rw [mem_translate] at hx ⊢
    exact h hx

theorem translate_comm (u w : ℤ × ℤ) (A : Diagram) :
    translate u (translate w A) = translate w (translate u A) := by
  rw [translate_translate, translate_translate, add_comm]

theorem mem_translate_translate {x : ℤ × ℤ} (u w : ℤ × ℤ) (A : Diagram) :
    x ∈ translate u (translate w A) ↔ x - u - w ∈ A := by
  rw [mem_translate, mem_translate]

end Invariance

namespace MarkedInner

/-- The marked inner `ω` translated by `u`: `E` and `W₋` move, `v` and the attachment case are
unchanged (so `W₊` moves with `W₋`). -/
def translate (u : ℤ × ℤ) (ω : MarkedInner) : MarkedInner where
  E := SkewGluing.translate u ω.E
  W := SkewGluing.translate u ω.W
  v := ω.v
  case := ω.case

@[simp] theorem translate_E (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).E = SkewGluing.translate u ω.E := rfl

@[simp] theorem translate_W (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).W = SkewGluing.translate u ω.W := rfl

@[simp] theorem translate_v (u : ℤ × ℤ) (ω : MarkedInner) : (ω.translate u).v = ω.v := rfl

@[simp] theorem translate_case (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).case = ω.case := rfl

theorem translate_eq_translateBy (u : ℤ × ℤ) (ω : MarkedInner) :
    ω.translate u = ω.translateBy u := rfl

theorem translate_zero (ω : MarkedInner) : ω.translate 0 = ω := by
  cases ω
  simp [translate, SkewGluing.translate_zero]

theorem translate_translate (u w : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate w).translate u = ω.translate (u + w) := by
  simp [translate, SkewGluing.translate_translate]

theorem translate_neg_translate (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).translate (-u) = ω := by
  rw [translate_translate, neg_add_cancel, translate_zero]

theorem upper_translate (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).upper = SkewGluing.translate u ω.upper := by
  ext y
  simp only [upper, translate_W, translate_v, mem_translate]
  rw [sub_right_comm]

theorem middle_translate (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).middle = SkewGluing.translate u ω.middle := by
  unfold middle
  rw [upper_translate, Invariance.translate_sdiff, Invariance.translate_union]
  rfl

theorem width_translate (u : ℤ × ℤ) (ω : MarkedInner) : (ω.translate u).width = ω.width := by
  simp only [width, translate_W, span_translate]

theorem period_translate (u : ℤ × ℤ) (ω : MarkedInner) : (ω.translate u).period = ω.period :=
  rfl

/-! ### Well-formedness, conditions I–IV, legality -/

theorem vH_translate (u : ℤ × ℤ) (E : Diagram) : vH (SkewGluing.translate u E) = vH E := by
  rcases E.eq_empty_or_nonempty with h | h
  · subst h
    simp [SkewGluing.translate]
  · unfold vH
    rw [ne_translate h, sw_translate h]
    abel

theorem exists_min_translate (O : Diagram) (u : ℤ × ℤ) (P : ℤ × ℤ → Prop) :
    (∃ x ∈ SkewGluing.translate u O, content x = minContent (SkewGluing.translate u O) ∧ P x) ↔
      ∃ y ∈ O, content y = minContent O ∧ P (y + u) := by
  rcases O.eq_empty_or_nonempty with h | h
  · subst h
    simp [SkewGluing.translate]
  · rw [minContent_translate h]
    constructor
    · rintro ⟨x, hx, hc, hP⟩
      refine ⟨x - u, mem_translate.mp hx, ?_, by simpa using hP⟩
      rw [content_sub]; omega
    · rintro ⟨y, hy, hc, hP⟩
      refine ⟨y + u, mem_translate.mpr (by simpa using hy), ?_, hP⟩
      rw [content_add]; omega

theorem exists_max_translate (O : Diagram) (u : ℤ × ℤ) (P : ℤ × ℤ → Prop) :
    (∃ x ∈ SkewGluing.translate u O, content x = maxContent (SkewGluing.translate u O) ∧ P x) ↔
      ∃ y ∈ O, content y = maxContent O ∧ P (y + u) := by
  rcases O.eq_empty_or_nonempty with h | h
  · subst h
    simp [SkewGluing.translate]
  · rw [maxContent_translate h]
    constructor
    · rintro ⟨x, hx, hc, hP⟩
      refine ⟨x - u, mem_translate.mp hx, ?_, by simpa using hP⟩
      rw [content_sub]; omega
    · rintro ⟨y, hy, hc, hP⟩
      refine ⟨y + u, mem_translate.mpr (by simpa using hy), ?_, hP⟩
      rw [content_add]; omega

theorem lowerH_translate (u : ℤ × ℤ) (ω : MarkedInner) : (ω.translate u).LowerH ↔ ω.LowerH := by
  unfold LowerH
  rw [middle_translate, exists_min_translate (P := fun x => (x.1, x.2 - 1) ∈
    (ω.translate u).W)]
  refine exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [translate_W, mem_translate]
  have e : ((y + u).1, (y + u).2 - 1) - u = (y.1, y.2 - 1) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e]

theorem lowerV_translate (u : ℤ × ℤ) (ω : MarkedInner) : (ω.translate u).LowerV ↔ ω.LowerV := by
  unfold LowerV
  rw [middle_translate, exists_min_translate (P := fun x => (x.1 + 1, x.2) ∈
    (ω.translate u).W)]
  refine exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [translate_W, mem_translate]
  have e : ((y + u).1 + 1, (y + u).2) - u = (y.1 + 1, y.2) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e]

theorem upperH_translate (u : ℤ × ℤ) (ω : MarkedInner) : (ω.translate u).UpperH ↔ ω.UpperH := by
  unfold UpperH
  rw [middle_translate, exists_max_translate (P := fun x => (x.1, x.2 + 1) ∈
    (ω.translate u).upper), upper_translate]
  refine exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [mem_translate]
  have e : ((y + u).1, (y + u).2 + 1) - u = (y.1, y.2 + 1) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e]

theorem upperV_translate (u : ℤ × ℤ) (ω : MarkedInner) : (ω.translate u).UpperV ↔ ω.UpperV := by
  unfold UpperV
  rw [middle_translate, exists_max_translate (P := fun x => (x.1 - 1, x.2) ∈
    (ω.translate u).upper), upper_translate]
  refine exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [mem_translate]
  have e : ((y + u).1 - 1, (y + u).2) - u = (y.1 - 1, y.2) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e]

theorem attachmentMatches_translate (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).AttachmentMatches ↔ ω.AttachmentMatches := by
  simp only [AttachmentMatches, translate_case, lowerH_translate, lowerV_translate,
    upperH_translate, upperV_translate]

theorem isEmptyMark_translate (u : ℤ × ℤ) {ω : MarkedInner} (h : ω.IsEmptyMark) :
    (ω.translate u).IsEmptyMark := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, h3⟩
  · simp [h1, SkewGluing.translate]
  · change ω.v = vH (SkewGluing.translate u ω.E)
    rw [vH_translate]; exact h2

theorem isNonemptyMark_translate (u : ℤ × ℤ) {ω : MarkedInner} (hE : ω.E.Nonempty)
    (h : ω.IsNonemptyMark) : (ω.translate u).IsNonemptyMark := by
  obtain ⟨hne, hW, hWE, hUE, hsw, hneU, hatt⟩ := h
  refine ⟨hne.image _, isConnectedSkew_translate u hW,
    (Invariance.translate_subset_iff u).mpr hWE, ?_, ?_, ?_, ?_⟩
  · rw [upper_translate]; exact (Invariance.translate_subset_iff u).mpr hUE
  · change sw (SkewGluing.translate u ω.E) ∈ SkewGluing.translate u ω.W
    rw [sw_translate hE, mem_translate, add_sub_cancel_right]; exact hsw
  · rw [upper_translate]
    change ne (SkewGluing.translate u ω.E) ∈ SkewGluing.translate u ω.upper
    rw [ne_translate hE, mem_translate, add_sub_cancel_right]; exact hneU
  · exact (attachmentMatches_translate u ω).mpr hatt

theorem isWellFormed_translate (u : ℤ × ℤ) {ω : MarkedInner} (h : ω.IsWellFormed) :
    (ω.translate u).IsWellFormed := by
  obtain ⟨hE, hm⟩ := h
  refine ⟨isConnectedSkew_translate u hE, ?_⟩
  rcases hm with h | h
  · exact Or.inl (isEmptyMark_translate u h)
  · exact Or.inr (isNonemptyMark_translate u hE.2.1 h)

theorem isNarrow_translate (u : ℤ × ℤ) {ω : MarkedInner} (h : ω.IsNarrow) :
    (ω.translate u).IsNarrow := by
  unfold IsNarrow at *
  rw [width_translate, period_translate]; exact h

theorem removalsConnected_translate (u : ℤ × ℤ) {ω : MarkedInner} (h : ω.RemovalsConnected) :
    (ω.translate u).RemovalsConnected := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · change IsConnectedSkew (SkewGluing.translate u ω.E \ SkewGluing.translate u ω.W)
    rw [← Invariance.translate_sdiff]; exact isConnectedSkew_translate u h1
  · change IsConnectedSkew (SkewGluing.translate u ω.E \ (ω.translate u).upper)
    rw [upper_translate, ← Invariance.translate_sdiff]; exact isConnectedSkew_translate u h2

theorem isMaximal_translate (u : ℤ × ℤ) {ω : MarkedInner} (hE : ω.E.Nonempty)
    (h : ω.IsMaximal) : (ω.translate u).IsMaximal := by
  intro W'' hW'' hlt hsk hc x hx hsub
  have hW''E : W'' ⊆ SkewGluing.translate u ω.E := Finset.mem_powerset.mp hW''
  have hW' : SkewGluing.translate (-u) W'' ∈ ω.E.powerset := by
    rw [Finset.mem_powerset]
    have := (Invariance.translate_subset_iff (-u)).mpr hW''E
    rwa [translate_neg_translate_cancel] at this
  have hlt' : ω.W ⊂ SkewGluing.translate (-u) W'' := by
    have hlt0 : SkewGluing.translate u ω.W ⊂ W'' := hlt
    have := translate_ssubset (-u) hlt0
    rwa [translate_neg_translate_cancel] at this
  have hc' : contents (SkewGluing.translate (-u) W'') = contents ω.W := by
    have hc0 : contents W'' = contents (SkewGluing.translate u ω.W) := hc
    ext k
    rw [mem_contents_translate, hc0, mem_contents_translate]
    have : k - content (-u) - content u = k := by simp only [content]; simp; ring
    rw [this]
  have hxu : x - u ∈ SkewGluing.translate (-u) W'' := by
    rw [mem_translate]
    simpa using hx
  refine h _ hW' hlt' (isSkew_translate _ hsk) hc' (x - u) hxu ?_
  intro z hz
  rw [mem_translate, mem_translate] at hz
  have hsub0 : SkewGluing.translate (ne (SkewGluing.translate u ω.E) - x) W'' ⊆
      SkewGluing.translate u ω.E := hsub
  rw [ne_translate hE] at hsub0
  have hzu : z + u ∈ SkewGluing.translate (ne ω.E + u - x) W'' := by
    rw [mem_translate]
    have e : z + u - (ne ω.E + u - x) = z - (ne ω.E - (x - u)) - -u := by abel
    rw [e]; exact hz
  have := hsub0 hzu
  rw [mem_translate] at this
  simpa using this

theorem mem_periodicUnion_translate (u : ℤ × ℤ) (ω : MarkedInner) (x : ℤ × ℤ) :
    x ∈ (ω.translate u).periodicUnion ↔ x - u ∈ ω.periodicUnion := by
  simp only [periodicUnion, Set.mem_ofPred_eq, translate_E, translate_v, mem_translate]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rwa [sub_right_comm] at hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rwa [sub_right_comm]⟩

theorem noHatAdjacency_translate (u : ℤ × ℤ) {ω : MarkedInner} (h : ω.NoHatAdjacency) :
    (ω.translate u).NoHatAdjacency := by
  intro k m x hx y hy hadj
  obtain ⟨hx1, hx2⟩ := hx
  have hm : ∀ z, z ∈ SkewGluing.translate (k • ω.v) (ω.translate u).middle ↔
      z - u ∈ SkewGluing.translate (k • ω.v) ω.middle := by
    intro z
    rw [middle_translate, Invariance.mem_translate_translate, mem_translate, sub_right_comm]
  have hw : ∀ z, z ∈ SkewGluing.translate (m • ω.v) (ω.translate u).W ↔
      z - u ∈ SkewGluing.translate (m • ω.v) ω.W := by
    intro z
    rw [translate_W, Invariance.mem_translate_translate, mem_translate, sub_right_comm]
  have hxe : x + eCell - u = x - u + eCell := by abel
  refine h k m (x - u) ⟨(hm x).mp hx1, ?_⟩ (y - u) ?_ (cellAdj_sub u hadj)
  · rw [← hxe]; exact (hm _).mp hx2
  · rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨(mem_periodicUnion_translate u ω y).mp h1, ?_⟩
      have := (hw _).mp h2
      rwa [show y + eCell - u = y - u + eCell by abel] at this
    · right
      refine ⟨(hw y).mp h1, ?_⟩
      have := (mem_periodicUnion_translate u ω (y + eCell)).mp h2
      rwa [show y + eCell - u = y - u + eCell by abel] at this

/-- Translation preserves legality. -/
theorem isLegal_translate (u : ℤ × ℤ) {ω : MarkedInner} (h : ω.IsLegal) :
    (ω.translate u).IsLegal :=
  ⟨isWellFormed_translate u h.1, isMaximal_translate u h.1.1.2.1 h.2.1,
    isNarrow_translate u h.2.2.1, removalsConnected_translate u h.2.2.2.1,
    noHatAdjacency_translate u h.2.2.2.2⟩

/-- Legality is invariant under translation, in both directions. -/
theorem isLegal_translate_iff (u : ℤ × ℤ) {ω : MarkedInner} :
    (ω.translate u).IsLegal ↔ ω.IsLegal :=
  ⟨fun h => by simpa [translate_neg_translate] using isLegal_translate (-u) h,
    isLegal_translate u⟩

theorem isWellFormed_translate_iff (u : ℤ × ℤ) {ω : MarkedInner} :
    (ω.translate u).IsWellFormed ↔ ω.IsWellFormed :=
  ⟨fun h => by simpa [translate_neg_translate] using isWellFormed_translate (-u) h,
    isWellFormed_translate u⟩

theorem isNarrow_translate_iff (u : ℤ × ℤ) {ω : MarkedInner} :
    (ω.translate u).IsNarrow ↔ ω.IsNarrow :=
  ⟨fun h => by simpa [translate_neg_translate] using isNarrow_translate (-u) h,
    isNarrow_translate u⟩

theorem removalsConnected_translate_iff (u : ℤ × ℤ) {ω : MarkedInner} :
    (ω.translate u).RemovalsConnected ↔ ω.RemovalsConnected :=
  ⟨fun h => by simpa [translate_neg_translate] using removalsConnected_translate (-u) h,
    removalsConnected_translate u⟩

theorem noHatAdjacency_translate_iff (u : ℤ × ℤ) {ω : MarkedInner} :
    (ω.translate u).NoHatAdjacency ↔ ω.NoHatAdjacency :=
  ⟨fun h => by simpa [translate_neg_translate] using noHatAdjacency_translate (-u) h,
    noHatAdjacency_translate u⟩

theorem isMaximal_translate_iff (u : ℤ × ℤ) {ω : MarkedInner} (hE : ω.E.Nonempty) :
    (ω.translate u).IsMaximal ↔ ω.IsMaximal :=
  ⟨fun h => by
    simpa [translate_neg_translate] using isMaximal_translate (-u) (hE.image _) h,
    isMaximal_translate u hE⟩

end MarkedInner

end SkewGluing
