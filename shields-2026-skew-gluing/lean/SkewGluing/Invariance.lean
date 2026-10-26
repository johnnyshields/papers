import Mathlib.Data.Int.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import SkewGluing.RowInner
import SkewGluing.Composition

/-!
# Translation of marked inners

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`), the convention that diagrams and marked inners are read up
to translation.

* `MarkedInner.translate u ω` translates `E` and `W₋`, keeping `v` and the case.  It preserves
  well-formedness, I–IV and legality (both directions), width and period.
* `MarkedInner.compose_translate`: `(ω.translate u).compose D = translate u (ω.compose D)`.
* `MarkedInner.compose_translate_outer`: `ω.compose (translate u D)` is the translate of
  `ω.compose D` by `MarkedInner.outerShift ω u`, the vector read off `eq:gluing-offsets`.
* `MarkedInner.rotate_translate`: rotation commutes with translation (with the opposite vector).
* `MarkedInner.rotate_compose`: `ω.rotate.compose (rotate D) = rotate (ω.compose D)` for
  nonempty `D` (an equality of cell sets, no translation needed); for an arbitrary outer the two
  agree up to translation (`MarkedInner.rotate_compose_translate`).
* `fiberClass`: the fiber `fiber s ω Q` read up to translation; `fiberClass_translate_inner`
  (invariant under translating the marked inner), `fiberClass_eq_normalized` (determined by
  southwest-normalized outers), and the `cellSchur` instances.

Sorry-free.
-/

namespace SkewGluing

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

/-! ### Composition and translation -/

/-- Rotation commutes with translation, the translation vector being negated. -/
theorem rotate_translate (u : ℤ × ℤ) (ω : MarkedInner) :
    (ω.translate u).rotate = ω.rotate.translate (-u) := by
  change (⟨SkewGluing.rotate (SkewGluing.translate u ω.E),
      SkewGluing.rotate (ω.translate u).upper, ω.v, ω.case.rotate⟩ : MarkedInner) =
    ⟨SkewGluing.translate (-u) (SkewGluing.rotate ω.E),
      SkewGluing.translate (-u) (SkewGluing.rotate ω.upper), ω.v, ω.case.rotate⟩
  rw [upper_translate, rotate_translate_eq, rotate_translate_eq]

/-- **Composition with a translated marked inner.**  Translating the inner translates the
composite by the same vector. -/
theorem compose_translate (u : ℤ × ℤ) (D : Diagram) (ω : MarkedInner) :
    (ω.translate u).compose D = SkewGluing.translate u (ω.compose D) := by
  rcases D.eq_empty_or_nonempty with h | h
  · subst h
    simp [compose]
  · exact compose_translate_inner (ω := ω.translate u) (ω₀ := ω) u rfl rfl rfl rfl h

/-- The vector by which `ω.compose D` moves when the outer `D` is translated by `u`, read off
`eq:gluing-offsets`: `c(u) v + u₁ e`, `c(u) v - u₁ e`, `c(u) v`, `c(u) v` in cases (a)–(d)
(the offsets of the mixed cases involve `ℓ_k` and `h_k`, which move with the outer). -/
def outerShift (ω : MarkedInner) (u : ℤ × ℤ) : ℤ × ℤ :=
  match ω.case with
  | .a => content u • ω.v + u.1 • eCell
  | .b => content u • ω.v - u.1 • eCell
  | .c => content u • ω.v
  | .d => content u • ω.v

theorem origin_translate_outer {D : Diagram} {d : ℤ × ℤ} (hd : d ∈ D) (u : ℤ × ℤ)
    (ω : MarkedInner) :
    ω.origin (SkewGluing.translate u D) (d + u) = ω.origin D d + ω.outerShift u := by
  have hk : content d ∈ contents D := content_mem_contents hd
  have hc : content (d + u) = content d + content u := content_add d u
  unfold origin outerShift
  cases ω.case
  · simp only [hc, add_smul, Prod.fst_add]; abel
  · simp only [hc, add_smul, Prod.fst_add]; abel
  · simp only [hc, diagLo_translate u _ hk, add_smul, Prod.fst_add]
    have e : (d.1 + u.1 - (diagLo D (content d) + u.1)) = d.1 - diagLo D (content d) := by ring
    rw [e]; abel
  · simp only [hc, diagHi_translate u _ hk, add_smul, Prod.fst_add]
    have e : (diagHi D (content d) + u.1 - (d.1 + u.1)) = diagHi D (content d) - d.1 := by ring
    rw [e]; abel

theorem sameRibbon_translate_outer {D : Diagram} {d : ℤ × ℤ} (hd : d ∈ D) (u : ℤ × ℤ)
    (ω : MarkedInner) :
    ω.SameRibbon (SkewGluing.translate u D) (d + u) ↔ ω.SameRibbon D d := by
  have hk : content d ∈ contents D := content_mem_contents hd
  have hc : content (d + u) = content d + content u := content_add d u
  have hmem : ((d + u).1 - 1, (d + u).2) ∈ SkewGluing.translate u D ↔ (d.1 - 1, d.2) ∈ D := by
    rw [mem_translate]
    have e : ((d + u).1 - 1, (d + u).2) - u = (d.1 - 1, d.2) := by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
    rw [e]
  have hk1 : (d.1 - 1, d.2) ∈ D → content d + 1 ∈ contents D := fun h => by
    have := content_mem_contents h
    have e : content (d.1 - 1, d.2) = content d + 1 := by simp only [content]; ring
    rwa [e] at this
  have e1 : content d + content u + 1 = (content d + 1) + content u := by ring
  unfold SameRibbon
  rw [hc]
  cases hcs : ω.case
  · simp only [hmem, and_false]
  · simp only [hmem, and_false]
  · dsimp only
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hmem.mp h1
      refine ⟨h1', ?_⟩
      rw [diagLo_translate u _ hk, e1, diagLo_translate u _ (hk1 h1')] at h2
      simp only [Prod.fst_add] at h2
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨hmem.mpr h1, ?_⟩
      rw [diagLo_translate u _ hk, e1, diagLo_translate u _ (hk1 h1)]
      simp only [Prod.fst_add]
      omega
  · dsimp only
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hmem.mp h1
      refine ⟨h1', ?_⟩
      rw [diagHi_translate u _ hk, e1, diagHi_translate u _ (hk1 h1')] at h2
      simp only [Prod.fst_add] at h2
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨hmem.mpr h1, ?_⟩
      rw [diagHi_translate u _ hk, e1, diagHi_translate u _ (hk1 h1)]
      simp only [Prod.fst_add]
      omega

/-- **Composition with a translated outer.**  For a nonempty outer `D`, `ω.compose (translate u D)`
is the translate of `ω.compose D` by `ω.outerShift u`. -/
theorem compose_translate_outer (u : ℤ × ℤ) {D : Diagram} (hD : D.Nonempty) (ω : MarkedInner) :
    ω.compose (SkewGluing.translate u D) =
      SkewGluing.translate (ω.outerShift u) (ω.compose D) := by
  have hD' : (SkewGluing.translate u D).Nonempty := hD.image _
  have reindex : ∀ P : ℤ × ℤ → Prop,
      (∃ d ∈ SkewGluing.translate u D, P d) ↔ ∃ d ∈ D, P (d + u) := by
    intro P
    constructor
    · rintro ⟨d', hd', hP⟩
      exact ⟨d' - u, mem_translate.mp hd', by simpa using hP⟩
    · rintro ⟨d, hd, hP⟩
      exact ⟨d + u, mem_translate.mpr (by simpa using hd), hP⟩
  ext x
  rw [mem_translate, mem_compose hD', mem_compose hD, reindex, reindex]
  apply or_congr
  · refine exists_congr fun d => and_congr_right fun hd => ?_
    rw [origin_translate_outer hd, mem_translate, mem_translate]
    have e : x - (ω.origin D d + ω.outerShift u) = x - ω.outerShift u - ω.origin D d := by abel
    rw [e]
  · refine exists_congr fun d => and_congr_right fun hd => ?_
    rw [sameRibbon_translate_outer hd, origin_translate_outer hd, mem_translate, mem_translate]
    have e : x - (ω.origin D d + ω.outerShift u + ω.supplementalShift) =
        x - ω.outerShift u - (ω.origin D d + ω.supplementalShift) := by abel
    rw [e]

/-! ### Rotation and composition -/

@[simp] theorem rotate_case (ω : MarkedInner) : ω.rotate.case = ω.case.rotate := rfl

@[simp] theorem rotate_v (ω : MarkedInner) : ω.rotate.v = ω.v := rfl

@[simp] theorem rotate_E (ω : MarkedInner) : ω.rotate.E = SkewGluing.rotate ω.E := rfl

theorem content_neg_cell (d : ℤ × ℤ) : content (-d) = -content d := by
  simp only [content, Prod.fst_neg, Prod.snd_neg]; ring

/-- The copy origin of the rotated inner at the rotated cell is the negated origin. -/
theorem origin_rotate (D : Diagram) (d : ℤ × ℤ) (ω : MarkedInner) :
    ω.rotate.origin (SkewGluing.rotate D) (-d) = -ω.origin D d := by
  have hc := content_neg_cell d
  unfold origin
  rw [rotate_case, rotate_v]
  cases ω.case
  · simp only [AttachCase.rotate, hc, Prod.fst_neg]; module
  · simp only [AttachCase.rotate, hc, Prod.fst_neg]; module
  · simp only [AttachCase.rotate, hc, Prod.fst_neg, diagHi_rotate, neg_neg]; module
  · simp only [AttachCase.rotate, hc, Prod.fst_neg, diagLo_rotate]; module

theorem supplementalShift_rotate {ω : MarkedInner} (h : ω.case.IsMixed) :
    ω.rotate.supplementalShift = -ω.supplementalShift := by
  unfold supplementalShift
  rw [rotate_case]
  rcases h with h | h <;> rw [h] <;> ext <;> simp [AttachCase.rotate, eCell]

theorem case_mixed_of_sameRibbon {ω : MarkedInner} {D : Diagram} {d : ℤ × ℤ}
    (h : ω.SameRibbon D d) : ω.case.IsMixed := by
  by_contra hn
  exact sameRibbon_of_ordinary hn D d h

/-- On the same boundary ribbon, the origin of the cell directly north is the origin of the
cell plus the displacement `v`. -/
theorem origin_north {ω : MarkedInner} {D : Diagram} {d : ℤ × ℤ} (h : ω.SameRibbon D d) :
    ω.origin D (d.1 - 1, d.2) = ω.origin D d + ω.v := by
  obtain ⟨-, hr⟩ := h
  have hc : content (d.1 - 1, d.2) = content d + 1 := by simp only [content]; ring
  unfold origin
  cases hcs : ω.case
  · simp [hcs] at hr
  · simp [hcs] at hr
  · simp only [hcs] at hr ⊢
    rw [hc, ← hr]
    module
  · simp only [hcs] at hr ⊢
    rw [hc, hr]
    module

theorem sameRibbon_rotate {D : Diagram} {d : ℤ × ℤ} (ω : MarkedInner) (hd : d ∈ D)
    (hn : (d.1 - 1, d.2) ∈ D) :
    ω.rotate.SameRibbon (SkewGluing.rotate D) (-(d.1 - 1, d.2)) ↔ ω.SameRibbon D d := by
  have hmem : ((-(d.1 - 1, d.2)).1 - 1, (-(d.1 - 1, d.2)).2) ∈ SkewGluing.rotate D := by
    rw [mem_rotate]
    have : -((-(d.1 - 1, d.2)).1 - 1, (-(d.1 - 1, d.2)).2) = d := by
      ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring
    rw [this]; exact hd
  have hk : content (-(d.1 - 1, d.2)) = -content d - 1 := by simp [content]; ring
  have hk' : content (-(d.1 - 1, d.2)) = -(content d + 1) := by rw [hk]; ring
  unfold SameRibbon
  rw [rotate_case]
  cases hcs : ω.case
  · simp only [AttachCase.rotate, hmem, hn, true_and]
  · simp only [AttachCase.rotate, hmem, hn, true_and]
  · simp only [AttachCase.rotate, hmem, hn, true_and]
    rw [hk, diagHi_rotate, diagHi_rotate, show -(-content d - 1) = content d + 1 by ring,
      show -(-content d - 1 + 1) = content d by ring]
    simp only [Prod.fst_neg]
    omega
  · simp only [AttachCase.rotate, hmem, hn, true_and]
    rw [hk', show -(content d + 1) + 1 = -content d by ring, diagLo_rotate,
      show -content d = -(content d) from rfl, diagLo_rotate]
    simp only [Prod.fst_neg]
    omega

/-- **Rotation and composition.**  For a nonempty outer `D`, composing the rotated inner with the
rotated outer is the rotation of the composite: `ω.rotate.compose (rotate D) =
rotate (ω.compose D)`, as sets of cells (the supplemental copies are matched through the
ribbon pairs, the lower cell of a rotated pair being the upper cell of the original). -/
theorem rotate_compose {D : Diagram} (hD : D.Nonempty) (ω : MarkedInner) :
    ω.rotate.compose (SkewGluing.rotate D) = SkewGluing.rotate (ω.compose D) := by
  have hD' : (SkewGluing.rotate D).Nonempty := hD.image _
  ext x
  rw [mem_rotate, mem_compose hD', mem_compose hD]
  apply or_congr
  · constructor
    · rintro ⟨d', hd', hx⟩
      obtain ⟨d, rfl⟩ : ∃ d, d' = -d := ⟨-d', (neg_neg _).symm⟩
      refine ⟨d, by simpa [mem_rotate] using hd', ?_⟩
      rw [rotate_E, origin_rotate, mem_translate, mem_rotate] at hx
      rw [mem_translate]
      have e : -(x - -ω.origin D d) = -x - ω.origin D d := by abel
      rwa [e] at hx
    · rintro ⟨d, hd, hx⟩
      refine ⟨-d, by rw [mem_rotate, neg_neg]; exact hd, ?_⟩
      rw [rotate_E, origin_rotate, mem_translate, mem_rotate]
      rw [mem_translate] at hx
      have e : -(x - -ω.origin D d) = -x - ω.origin D d := by abel
      rwa [e]
  · constructor
    · rintro ⟨d', hd', hr, hx⟩
      obtain ⟨d, rfl⟩ : ∃ d : ℤ × ℤ, d' = -(d.1 - 1, d.2) :=
        ⟨-(d'.1 - 1, d'.2), by
          ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring⟩
      have hn : (d.1 - 1, d.2) ∈ D := by simpa [mem_rotate] using hd'
      have hd0 : d ∈ D := by
        have := hr.1
        rw [mem_rotate] at this
        have e : -((-(d.1 - 1, d.2)).1 - 1, (-(d.1 - 1, d.2)).2) = d := by
          ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring
        rwa [e] at this
      have hr' := (sameRibbon_rotate ω hd0 hn).mp hr
      have hmix := case_mixed_of_sameRibbon hr'
      refine ⟨d, hd0, hr', ?_⟩
      rw [origin_rotate, supplementalShift_rotate hmix, upper_rotate, origin_north hr',
        mem_translate, mem_rotate] at hx
      rw [mem_translate]
      have : ω.upper = SkewGluing.translate ω.v ω.W := rfl
      rw [this, mem_translate]
      have e : -(x - (-(ω.origin D d + ω.v) + -ω.supplementalShift)) =
          -x - (ω.origin D d + ω.supplementalShift) - ω.v := by abel
      rwa [e] at hx
    · rintro ⟨d, hd, hr, hx⟩
      have hn : (d.1 - 1, d.2) ∈ D := hr.1
      have hmix := case_mixed_of_sameRibbon hr
      refine ⟨-(d.1 - 1, d.2), by rw [mem_rotate, neg_neg]; exact hn,
        (sameRibbon_rotate ω hd hn).mpr hr, ?_⟩
      rw [origin_rotate, supplementalShift_rotate hmix, upper_rotate, origin_north hr,
        mem_translate, mem_rotate]
      rw [mem_translate] at hx
      have : ω.upper = SkewGluing.translate ω.v ω.W := rfl
      rw [this, mem_translate] at hx
      have e : -(x - (-(ω.origin D d + ω.v) + -ω.supplementalShift)) =
          -x - (ω.origin D d + ω.supplementalShift) - ω.v := by abel
      rwa [e]

/-- Rotation and composition for an arbitrary outer: the two sides agree up to translation (the
empty outer is the only case that needs a nonzero vector, `-v`). -/
theorem rotate_compose_translate (D : Diagram) (ω : MarkedInner) :
    ∃ t : ℤ × ℤ, ω.rotate.compose (SkewGluing.rotate D) =
      SkewGluing.translate t (SkewGluing.rotate (ω.compose D)) := by
  rcases D.eq_empty_or_nonempty with h | h
  · subst h
    refine ⟨-ω.v, ?_⟩
    have h0 : SkewGluing.rotate (∅ : Diagram) = ∅ := by simp [SkewGluing.rotate]
    have hc : ∀ ω' : MarkedInner, ω'.compose ∅ = ω'.W := fun ω' => by simp [compose]
    rw [h0, hc, hc]
    ext y
    change y ∈ SkewGluing.rotate ω.upper ↔ _
    rw [mem_translate, mem_rotate, mem_rotate]
    have e : -(y - -ω.v) = -y - ω.v := by abel
    rw [e]
    exact mem_translate
  · exact ⟨0, by rw [rotate_compose h, SkewGluing.translate_zero]⟩

end MarkedInner

/-! ### Fibers up to translation -/

section Fiber

variable {R : Type*} (s : Diagram → R)

/-- The fiber `𝓕(ω, Q)` read up to translation, as the paper reads diagrams: all translates of the
members of `fiber s ω Q`. -/
def fiberClass (ω : MarkedInner) (Q : R) : Set Diagram :=
  {F | ∃ F' ∈ fiber s ω Q, ∃ t : ℤ × ℤ, F = translate t F'}

theorem subset_fiberClass {ω : MarkedInner} {Q : R} {F : Diagram} (hF : F ∈ fiber s ω Q) :
    F ∈ fiberClass s ω Q :=
  ⟨F, hF, 0, (translate_zero).symm⟩

/-- Translating the marked inner moves every member of the fiber to a member of the translated
fiber, by a translation. -/
theorem fiber_translate_inner (u : ℤ × ℤ) {ω : MarkedInner} {Q : R} {F : Diagram}
    (hF : F ∈ fiber s ω Q) : ∃ t : ℤ × ℤ, translate t F ∈ fiber s (ω.translate u) Q := by
  obtain ⟨A, hA, hc2, hQ, hF⟩ := hF
  rcases hF with rfl | rfl
  · refine ⟨u, A, hA, hc2, hQ, Or.inl ?_⟩
    rw [MarkedInner.compose_translate]
  · refine ⟨-u, A, hA, hc2, hQ, Or.inr ?_⟩
    rw [MarkedInner.rotate_translate, MarkedInner.compose_translate]

/-- **The fiber is invariant under translating the marked inner**, in the sense in which the
paper reads diagrams up to translation: `𝓕(ω.translate u, Q)` and `𝓕(ω, Q)` have the same
translation classes.  No property of the outer function is needed. -/
theorem fiberClass_translate_inner (u : ℤ × ℤ) (ω : MarkedInner) (Q : R) :
    fiberClass s (ω.translate u) Q = fiberClass s ω Q := by
  have key : ∀ (u : ℤ × ℤ) (ω : MarkedInner),
      fiberClass s ω Q ⊆ fiberClass s (ω.translate u) Q := by
    rintro u ω F ⟨F', hF', t, rfl⟩
    obtain ⟨t', ht'⟩ := fiber_translate_inner s u hF'
    refine ⟨_, ht', -t' + t, ?_⟩
    rw [translate_translate]
    congr 1
    abel
  apply Set.Subset.antisymm
  · intro F hF
    have := key (-u) (ω.translate u) hF
    rwa [MarkedInner.translate_neg_translate] at this
  · exact key u ω

/-- Translating the outer gives a member of the fiber that is a translate of the original, so the
class of the fiber does not depend on the position of the outer. -/
theorem compose_translate_outer_mem_fiberClass {ω : MarkedInner} {Q : R} {A : Diagram}
    (hA : IsConnectedSkew A) (hc2 : 2 ≤ A.card) (hQ : s A = Q)
    (hs : ∀ (t : ℤ × ℤ) (B : Diagram), s (translate t B) = s B) (u : ℤ × ℤ) :
    ω.compose (translate u A) ∈ fiberClass s ω Q ∧
      ω.rotate.compose (translate u A) ∈ fiberClass s ω Q := by
  have hne : A.Nonempty := hA.2.1
  have hA' : IsConnectedSkew (translate u A) := isConnectedSkew_translate u hA
  have hc2' : 2 ≤ (translate u A).card := by
    rw [translate, Finset.card_image_of_injective _ (add_left_injective u)]; exact hc2
  have hQ' : s (translate u A) = Q := by rw [hs, hQ]
  refine ⟨subset_fiberClass s ⟨_, hA', hc2', hQ', Or.inl rfl⟩,
    subset_fiberClass s ⟨_, hA', hc2', hQ', Or.inr rfl⟩⟩

/-- **The fiber is determined by southwest-normalized outers.**  For a translation-invariant outer
function, the translation class of `𝓕(ω, Q)` consists of the translates of `A ∘_ω E` and
`A ∘_{ω*} E*` for connected `A` with `|A| ≥ 2`, `s A = Q` and `sw(A) = (0, 0)`. -/
theorem fiberClass_eq_normalized (hs : ∀ (t : ℤ × ℤ) (B : Diagram), s (translate t B) = s B)
    (ω : MarkedInner) (Q : R) :
    fiberClass s ω Q = {F | ∃ A : Diagram, IsConnectedSkew A ∧ 2 ≤ A.card ∧ s A = Q ∧
      sw A = 0 ∧ ((∃ t : ℤ × ℤ, F = translate t (ω.compose A)) ∨
        ∃ t : ℤ × ℤ, F = translate t (ω.rotate.compose A))} := by
  ext F
  constructor
  · rintro ⟨F', ⟨A, hA, hc2, hQ, hF'⟩, t, rfl⟩
    have hne : A.Nonempty := hA.2.1
    set A₀ := translate (-sw A) A with hA₀
    have hA₀c : IsConnectedSkew A₀ := isConnectedSkew_translate _ hA
    have hsw : sw A₀ = 0 := by
      rw [hA₀, sw_translate hne]; abel
    have hcard : A₀.card = A.card := by
      rw [hA₀, translate, Finset.card_image_of_injective _ (add_left_injective _)]
    have hA_eq : A = translate (sw A) A₀ := by
      rw [hA₀, translate_translate, add_neg_cancel, translate_zero]
    refine ⟨A₀, hA₀c, by rw [hcard]; exact hc2, by rw [hA₀, hs, hQ], hsw, ?_⟩
    rcases hF' with rfl | rfl
    · left
      refine ⟨t + MarkedInner.outerShift ω (sw A), ?_⟩
      have := MarkedInner.compose_translate_outer (sw A) hA₀c.2.1 ω
      rw [← hA_eq] at this
      rw [this, translate_translate]
    · right
      refine ⟨t + MarkedInner.outerShift ω.rotate (sw A), ?_⟩
      have := MarkedInner.compose_translate_outer (sw A) hA₀c.2.1 ω.rotate
      rw [← hA_eq] at this
      rw [this, translate_translate]
  · rintro ⟨A, hA, hc2, hQ, -, h | h⟩
    · obtain ⟨t, rfl⟩ := h
      exact ⟨ω.compose A, ⟨A, hA, hc2, hQ, Or.inl rfl⟩, t, rfl⟩
    · obtain ⟨t, rfl⟩ := h
      exact ⟨ω.rotate.compose A, ⟨A, hA, hc2, hQ, Or.inr rfl⟩, t, rfl⟩

/-- The fiber of the paper's outer function `s_A`, read up to translation, is invariant under
translating the marked inner. -/
theorem fiberClass_cellSchur_translate_inner (u : ℤ × ℤ) (ω : MarkedInner) (Q : Lambda) :
    fiberClass cellSchur (ω.translate u) Q = fiberClass cellSchur ω Q :=
  fiberClass_translate_inner cellSchur u ω Q

/-- The fiber of `s_A`, read up to translation, is determined by the southwest-normalized
outers. -/
theorem fiberClass_cellSchur_eq_normalized (ω : MarkedInner) (Q : Lambda) :
    fiberClass cellSchur ω Q = {F | ∃ A : Diagram, IsConnectedSkew A ∧ 2 ≤ A.card ∧
      cellSchur A = Q ∧ sw A = 0 ∧ ((∃ t : ℤ × ℤ, F = translate t (ω.compose A)) ∨
        ∃ t : ℤ × ℤ, F = translate t (ω.rotate.compose A))} :=
  fiberClass_eq_normalized cellSchur cellSchur_translate ω Q

end Fiber

/-! ### Checked examples -/

section Examples

open MarkedInner

example : (chartFigureInner.translate (3, -2)).IsLegal := by decide
example : (hookInner.translate (-4, 5)).IsLegal := by decide
example : (gaugeInnerB.translate (1, 1)).IsLegal := by decide +kernel

/-- A translated inner of the hook composes to the translate of the composite. -/
example : (hookInner.translate (2, 3)).compose (skewOf [3, 2] []) =
    translate (2, 3) (hookInner.compose (skewOf [3, 2] [])) := by decide +kernel

/-- Translating the outer moves the composite by `outerShift`: case (d), (c), (a), (b). -/
example : hookInner.compose (translate (2, 3) (skewOf [3, 2] [])) =
    translate (hookInner.outerShift (2, 3)) (hookInner.compose (skewOf [3, 2] [])) := by
  decide +kernel

example : hookInner.rotate.compose (translate (2, -3) (skewOf [3, 3, 1] [1])) =
    translate (hookInner.rotate.outerShift (2, -3))
      (hookInner.rotate.compose (skewOf [3, 3, 1] [1])) := by decide +kernel

example : chartFigureInner.compose (translate (2, 3) (skewOf [2, 2] [])) =
    translate (chartFigureInner.outerShift (2, 3))
      (chartFigureInner.compose (skewOf [2, 2] [])) := by decide +kernel

example : gaugeInnerB.compose (translate (-1, 4) (skewOf [2, 1] [])) =
    translate (gaugeInnerB.outerShift (-1, 4)) (gaugeInnerB.compose (skewOf [2, 1] [])) := by
  decide +kernel

/-- The offsets move by a vector depending on the content of the translation (the vectors are
visibly different in the ordinary and mixed cases). -/
example : chartFigureInner.outerShift (2, 3) = (1, 4) := by decide
example : hookInner.outerShift (2, 3) = (-1, 1) := by decide

/-- Rotation and composition on the hook (cases (d), (c)), the chart figure and a gauge inner. -/
example : hookInner.rotate.compose (rotate (skewOf [3, 2] [])) =
    rotate (hookInner.compose (skewOf [3, 2] [])) := by decide +kernel

example : hookInner.compose (rotate (skewOf [2, 2] [])) =
    rotate (hookInner.rotate.compose (skewOf [2, 2] [])) := by decide +kernel

example : chartFigureInner.rotate.compose (rotate (skewOf [2, 2] [])) =
    rotate (chartFigureInner.compose (skewOf [2, 2] [])) := by decide +kernel

example : gaugeInnerB.rotate.compose (rotate (skewOf [3, 2, 2] [1])) =
    rotate (gaugeInnerB.compose (skewOf [3, 2, 2] [1])) := by decide +kernel

end Examples

end SkewGluing
