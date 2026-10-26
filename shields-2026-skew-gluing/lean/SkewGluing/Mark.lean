import Mathlib.Algebra.Module.Prod
import SkewGluing.Diagram

/-!
# Marked inners and legality

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`), the definitions of a marked inner, the attachment cases (a)–(d), the legality
conditions I–IV, and the rotation `ω*` of a marked inner.

A marked inner is plain data `(E, W₋, v, case)`; the predicate `MarkedInner.IsLegal` asserts
that the data are a marked inner of the paper (well-formed, with the stated attachment case)
and satisfy I–IV.  Condition IV is stated in the bi-infinite form of the paper; its
finite-window equivalent (`noHatAdjacency_iff_window`) is what makes legality decidable.
The empty mark (`w = 0`) is the data `W₋ = ∅`, `v = v_H`, case (a).

Sorry-free.
-/

namespace SkewGluing

/-- The attachment case of a marked inner, in the order lower attachment, upper attachment:
(a) `(H, H)`, (b) `(V, V)`, (c) `(H, V)`, (d) `(V, H)`. -/
inductive AttachCase
  | a | b | c | d
  deriving DecidableEq, Repr

namespace AttachCase

/-- Ordinary cases are (a) and (b); mixed cases are (c) and (d). -/
def IsMixed (x : AttachCase) : Prop := x = c ∨ x = d

instance : DecidablePred IsMixed := fun x => by unfold IsMixed; infer_instance

/-- Rotation interchanges the roles of the two copies, hence of (c) and (d). -/
def rotate : AttachCase → AttachCase
  | a => a
  | b => b
  | c => d
  | d => c

theorem rotate_rotate (x : AttachCase) : x.rotate.rotate = x := by cases x <;> rfl

end AttachCase

/-- A marked inner: the diagram `E`, the lower copy `W₋ = W`, the displacement `v`, and the
attachment case.  The upper copy is `W₊ = W₋ + v`.  The empty mark (`w = 0`) is represented by
`W = ∅`, `v = vH E` and case (a). -/
structure MarkedInner where
  /-- The inner diagram `E`. -/
  E : Diagram
  /-- The lower copy `W₋`. -/
  W : Diagram
  /-- The displacement `v`, with `W₊ = W₋ + v`. -/
  v : ℤ × ℤ
  /-- The attachment case. -/
  case : AttachCase
  deriving DecidableEq

/-- The horizontal empty-overlap displacement `v_H = ne(E) - sw(E) + (0, 1)`. -/
def vH (E : Diagram) : ℤ × ℤ := ne E - sw E + (0, 1)

namespace MarkedInner

/-- The upper copy `W₊ = W₋ + v`. -/
def upper (ω : MarkedInner) : Diagram := translate ω.v ω.W

/-- The width `w = N_W`. -/
def width (ω : MarkedInner) : ℕ := span ω.W

/-- The period `q = c(v)` (which equals `N_E - w` for a legal mark). -/
def period (ω : MarkedInner) : ℤ := content ω.v

/-- The middle `O = E \ (W₋ ∪ W₊)`. -/
def middle (ω : MarkedInner) : Diagram := ω.E \ (ω.W ∪ ω.upper)

/-- The lower attachment is horizontal: the southwest cell of `O` (the cell of least content)
has its western neighbor in `W₋`. -/
def LowerH (ω : MarkedInner) : Prop :=
  ∃ x ∈ ω.middle, content x = minContent ω.middle ∧ (x.1, x.2 - 1) ∈ ω.W

/-- The lower attachment is vertical: the southwest cell of `O` has its southern neighbor in
`W₋`. -/
def LowerV (ω : MarkedInner) : Prop :=
  ∃ x ∈ ω.middle, content x = minContent ω.middle ∧ (x.1 + 1, x.2) ∈ ω.W

/-- The upper attachment is horizontal: the northeast cell of `O` has its eastern neighbor in
`W₊`. -/
def UpperH (ω : MarkedInner) : Prop :=
  ∃ x ∈ ω.middle, content x = maxContent ω.middle ∧ (x.1, x.2 + 1) ∈ ω.upper

/-- The upper attachment is vertical: the northeast cell of `O` has its northern neighbor in
`W₊`. -/
def UpperV (ω : MarkedInner) : Prop :=
  ∃ x ∈ ω.middle, content x = maxContent ω.middle ∧ (x.1 - 1, x.2) ∈ ω.upper

instance (ω : MarkedInner) : Decidable ω.LowerH := by unfold LowerH; infer_instance
instance (ω : MarkedInner) : Decidable ω.LowerV := by unfold LowerV; infer_instance
instance (ω : MarkedInner) : Decidable ω.UpperH := by unfold UpperH; infer_instance
instance (ω : MarkedInner) : Decidable ω.UpperV := by unfold UpperV; infer_instance

/-- The stated attachment case is the actual attachment of `E`, `W₋`, `W₊`. -/
def AttachmentMatches (ω : MarkedInner) : Prop :=
  (ω.case = .a → ω.LowerH ∧ ω.UpperH) ∧ (ω.case = .b → ω.LowerV ∧ ω.UpperV) ∧
  (ω.case = .c → ω.LowerH ∧ ω.UpperV) ∧ (ω.case = .d → ω.LowerV ∧ ω.UpperH)

instance (ω : MarkedInner) : Decidable ω.AttachmentMatches := by
  unfold AttachmentMatches; infer_instance

/-- The data of the empty mark on `E`: no copies, the horizontal displacement, case (a). -/
def IsEmptyMark (ω : MarkedInner) : Prop :=
  ω.W = ∅ ∧ ω.v = vH ω.E ∧ ω.case = .a

/-- The data of a nonempty mark: connected end copies `W₋`, `W₊ = W₋ + v` inside `E`, the
lower copy containing `sw(E)`, the upper copy containing `ne(E)`, and the stated attachment
case being the actual one. -/
def IsNonemptyMark (ω : MarkedInner) : Prop :=
  ω.W.Nonempty ∧ IsConnectedSkew ω.W ∧ ω.W ⊆ ω.E ∧ ω.upper ⊆ ω.E ∧ sw ω.E ∈ ω.W ∧
    ne ω.E ∈ ω.upper ∧ ω.AttachmentMatches

/-- The data are a marked inner of the paper: `E` is connected skew, and the marks are either
the empty mark or a nonempty mark. -/
def IsWellFormed (ω : MarkedInner) : Prop :=
  IsConnectedSkew ω.E ∧ (ω.IsEmptyMark ∨ ω.IsNonemptyMark)

instance (ω : MarkedInner) : Decidable ω.IsEmptyMark := by unfold IsEmptyMark; infer_instance

instance (ω : MarkedInner) : Decidable ω.IsNonemptyMark := by
  unfold IsNonemptyMark; infer_instance

instance (ω : MarkedInner) : Decidable ω.IsWellFormed := by
  unfold IsWellFormed; infer_instance

/-! ### Conditions I–IV -/

/-- (I) Maximality: no strictly larger skew diagram containing `W₋`, on the same content
diagonals, has translates at both ends of `E`.  The lower translate is the diagram itself
(it contains `W₋ ∋ sw(E)`), and an upper translate containing `ne(E)` is determined by the cell
of the diagram sent to `ne(E)`. -/
def IsMaximal (ω : MarkedInner) : Prop :=
  ∀ W' ∈ ω.E.powerset, ω.W ⊂ W' → IsSkew W' → contents W' = contents ω.W →
    ∀ x ∈ W', ¬ translate (ne ω.E - x) W' ⊆ ω.E

/-- (II) `0 ≤ w < q`, equivalently an occupied diagonal between the two copies meets neither. -/
def IsNarrow (ω : MarkedInner) : Prop :=
  0 ≤ (ω.width : ℤ) ∧ (ω.width : ℤ) < ω.period

/-- (III) Removing either copy leaves a connected skew diagram. -/
def RemovalsConnected (ω : MarkedInner) : Prop :=
  IsConnectedSkew (ω.E \ ω.W) ∧ IsConnectedSkew (ω.E \ ω.upper)

/-- The bi-infinite union `𝐄 = ⋃_{k ∈ ℤ} (E + k v)`. -/
def periodicUnion (ω : MarkedInner) : Set (ℤ × ℤ) :=
  {x | ∃ k : ℤ, x - k • ω.v ∈ ω.E}

/-- The hatted middle `Ô₁ = {x ∈ O₁ : x + e ∈ O₁}` of a copy `O₁` of the middle. -/
def hatMiddle (O₁ : Diagram) : Set (ℤ × ℤ) :=
  {x | x ∈ O₁ ∧ x + eCell ∈ O₁}

/-- The hatted mark `Ŵ₁ = {x ∈ 𝐄 : x + e ∈ W₁} ∪ {x ∈ W₁ : x + e ∈ 𝐄}` of a marked copy `W₁`. -/
def hatMark (ω : MarkedInner) (W₁ : Diagram) : Set (ℤ × ℤ) :=
  {x | x ∈ ω.periodicUnion ∧ x + eCell ∈ W₁} ∪ {x | x ∈ W₁ ∧ x + eCell ∈ ω.periodicUnion}

/-- (IV) In `𝐄 = ⋃_k (E + k v)`, no copy of the hatted middle is adjacent (shares an edge)
with a copy of the hatted mark.  The copies of the middle are `O + k v` and the marked copies
are `W₋ + m v`, for `k, m ∈ ℤ`. -/
def NoHatAdjacency (ω : MarkedInner) : Prop :=
  ∀ k m : ℤ, ∀ x ∈ hatMiddle (translate (k • ω.v) ω.middle),
    ∀ y ∈ ω.hatMark (translate (m • ω.v) ω.W), ¬ CellAdj x y

/-- A marked inner is *legal* if it is a well-formed marked inner satisfying I–IV. -/
def IsLegal (ω : MarkedInner) : Prop :=
  ω.IsWellFormed ∧ ω.IsMaximal ∧ ω.IsNarrow ∧ ω.RemovalsConnected ∧ ω.NoHatAdjacency

/-! ### Content bookkeeping for a mark -/

theorem content_smul (k : ℤ) (v : ℤ × ℤ) : content (k • v) = k * content v := by
  simp [content]; ring

theorem mem_translate_smul {D : Diagram} {k : ℤ} {v x : ℤ × ℤ} :
    x ∈ translate (k • v) D ↔ x - k • v ∈ D := mem_translate

theorem cellAdj_sub {x y : ℤ × ℤ} (u : ℤ × ℤ) (h : CellAdj x y) : CellAdj (x - u) (y - u) := by
  rw [cellAdj_iff] at h ⊢
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

theorem content_sub (x u : ℤ × ℤ) : content (x - u) = content x - content u := by
  simp [content]; ring

theorem content_eCell_add (x : ℤ × ℤ) : content (x + eCell) = content x := by
  simp [content, eCell]

/-- Content bounds for a nonempty mark: with `c₀` the least content of `E`, the cells of `W₋`
have contents in `[c₀, c₀ + w - 1]` and those of `E` in `[c₀, c₀ + q + w - 1]`. -/
theorem IsNonemptyMark.content_bounds {ω : MarkedInner} (hE : IsConnectedSkew ω.E)
    (h : ω.IsNonemptyMark) :
    (∀ x ∈ ω.W, minContent ω.E ≤ content x ∧
      content x ≤ minContent ω.E + ω.width - 1) ∧
    (∀ x ∈ ω.E, minContent ω.E ≤ content x ∧
      content x ≤ minContent ω.E + ω.period + ω.width - 1) := by
  obtain ⟨hne, hW, hWE, hUE, hsw, hneU, -⟩ := h
  have hEne : ω.E.Nonempty := hE.2.1
  have hspan := span_eq_of_isConnectedSkew hW
  have hsub : ∀ {A B : Diagram}, A ⊆ B → contents A ⊆ contents B :=
    fun h => Finset.image_subset_image h
  have hmin : minContent ω.W = minContent ω.E := by
    apply le_antisymm
    · have : content (sw ω.E) ∈ contents ω.W := content_mem_contents hsw
      rw [content_sw hEne] at this
      exact minContent_le this
    · exact minContent_le (hsub hWE (minContent_mem hne))
  have hUne : ω.upper.Nonempty := hne.image _
  have hmaxU : maxContent ω.upper = maxContent ω.W + content ω.v :=
    maxContent_translate hne ω.v
  have hmax : maxContent ω.E = maxContent ω.upper := by
    apply le_antisymm
    · have : content (ne ω.E) ∈ contents ω.upper := content_mem_contents hneU
      rw [content_ne hEne] at this
      exact le_maxContent this
    · exact le_maxContent (hsub hUE (maxContent_mem hUne))
  have hq : ω.period = content ω.v := rfl
  constructor
  · intro x hx
    have h1 := minContent_le (content_mem_contents hx)
    have h2 := le_maxContent (content_mem_contents hx)
    unfold MarkedInner.width
    omega
  · intro x hx
    have h1 := minContent_le (content_mem_contents hx)
    have h2 := le_maxContent (content_mem_contents hx)
    unfold MarkedInner.width
    omega

/-- The greatest content of `E` is that of `W₊`: `max E = max W₋ + c(v)`. -/
theorem IsNonemptyMark.maxContent_eq {ω : MarkedInner} (hE : IsConnectedSkew ω.E)
    (h : ω.IsNonemptyMark) : maxContent ω.E = maxContent ω.W + content ω.v := by
  obtain ⟨hne, hW, hWE, hUE, hsw, hneU, -⟩ := h
  have hEne : ω.E.Nonempty := hE.2.1
  have hsub : ∀ {A B : Diagram}, A ⊆ B → contents A ⊆ contents B :=
    fun h => Finset.image_subset_image h
  have hUne : ω.upper.Nonempty := hne.image _
  have hmaxU : maxContent ω.upper = maxContent ω.W + content ω.v :=
    maxContent_translate hne ω.v
  have : maxContent ω.E = maxContent ω.upper := by
    apply le_antisymm
    · have : content (ne ω.E) ∈ contents ω.upper := content_mem_contents hneU
      rw [content_ne hEne] at this
      exact le_maxContent this
    · exact le_maxContent (hsub hUE (maxContent_mem hUne))
  omega

/-- The northeast cell is the only cell of `E` of greatest content. -/
theorem eq_ne_of_content {E : Diagram} (hE : IsConnectedSkew E) {z : ℤ × ℤ} (hz : z ∈ E)
    (hc : content z = maxContent E) : z = ne E := by
  have h' := isConnectedSkew_iff_diagonal.mp hE
  have sing1 : diagLo E (maxContent E) = diagHi E (maxContent E) :=
    h'.2.2.2.2 _ (maxContent_mem h'.1)
      (Or.inr (fun hm => by have := le_maxContent hm; omega))
  have h1 := diagLo_le hz hc
  have h2 := le_diagHi hz hc
  obtain ⟨a, b⟩ := z
  simp only [content] at hc
  simp only [ne, Prod.mk.injEq]
  omega

/-- The southwest cell is the only cell of `E` of least content. -/
theorem eq_sw_of_content {E : Diagram} (hE : IsConnectedSkew E) {z : ℤ × ℤ} (hz : z ∈ E)
    (hc : content z = minContent E) : z = sw E := by
  have h' := isConnectedSkew_iff_diagonal.mp hE
  have sing0 : diagLo E (minContent E) = diagHi E (minContent E) :=
    h'.2.2.2.2 _ (minContent_mem h'.1)
      (Or.inl (fun hm => by have := minContent_le hm; omega))
  have h1 := diagLo_le hz hc
  have h2 := le_diagHi hz hc
  obtain ⟨a, b⟩ := z
  simp only [content] at hc
  simp only [sw, Prod.mk.injEq]
  omega

theorem middle_index {c0 q w xc yc k m : ℤ} (hwq : w < q)
    (hx1 : c0 ≤ xc - k * q) (hx2 : xc - k * q ≤ c0 + q + w - 1)
    (hy1 : c0 ≤ yc - m * q) (hy2 : yc - m * q ≤ c0 + w - 1)
    (hadj : xc = yc + 1 ∨ yc = xc + 1) : -1 ≤ k - m ∧ k - m ≤ 0 := by
  have e : (k - m) * q = k * q - m * q := by ring
  have e2 : (k - m + 1) * q = k * q - m * q + q := by ring
  constructor
  · by_contra h
    have h' : k - m + 1 ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_right h' (by omega : 0 ≤ q)
    omega
  · by_contra h
    have h' : 1 ≤ k - m := by omega
    have := mul_le_mul_of_nonneg_right h' (by omega : 0 ≤ q)
    omega

theorem periodic_index {c0 q w yc j : ℤ} (hw : 0 ≤ w) (hwq : w < q)
    (hy1 : c0 ≤ yc) (hy2 : yc ≤ c0 + w - 1)
    (h3 : c0 ≤ yc - j * q) (h4 : yc - j * q ≤ c0 + q + w - 1) : -1 ≤ j ∧ j ≤ 0 := by
  constructor
  · by_contra h
    have h' : j ≤ -2 := by omega
    have := mul_le_mul_of_nonneg_right h' (by omega : 0 ≤ q)
    omega
  · by_contra h
    have h' : 1 ≤ j := by omega
    have := mul_le_mul_of_nonneg_right h' (by omega : 0 ≤ q)
    omega

/-- The finite window of cells of `𝐄` that meet the hatted mark `Ŵ₋`: the copies `E` and
`E - v`. -/
def windowCells (ω : MarkedInner) : Diagram := ω.E ∪ translate (-ω.v) ω.E

/-- The finite window of the hatted mark `Ŵ₋`. -/
def hatMarkWindow (ω : MarkedInner) : Diagram :=
  (ω.windowCells.filter fun x => x + eCell ∈ ω.W) ∪
    (ω.W.filter fun x => x + eCell ∈ ω.windowCells)

/-- A decidable finite-window form of IV: only the middle copies `O` and `O - v` and the
marked copy `W₋` can be adjacent, and only the copies `E`, `E - v` of `E` meet `Ŵ₋`. -/
def HatWindowClear (ω : MarkedInner) : Prop :=
  ∀ k ∈ ({-1, 0} : Finset ℤ),
    ∀ x ∈ (translate (k • ω.v) ω.middle).filter
        (fun x => x + eCell ∈ translate (k • ω.v) ω.middle),
      ∀ y ∈ ω.hatMarkWindow, ¬ CellAdj x y

instance (ω : MarkedInner) : Decidable ω.HatWindowClear := by
  unfold HatWindowClear; infer_instance

theorem noHatAdjacency_of_empty {ω : MarkedInner} (h : ω.W = ∅) : ω.NoHatAdjacency := by
  intro k m x _ y hy
  exfalso
  have hy' : y ∈ ω.hatMark (translate (m • ω.v) ω.W) := hy
  unfold hatMark at hy'
  simp [h, translate] at hy'

/-- **Finite-window form of IV.**  For a well-formed mark satisfying II, the bi-infinite
condition IV is equivalent to the decidable condition `HatWindowClear`. -/
theorem noHatAdjacency_iff_window {ω : MarkedInner} (hwf : ω.IsWellFormed)
    (hII : ω.IsNarrow) : ω.NoHatAdjacency ↔ ω.HatWindowClear := by
  obtain ⟨hE, hmark⟩ := hwf
  rcases hmark with hemp | hnon
  · have h := hemp.1
    have h1 := noHatAdjacency_of_empty h
    refine ⟨fun _ => ?_, fun _ => h1⟩
    intro k _ x _ y hy
    exfalso
    simp [hatMarkWindow, h] at hy
  have hb := hnon.content_bounds hE
  obtain ⟨hw0, hwq⟩ := hII
  set c0 := minContent ω.E with hc0
  constructor
  · intro h k hk x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [Finset.mem_filter] at hx
    have hy' : y ∈ ω.hatMark (translate ((0 : ℤ) • ω.v) ω.W) := by
      simp only [zero_smul, hatMark, translate_zero]
      simp only [hatMarkWindow, windowCells, Finset.mem_union, Finset.mem_filter] at hy
      rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
      · left
        refine ⟨?_, hy2⟩
        rcases hy1 with h1 | h1
        · exact ⟨0, by simpa using h1⟩
        · refine ⟨-1, ?_⟩
          have := mem_translate.mp h1
          simpa using this
      · right
        refine ⟨hy1, ?_⟩
        rcases hy2 with h1 | h1
        · exact ⟨0, by simpa using h1⟩
        · refine ⟨-1, ?_⟩
          have := mem_translate.mp h1
          simpa using this
    exact h k 0 x ⟨hx.1, hx.2⟩ y hy'
  · intro h k m x hx y hy hadj
    obtain ⟨hx1, hx2⟩ := hx
    have hxO := mem_translate.mp hx1
    have hxO2 := mem_translate.mp hx2
    have hO : ∀ z ∈ ω.middle, z ∈ ω.E := fun z hz => (Finset.mem_sdiff.mp hz).1
    simp only [MarkedInner.period] at hb hwq
    -- the content of `y` relative to the marked copy `W₋ + m v`
    have hyW : c0 ≤ content y - m * content ω.v ∧
        content y - m * content ω.v ≤ c0 + ω.width - 1 := by
      have key : ∀ z, z - m • ω.v ∈ ω.W → c0 ≤ content z - m * content ω.v ∧
          content z - m * content ω.v ≤ c0 + ω.width - 1 := by
        intro z hz
        have := hb.1 _ hz
        rw [content_sub, content_smul] at this
        exact this
      rcases hy with ⟨_, hy2⟩ | ⟨hy1, _⟩
      · have := key (y + eCell) (by
          have := mem_translate.mp hy2
          exact this)
        rw [content_eCell_add] at this
        exact this
      · exact key y (mem_translate.mp hy1)
    have hxE := hb.2 _ (hO _ hxO)
    rw [content_sub, content_smul] at hxE
    have hadj' := content_adj hadj
    obtain ⟨hk1, hk2⟩ := middle_index (c0 := c0) (q := content ω.v) (w := ω.width) hwq
      hxE.1 (by have := hxE.2; linarith) hyW.1 hyW.2 (by omega)
    have hk' : k - m ∈ ({-1, 0} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    -- periodic index of a cell of `𝐄` of the same content as `y`
    have pidx : ∀ (z : ℤ × ℤ) (j : ℤ), content z = content y → z - j • ω.v ∈ ω.E →
        -1 ≤ j - m ∧ j - m ≤ 0 := by
      intro z j hzc hz
      have h1 := hb.2 _ hz
      rw [content_sub, content_smul, hzc] at h1
      have e : (j - m) * content ω.v = j * content ω.v - m * content ω.v := by ring
      exact periodic_index (c0 := c0) (q := content ω.v) (w := ω.width)
        (yc := content y - m * content ω.v) (j := j - m) hw0 hwq hyW.1 hyW.2
        (by rw [e]; linarith [h1.1]) (by rw [e]; linarith [h1.2])
    have inWindow : ∀ z : ℤ × ℤ, content z = content y → (∃ j : ℤ, z - j • ω.v ∈ ω.E) →
        z - m • ω.v ∈ ω.windowCells := by
      rintro z hzc ⟨j, hj⟩
      have hjr := pidx z j hzc hj
      simp only [windowCells, Finset.mem_union]
      have : j - m = -1 ∨ j - m = 0 := by omega
      rcases this with h0 | h0
      · right
        rw [mem_translate]
        have hjm : j = m - 1 := by omega
        subst hjm
        have e : z - m • ω.v - -ω.v = z - (m - 1) • ω.v := by rw [sub_smul, one_smul]; abel
        rw [e]; exact hj
      · left
        have hjm : j = m := by omega
        subst hjm
        exact hj
    refine h (k - m) hk' (x - m • ω.v) ?_ (y - m • ω.v) ?_ (cellAdj_sub _ hadj)
    · rw [Finset.mem_filter]
      constructor
      · rw [mem_translate_smul]
        have e : x - m • ω.v - (k - m) • ω.v = x - k • ω.v := by rw [sub_smul]; abel
        rw [e]; exact hxO
      · rw [mem_translate_smul]
        have e : x - m • ω.v + eCell - (k - m) • ω.v = x + eCell - k • ω.v := by
          rw [sub_smul]; abel
        rw [e]; exact hxO2
    · simp only [hatMarkWindow, Finset.mem_union, Finset.mem_filter]
      rcases hy with ⟨hyE, hyW1⟩ | ⟨hyW1, hyE⟩
      · refine Or.inl ⟨inWindow y rfl hyE, ?_⟩
        have := mem_translate.mp hyW1
        have e2 : y - m • ω.v + eCell = y + eCell - m • ω.v := by abel
        rw [e2]; exact this
      · refine Or.inr ⟨mem_translate.mp hyW1, ?_⟩
        have := inWindow (y + eCell) (content_eCell_add y) hyE
        have e2 : y + eCell - m • ω.v = y - m • ω.v + eCell := by abel
        rw [e2] at this; exact this

/-- Legality is decidable: IV is replaced by its finite-window form. -/
theorem isLegal_iff_window {ω : MarkedInner} :
    ω.IsLegal ↔ ω.IsWellFormed ∧ ω.IsMaximal ∧ ω.IsNarrow ∧ ω.RemovalsConnected ∧
      ω.HatWindowClear := by
  constructor
  · rintro ⟨hwf, hI, hII, hIII, hIV⟩
    exact ⟨hwf, hI, hII, hIII, (noHatAdjacency_iff_window hwf hII).mp hIV⟩
  · rintro ⟨hwf, hI, hII, hIII, hIV⟩
    exact ⟨hwf, hI, hII, hIII, (noHatAdjacency_iff_window hwf hII).mpr hIV⟩

instance (ω : MarkedInner) : Decidable ω.IsMaximal := by unfold IsMaximal; infer_instance
instance (ω : MarkedInner) : Decidable ω.IsNarrow := by unfold IsNarrow; infer_instance
instance (ω : MarkedInner) : Decidable ω.RemovalsConnected := by
  unfold RemovalsConnected; infer_instance

instance (ω : MarkedInner) : Decidable ω.IsLegal :=
  decidable_of_iff _ isLegal_iff_window.symm

end MarkedInner

/-! ### Rotation of a marked inner -/

theorem rotate_subset {A B : Diagram} (h : A ⊆ B) : rotate A ⊆ rotate B := by
  intro y hy
  rw [mem_rotate] at hy ⊢
  exact h hy

theorem rotate_sdiff (A B : Diagram) : rotate (A \ B) = rotate A \ rotate B := by
  ext y
  simp [mem_rotate]

theorem rotate_union (A B : Diagram) : rotate (A ∪ B) = rotate A ∪ rotate B := by
  ext y
  simp [mem_rotate]

theorem cellAdj_neg {x y : ℤ × ℤ} (h : CellAdj x y) : CellAdj (-x) (-y) := by
  rw [cellAdj_iff] at h ⊢
  simp only [Prod.fst_neg, Prod.snd_neg]
  omega

theorem cellAdj_neg_sub_eCell {x y : ℤ × ℤ} (h : CellAdj x y) :
    CellAdj (-x - eCell) (-y - eCell) := by
  rw [cellAdj_iff] at h ⊢
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, eCell]
  omega

theorem rotate_ssubset {A B : Diagram} (h : A ⊂ B) : rotate A ⊂ rotate B := by
  rw [Finset.ssubset_def] at h ⊢
  refine ⟨rotate_subset h.1, fun hh => h.2 ?_⟩
  intro y hy
  have h1 : -y ∈ rotate B := by rw [mem_rotate, neg_neg]; exact hy
  have h2 := hh h1
  rw [mem_rotate, neg_neg] at h2
  exact h2

theorem translate_ssubset (v : ℤ × ℤ) {A B : Diagram} (h : A ⊂ B) :
    translate v A ⊂ translate v B := by
  rw [Finset.ssubset_def] at h ⊢
  refine ⟨?_, fun hh => h.2 ?_⟩
  · intro y hy
    rw [mem_translate] at hy ⊢
    exact h.1 hy
  · intro y hy
    have := hh (mem_translate.mpr (by simpa using hy) : y + v ∈ translate v B)
    rw [mem_translate] at this
    simpa using this

namespace MarkedInner

/-- Rotation `ω*`: it rotates both end copies and interchanges their roles (the new lower copy
is the rotation of `W₊`), keeping the displacement; the attachment data are transported by
exchanging (c) and (d).  This is the representative obtained by negating all cells, so that
`ω** = ω` on the nose; any translate of it is the same rotation up to translation. -/
def rotate (ω : MarkedInner) : MarkedInner where
  E := SkewGluing.rotate ω.E
  W := SkewGluing.rotate ω.upper
  v := ω.v
  case := ω.case.rotate

theorem upper_rotate (ω : MarkedInner) : ω.rotate.upper = SkewGluing.rotate ω.W := by
  ext y
  simp only [upper, rotate, mem_translate, mem_rotate]
  have : -(y - ω.v) - ω.v = -y := by abel
  rw [this]

/-- Rotation is an involution. -/
theorem rotate_rotate (ω : MarkedInner) : ω.rotate.rotate = ω := by
  have h1 : ω.rotate.rotate.E = ω.E := SkewGluing.rotate_rotate
  have h2 : ω.rotate.rotate.W = ω.W := by
    change SkewGluing.rotate ω.rotate.upper = ω.W
    rw [upper_rotate, SkewGluing.rotate_rotate]
  have h3 : ω.rotate.rotate.case = ω.case := AttachCase.rotate_rotate _
  cases ω
  simp_all [rotate]

theorem middle_rotate (ω : MarkedInner) : ω.rotate.middle = SkewGluing.rotate ω.middle := by
  unfold middle
  rw [upper_rotate, rotate_sdiff, rotate_union]
  simp only [rotate, upper]
  rw [Finset.union_comm]

theorem width_rotate (ω : MarkedInner) : ω.rotate.width = ω.width := by
  simp only [width, rotate, upper, span_rotate, span_translate]

theorem period_rotate (ω : MarkedInner) : ω.rotate.period = ω.period := rfl

theorem exists_min_rotate {O S : Diagram} {f g : ℤ × ℤ → ℤ × ℤ}
    (hfg : ∀ y, f (-y) = -(g y)) :
    (∃ x ∈ SkewGluing.rotate O, content x = minContent (SkewGluing.rotate O) ∧
        f x ∈ SkewGluing.rotate S) ↔
      ∃ y ∈ O, content y = maxContent O ∧ g y ∈ S := by
  constructor
  · rintro ⟨x, hx, hc, hf⟩
    have hO : O.Nonempty := by
      rw [mem_rotate] at hx; exact ⟨-x, hx⟩
    rw [minContent_rotate hO] at hc
    refine ⟨-x, by rwa [mem_rotate] at hx, ?_, ?_⟩
    · simp only [content, Prod.fst_neg, Prod.snd_neg] at hc ⊢
      omega
    · rw [mem_rotate] at hf
      have := hfg (-x)
      rw [neg_neg] at this
      have h2 : g (-x) = -(f x) := by rw [this]; simp
      rw [h2]; exact hf
  · rintro ⟨y, hy, hc, hg⟩
    have hO : O.Nonempty := ⟨y, hy⟩
    refine ⟨-y, by rw [mem_rotate]; simpa using hy, ?_, ?_⟩
    · rw [minContent_rotate hO]
      simp only [content, Prod.fst_neg, Prod.snd_neg] at hc ⊢
      omega
    · rw [mem_rotate, hfg]
      simpa using hg

theorem exists_max_rotate {O S : Diagram} {f g : ℤ × ℤ → ℤ × ℤ}
    (hfg : ∀ y, f (-y) = -(g y)) :
    (∃ x ∈ SkewGluing.rotate O, content x = maxContent (SkewGluing.rotate O) ∧
        f x ∈ SkewGluing.rotate S) ↔
      ∃ y ∈ O, content y = minContent O ∧ g y ∈ S := by
  constructor
  · rintro ⟨x, hx, hc, hf⟩
    have hO : O.Nonempty := by
      rw [mem_rotate] at hx; exact ⟨-x, hx⟩
    rw [maxContent_rotate hO] at hc
    refine ⟨-x, by rwa [mem_rotate] at hx, ?_, ?_⟩
    · simp only [content, Prod.fst_neg, Prod.snd_neg] at hc ⊢
      omega
    · rw [mem_rotate] at hf
      have := hfg (-x)
      rw [neg_neg] at this
      have h2 : g (-x) = -(f x) := by rw [this]; simp
      rw [h2]; exact hf
  · rintro ⟨y, hy, hc, hg⟩
    have hO : O.Nonempty := ⟨y, hy⟩
    refine ⟨-y, by rw [mem_rotate]; simpa using hy, ?_, ?_⟩
    · rw [maxContent_rotate hO]
      simp only [content, Prod.fst_neg, Prod.snd_neg] at hc ⊢
      omega
    · rw [mem_rotate, hfg]
      simpa using hg

theorem lowerH_rotate (ω : MarkedInner) : ω.rotate.LowerH ↔ ω.UpperH := by
  unfold LowerH UpperH
  rw [middle_rotate]
  exact exists_min_rotate (O := ω.middle) (S := ω.upper) (f := fun x => (x.1, x.2 - 1))
    (g := fun y => (y.1, y.2 + 1)) (by intro y; simp; ring)

theorem lowerV_rotate (ω : MarkedInner) : ω.rotate.LowerV ↔ ω.UpperV := by
  unfold LowerV UpperV
  rw [middle_rotate]
  exact exists_min_rotate (O := ω.middle) (S := ω.upper) (f := fun x => (x.1 + 1, x.2))
    (g := fun y => (y.1 - 1, y.2)) (by intro y; simp; ring)

theorem upperH_rotate (ω : MarkedInner) : ω.rotate.UpperH ↔ ω.LowerH := by
  unfold UpperH LowerH
  rw [middle_rotate, upper_rotate]
  exact exists_max_rotate (O := ω.middle) (S := ω.W) (f := fun x => (x.1, x.2 + 1))
    (g := fun y => (y.1, y.2 - 1)) (by intro y; simp; ring)

theorem upperV_rotate (ω : MarkedInner) : ω.rotate.UpperV ↔ ω.LowerV := by
  unfold UpperV LowerV
  rw [middle_rotate, upper_rotate]
  exact exists_max_rotate (O := ω.middle) (S := ω.W) (f := fun x => (x.1 - 1, x.2))
    (g := fun y => (y.1 + 1, y.2)) (by intro y; simp; ring)

theorem attachmentMatches_rotate (ω : MarkedInner) :
    ω.rotate.AttachmentMatches ↔ ω.AttachmentMatches := by
  unfold AttachmentMatches
  rw [lowerH_rotate, lowerV_rotate, upperH_rotate, upperV_rotate]
  have : ω.rotate.case = ω.case.rotate := rfl
  rw [this]
  cases hc : ω.case <;> simp [AttachCase.rotate, and_comm]

theorem isEmptyMark_rotate {ω : MarkedInner} (hE : IsConnectedSkew ω.E)
    (h : ω.IsEmptyMark) : ω.rotate.IsEmptyMark := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp [rotate, upper, h1, SkewGluing.rotate, translate]
  · change ω.v = vH (SkewGluing.rotate ω.E)
    unfold vH
    rw [sw_rotate hE, ne_rotate hE, h2]
    unfold vH
    ext <;> simp <;> ring
  · change ω.case.rotate = .a
    rw [h3]; rfl

theorem isNonemptyMark_rotate {ω : MarkedInner} (hE : IsConnectedSkew ω.E)
    (h : ω.IsNonemptyMark) : ω.rotate.IsNonemptyMark := by
  obtain ⟨hne, hW, hWE, hUE, hsw, hneU, hatt⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (attachmentMatches_rotate ω).mpr hatt⟩
  · exact (hne.image _).image _
  · exact isConnectedSkew_rotate (isConnectedSkew_translate _ hW)
  · exact rotate_subset hUE
  · rw [upper_rotate]; exact rotate_subset hWE
  · change sw (SkewGluing.rotate ω.E) ∈ SkewGluing.rotate ω.upper
    rw [sw_rotate hE, mem_rotate, neg_neg]; exact hneU
  · change ne (SkewGluing.rotate ω.E) ∈ ω.rotate.upper
    rw [upper_rotate, ne_rotate hE, mem_rotate, neg_neg]; exact hsw

theorem isWellFormed_rotate {ω : MarkedInner} (h : ω.IsWellFormed) :
    ω.rotate.IsWellFormed := by
  obtain ⟨hE, hm⟩ := h
  refine ⟨isConnectedSkew_rotate hE, ?_⟩
  rcases hm with h | h
  · exact Or.inl (isEmptyMark_rotate hE h)
  · exact Or.inr (isNonemptyMark_rotate hE h)

theorem isNarrow_rotate {ω : MarkedInner} (h : ω.IsNarrow) : ω.rotate.IsNarrow := by
  unfold IsNarrow at *
  rw [width_rotate, period_rotate]; exact h

theorem mem_periodicUnion_rotate {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ ω.rotate.periodicUnion ↔ -x ∈ ω.periodicUnion := by
  simp only [periodicUnion, Set.mem_ofPred_eq, rotate, mem_rotate]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have e : -x - (-k) • ω.v = -(x - k • ω.v) := by rw [neg_smul]; abel
    rw [e]; exact hk
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have e : -(x - (-k) • ω.v) = -x - k • ω.v := by rw [neg_smul]; abel
    rw [e]; exact hk

/-- Rotation preserves condition IV. -/
theorem noHatAdjacency_rotate {ω : MarkedInner} (h : ω.NoHatAdjacency) :
    ω.rotate.NoHatAdjacency := by
  intro k m x hx y hy hadj
  have hmid : ∀ u : ℤ × ℤ, u ∈ translate (k • ω.rotate.v) ω.rotate.middle ↔
      -(u - k • ω.v) ∈ ω.middle := by
    intro u
    rw [middle_rotate, mem_translate, mem_rotate]; rfl
  have hmark : ∀ u : ℤ × ℤ, u ∈ translate (m • ω.rotate.v) ω.rotate.W ↔
      -(u - m • ω.v) - ω.v ∈ ω.W := by
    intro u
    change u ∈ translate (m • ω.v) (SkewGluing.rotate ω.upper) ↔ _
    rw [mem_translate, mem_rotate]
    unfold upper
    rw [mem_translate]
  obtain ⟨hx1, hx2⟩ := hx
  rw [hmid] at hx1 hx2
  refine h (-k) (1 - m) (-x - eCell) ⟨?_, ?_⟩ (-y - eCell) ?_ (cellAdj_neg_sub_eCell hadj)
  · rw [mem_translate_smul]
    have e : -x - eCell - (-k) • ω.v = -(x + eCell - k • ω.v) := by rw [neg_smul]; abel
    rw [e]; exact hx2
  · rw [mem_translate_smul]
    have e : -x - eCell + eCell - (-k) • ω.v = -(x - k • ω.v) := by rw [neg_smul]; abel
    rw [e]; exact hx1
  · rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · right
      refine ⟨?_, ?_⟩
      · rw [mem_translate_smul]
        have := (hmark _).mp hy2
        have e : -y - eCell - (1 - m) • ω.v = -(y + eCell - m • ω.v) - ω.v := by
          rw [sub_smul, one_smul]; abel
        rw [e]; exact this
      · have := mem_periodicUnion_rotate.mp hy1
        have e : -y - eCell + eCell = -y := by abel
        rw [e]; exact this
    · left
      refine ⟨?_, ?_⟩
      · have := mem_periodicUnion_rotate.mp hy2
        have e : -(y + eCell) = -y - eCell := by abel
        rw [e] at this; exact this
      · rw [mem_translate_smul]
        have := (hmark _).mp hy1
        have e : -y - eCell + eCell - (1 - m) • ω.v = -(y - m • ω.v) - ω.v := by
          rw [sub_smul, one_smul]; abel
        rw [e]; exact this

/-- Maximality at the prescribed displacement: no strictly larger skew diagram on the same
contents contains `W₋` with its translate by `v` still inside `E`. -/
def IsMaximalAtDisplacement (ω : MarkedInner) : Prop :=
  ∀ W' ∈ ω.E.powerset, ω.W ⊂ W' → IsSkew W' → contents W' = contents ω.W →
    ¬ translate ω.v W' ⊆ ω.E

theorem IsMaximal.atDisplacement {ω : MarkedInner} (hneU : ne ω.E ∈ ω.upper)
    (h : ω.IsMaximal) : ω.IsMaximalAtDisplacement := by
  intro W' hW' hlt hsk hc hsub
  have hy : ne ω.E - ω.v ∈ ω.W := by
    have := mem_translate.mp hneU
    exact this
  have := h W' hW' hlt hsk hc (ne ω.E - ω.v) (hlt.subset hy)
  apply this
  have e : ne ω.E - (ne ω.E - ω.v) = ω.v := by abel
  rw [e]; exact hsub

theorem IsMaximalAtDisplacement.isMaximal {ω : MarkedInner} (hE : IsConnectedSkew ω.E)
    (hnon : ω.IsNonemptyMark) (h : ω.IsMaximalAtDisplacement) : ω.IsMaximal := by
  have hmax := hnon.maxContent_eq hE
  obtain ⟨hne, hW, hWE, hUE, hsw, hneU, -⟩ := hnon
  intro W' hW' hlt hsk hc x hx hsub
  have hEne : ω.E.Nonempty := hE.2.1
  have hy : ne ω.E - ω.v ∈ ω.W := mem_translate.mp hneU
  have hyW' : ne ω.E - ω.v ∈ W' := hlt.subset hy
  -- the content of `u = ne E - x` is `c(v)`
  set u := ne ω.E - x with hu
  have hxW' : content x ≤ maxContent ω.W := by
    have h1 : content x ∈ contents W' := content_mem_contents hx
    rw [hc] at h1
    exact le_maxContent h1
  have hne1 : ne ω.E ∈ translate u W' := mem_translate.mpr (by
    have : ne ω.E - u = x := by rw [hu]; abel
    rw [this]; exact hx)
  have hcu : content u = content ω.v := by
    have hc1 : content (ne ω.E) = content x + content u := by
      have : ne ω.E = x + u := by rw [hu]; abel
      rw [this, content_add]
    have hc2 : content (ne ω.E) = maxContent ω.E := content_ne hEne
    have hy2 : ne ω.E - ω.v + u ∈ ω.E := by
      apply hsub
      exact mem_translate.mpr (by simpa using hyW')
    have h3 := le_maxContent (content_mem_contents hy2)
    rw [content_add, content_sub] at h3
    omega
  have hz : ne ω.E - ω.v + u ∈ ω.E := by
    apply hsub
    exact mem_translate.mpr (by simpa using hyW')
  have hzc : content (ne ω.E - ω.v + u) = maxContent ω.E := by
    rw [content_add, content_sub, hcu, content_ne hEne]; ring
  have hzne := eq_ne_of_content hE hz hzc
  have huv : u = ω.v := by
    have : ne ω.E - ω.v + u = ne ω.E := hzne
    have h2 : u - ω.v = 0 := by
      have : (ne ω.E - ω.v + u) - ne ω.E = 0 := by rw [this]; abel
      rw [← this]; abel
    exact sub_eq_zero.mp h2
  exact h W' hW' hlt hsk hc (huv ▸ hsub)

theorem isMaximalAtDisplacement_rotate {ω : MarkedInner}
    (h : ω.IsMaximalAtDisplacement) : ω.rotate.IsMaximalAtDisplacement := by
  intro X hX hlt hsk hc hsub
  have hXE : X ⊆ SkewGluing.rotate ω.E := Finset.mem_powerset.mp hX
  have hX1 : SkewGluing.rotate X ⊆ ω.E := by
    intro y hy
    rw [mem_rotate] at hy
    have := hXE hy
    rw [mem_rotate] at this
    simpa using this
  have hup : translate (-ω.v) ω.upper = ω.W := by
    unfold upper; rw [translate_translate]; simp [translate_zero]
  refine h (translate (-ω.v) (SkewGluing.rotate X)) ?_ ?_ ?_ ?_ ?_
  · rw [Finset.mem_powerset]
    intro z hz
    rw [mem_translate, mem_rotate] at hz
    have h1 : -(z - -ω.v) + ω.v ∈ translate ω.v X :=
      mem_translate.mpr (by rw [add_sub_cancel_right]; exact hz)
    have h2 := hsub h1
    change _ ∈ SkewGluing.rotate ω.E at h2
    rw [mem_rotate] at h2
    have e : -(-(z - -ω.v) + ω.v) = z := by abel
    rw [e] at h2; exact h2
  · rw [← hup]
    apply translate_ssubset
    have := rotate_ssubset (show SkewGluing.rotate ω.upper ⊂ X from hlt)
    rw [SkewGluing.rotate_rotate] at this
    exact this
  · exact isSkew_translate _ (isSkew_rotate hsk)
  · ext k
    rw [mem_contents_translate, mem_contents_rotate]
    have hc' : contents X = contents (SkewGluing.rotate ω.upper) := hc
    rw [hc', mem_contents_rotate, neg_neg, ← hup, mem_contents_translate]
  · intro z hz
    rw [translate_translate, add_neg_cancel, translate_zero] at hz
    exact hX1 hz

theorem isMaximal_of_empty {ω : MarkedInner} (h : ω.W = ∅) : ω.IsMaximal := by
  intro W' _ hlt _ hc
  exfalso
  rw [h] at hlt hc
  have : W' = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    have : content y ∈ contents W' := content_mem_contents hy
    rw [hc] at this
    simp [contents] at this
  rw [this] at hlt
  exact absurd hlt (Finset.not_ssubset_empty _)

/-- Rotation preserves condition I. -/
theorem isMaximal_rotate {ω : MarkedInner} (hwf : ω.IsWellFormed) (h : ω.IsMaximal) :
    ω.rotate.IsMaximal := by
  obtain ⟨hE, hm⟩ := hwf
  rcases hm with hemp | hnon
  · exact isMaximal_of_empty (isEmptyMark_rotate hE hemp).1
  · have hrot := isNonemptyMark_rotate hE hnon
    have hat := h.atDisplacement hnon.2.2.2.2.2.1
    exact (isMaximalAtDisplacement_rotate hat).isMaximal (isConnectedSkew_rotate hE) hrot

theorem removalsConnected_rotate {ω : MarkedInner} (h : ω.RemovalsConnected) :
    ω.rotate.RemovalsConnected := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · change IsConnectedSkew (SkewGluing.rotate ω.E \ SkewGluing.rotate ω.upper)
    rw [← rotate_sdiff]; exact isConnectedSkew_rotate h2
  · change IsConnectedSkew (SkewGluing.rotate ω.E \ ω.rotate.upper)
    rw [upper_rotate, ← rotate_sdiff]; exact isConnectedSkew_rotate h1

/-- Rotation preserves legality. -/
theorem isLegal_rotate {ω : MarkedInner} (h : ω.IsLegal) : ω.rotate.IsLegal :=
  ⟨isWellFormed_rotate h.1, isMaximal_rotate h.1 h.2.1, isNarrow_rotate h.2.2.1,
    removalsConnected_rotate h.2.2.2.1, noHatAdjacency_rotate h.2.2.2.2⟩

theorem isLegal_rotate_iff {ω : MarkedInner} : ω.rotate.IsLegal ↔ ω.IsLegal :=
  ⟨fun h => by simpa [rotate_rotate] using isLegal_rotate h, isLegal_rotate⟩

/-- The cells of `E` whose translate by `v` stays in `E`: `E ∩ (E - v)`. -/
def fullIntersection (ω : MarkedInner) : Diagram := ω.E.filter fun x => x + ω.v ∈ ω.E

theorem isSkew_fullIntersection {ω : MarkedInner} (hE : IsSkew ω.E) :
    IsSkew ω.fullIntersection := by
  intro x hx y hy h1 h2 i hi j hj
  simp only [fullIntersection, Finset.mem_filter] at hx hy ⊢
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Finset.mem_Icc] at hi hj
  refine ⟨hE.mem hx.1 hy.1 h1 h2 hi.1 hi.2 hj.1 hj.2, ?_⟩
  have hx2 : (a + ω.v.1, b + ω.v.2) ∈ ω.E := hx.2
  have hy2 : (c + ω.v.1, d + ω.v.2) ∈ ω.E := hy.2
  change (i + ω.v.1, j + ω.v.2) ∈ ω.E
  exact hE.mem hx2 hy2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **`lem:gluing-local` (1), first assertion.**  For a legal nonempty mark the copies are full
intersections: `W₋ = E ∩ (E - v)`. -/
theorem IsLegal.W_eq_fullIntersection {ω : MarkedInner} (h : ω.IsLegal)
    (hW : ω.W.Nonempty) : ω.W = ω.fullIntersection := by
  obtain ⟨⟨hE, hm⟩, hI, hII, -, -⟩ := h
  have hnon : ω.IsNonemptyMark := by
    rcases hm with h | h
    · exact absurd h.1 hW.ne_empty
    · exact h
  have hb := hnon.content_bounds hE
  have hmax := hnon.maxContent_eq hE
  obtain ⟨hne, hWsk, hWE, hUE, hsw, hneU, -⟩ := hnon
  have hsub : ω.W ⊆ ω.fullIntersection := by
    intro x hx
    simp only [fullIntersection, Finset.mem_filter]
    exact ⟨hWE hx, hUE (mem_translate.mpr (by simpa using hx))⟩
  by_contra hne'
  have hlt : ω.W ⊂ ω.fullIntersection := lt_of_le_of_ne hsub hne'
  have hspW := span_eq_of_isConnectedSkew hWsk
  have hEne : ω.E.Nonempty := hE.2.1
  have hmin : minContent ω.W = minContent ω.E := by
    have hs : contents ω.W ⊆ contents ω.E := Finset.image_subset_image hWE
    apply le_antisymm
    · have : content (sw ω.E) ∈ contents ω.W := content_mem_contents hsw
      rw [content_sw hEne] at this
      exact minContent_le this
    · exact minContent_le (hs (minContent_mem hne))
  have hcont : contents ω.fullIntersection = contents ω.W := by
    apply Finset.Subset.antisymm
    · intro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      simp only [fullIntersection, Finset.mem_filter] at hx
      have h1 := hb.2 x hx.1
      have h2 := hb.2 _ hx.2
      rw [content_add] at h2
      have hII' : (ω.width : ℤ) < ω.period := hII.2
      have hq : ω.period = content ω.v := rfl
      have hw : (ω.width : ℤ) = span ω.W := rfl
      have hW2 : maxContent ω.W = minContent ω.W + ω.width - 1 := by omega
      have h' := isConnectedSkew_iff_diagonal.mp hWsk
      rw [h'.mem_contents_iff]
      constructor <;> omega
    · exact Finset.image_subset_image hsub
  have hv : ω.fullIntersection ∈ ω.E.powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hy : ne ω.E - ω.v ∈ ω.W := mem_translate.mp hneU
  refine hI _ hv hlt (isSkew_fullIntersection hE.1) hcont (ne ω.E - ω.v) (hsub hy) ?_
  have e : ne ω.E - (ne ω.E - ω.v) = ω.v := by abel
  rw [e]
  intro z hz
  obtain ⟨y, hy', rfl⟩ := Finset.mem_image.mp hz
  simp only [fullIntersection, Finset.mem_filter] at hy'
  exact hy'.2

end MarkedInner

/-! ### Checked examples -/

section Examples

/-- The marked inner of the chart figure (`fig:chart`): case (a), `v = (-1, 2)`, `w = 2`,
`q = 3`.  The examples below check that it is legal, of width two and period three, with a middle
of two cells. -/
def chartFigureInner : MarkedInner where
  E := {(-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (0, 0)}
  W := {(-1, 0), (0, 0)}
  v := (-1, 2)
  case := .a

example : chartFigureInner.IsLegal := by decide
example : chartFigureInner.width = 2 ∧ chartFigureInner.period = 3 := by decide
example : chartFigureInner.middle.card = 2 := by decide

/-- The singleton case-(d) mark on the hook `(2, 1)`. -/
def hookInner : MarkedInner where
  E := skewOf [2, 1] []
  W := {(1, 0)}
  v := (-1, 1)
  case := .d

example : hookInner.IsLegal := by decide

/-- The singleton-overlap mark on the row `(3)`, period two. -/
def rowInnerThree : MarkedInner where
  E := skewOf [3] []
  W := {(0, 0)}
  v := (0, 2)
  case := .a

/-- The singleton-overlap mark on the row `(4)`, period three. -/
def rowInnerFour : MarkedInner where
  E := skewOf [4] []
  W := {(0, 0)}
  v := (0, 3)
  case := .a

example : rowInnerThree.IsLegal := by decide
example : rowInnerFour.IsLegal := by decide

/-- The empty mark on the row `(3)`. -/
def rowEmptyInner : MarkedInner where
  E := skewOf [3] []
  W := ∅
  v := (0, 3)
  case := .a

example : rowEmptyInner.IsLegal := by decide

/-- The ordinary mark `ω_a` on `E = (4, 4, 2) / (2)` (coordinates from zero). -/
def gaugeInnerA : MarkedInner where
  E := skewOf [4, 4, 2] [2]
  W := {(1, 0), (2, 0)}
  v := (-1, 3)
  case := .a

/-- The ordinary mark `ω_b` on `E = (4, 4, 2) / (2)` (coordinates from zero). -/
def gaugeInnerB : MarkedInner where
  E := skewOf [4, 4, 2] [2]
  W := {(2, 0), (2, 1)}
  v := (-2, 2)
  case := .b

example : gaugeInnerA.IsLegal := by decide +kernel
example : gaugeInnerB.IsLegal := by decide +kernel

/-- A non-example: the case (b) label is wrong for the data of `ω_a`. -/
example : ¬ ({ gaugeInnerA with case := .b } : MarkedInner).IsLegal := by decide

/-- A non-example: a width equal to the period violates II. -/
example : ¬ ({ E := skewOf [2] [], W := {(0, 0), (0, 1)}, v := (0, 1), case := .a } :
    MarkedInner).IsLegal := by decide

end Examples

end SkewGluing
