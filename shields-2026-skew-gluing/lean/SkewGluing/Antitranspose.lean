import SkewGluing.Composition

/-!
# Antitransposition of cells, diagrams and marked inners

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`eq:gluing-gauge`, and "antitransposition changes the bit pair to `(1 - B, 1 - A)`, giving case
(b)"), the antitransposition `AT` used by `prop:gluing-ordinary-fold` ("antitranspose the pair if
necessary") and by `lem:gluing-lines` (the column case).

* `atVec (i, j) = (-j, -i)`: antitransposition on cells.  It is additive, preserves contents, sends
  `e` to `-e` and preserves cell adjacency; `antitranspose` of a diagram commutes with
  translation, differences, unions and inclusion, and preserves cardinality, the extreme contents
  and the extreme cells `sw`, `ne`.
* `MarkedInner.anti ω`: the marked inner on `AT(E)` with copies `AT(W₋)`, displacement `AT(v)` and
  the attachment case exchanged `(a) ↔ (b)`, `(c) ↔ (d)` (`AttachCase.anti`).  It has the same
  period and width, and the conditions of legality transfer to it one by one: `isLegal_anti` says
  that a legal mark with a nonempty copy has a legal antitransposed mark.
* `MarkedInner.antitranspose_compose`: for an ordinary mark, `AT(D ∘_ω E) = D ∘_{ω^{AT}} AT(E)`
  with the same outer `D` (the origin `L_ω(d)` is carried to `L_{ω^{AT}}(d)` by `AT`).

Sorry-free.
-/

namespace SkewGluing

/-- The linear part of antitransposition `(a, b) ↦ (-b, -a)`. -/
def atVec (x : ℤ × ℤ) : ℤ × ℤ := (-x.2, -x.1)

theorem atVec_atVec (x : ℤ × ℤ) : atVec (atVec x) = x := by simp [atVec]

theorem atVec_add (x y : ℤ × ℤ) : atVec (x + y) = atVec x + atVec y := by
  ext <;> simp [atVec] <;> ring

theorem atVec_sub (x y : ℤ × ℤ) : atVec (x - y) = atVec x - atVec y := by
  ext <;> simp [atVec] <;> ring

theorem atVec_smul (n : ℤ) (x : ℤ × ℤ) : atVec (n • x) = n • atVec x := by
  ext <;> simp [atVec]

theorem atVec_eCell : atVec eCell = -eCell := by
  ext <;> simp [atVec, eCell]

theorem content_atVec (x : ℤ × ℤ) : content (atVec x) = content x :=
  content_antitranspose x

theorem atVec_neg (x : ℤ × ℤ) : atVec (-x) = -atVec x := by
  ext <;> simp [atVec]

theorem atVec_fst (x : ℤ × ℤ) : (atVec x).1 = -x.2 := rfl

theorem atVec_snd (x : ℤ × ℤ) : (atVec x).2 = -x.1 := rfl

theorem cellAdj_atVec_iff {x y : ℤ × ℤ} : CellAdj (atVec x) (atVec y) ↔ CellAdj x y := by
  simp only [cellAdj_iff, atVec_fst, atVec_snd]; omega

theorem mem_antitranspose' {D : Diagram} {y : ℤ × ℤ} : y ∈ antitranspose D ↔ atVec y ∈ D :=
  mem_antitranspose

theorem antitranspose_injective : Function.Injective antitranspose := fun A B h => by
  have := congrArg antitranspose h
  rwa [antitranspose_antitranspose, antitranspose_antitranspose] at this

theorem card_antitranspose (D : Diagram) : (antitranspose D).card = D.card := by
  unfold antitranspose
  exact Finset.card_image_of_injective _ (fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega))

theorem antitranspose_nonempty_iff {D : Diagram} : (antitranspose D).Nonempty ↔ D.Nonempty := by
  rw [← Finset.card_pos, ← Finset.card_pos, card_antitranspose]

theorem antitranspose_translate (t : ℤ × ℤ) (D : Diagram) :
    antitranspose (translate t D) = translate (atVec t) (antitranspose D) := by
  ext y
  rw [mem_antitranspose, mem_translate, mem_translate, mem_antitranspose]
  have e : (-y.2, -y.1) - t = (-(y - atVec t).2, -(y - atVec t).1) := by
    ext <;> simp [atVec] <;> ring
  rw [e]

theorem antitranspose_sdiff (A B : Diagram) :
    antitranspose (A \ B) = antitranspose A \ antitranspose B := by
  ext y; simp [mem_antitranspose]

theorem antitranspose_union (A B : Diagram) :
    antitranspose (A ∪ B) = antitranspose A ∪ antitranspose B := by
  ext y; simp [mem_antitranspose]

theorem antitranspose_subset {A B : Diagram} (h : A ⊆ B) : antitranspose A ⊆ antitranspose B := by
  intro y hy
  rw [mem_antitranspose] at hy ⊢
  exact h hy

theorem antitranspose_ssubset {A B : Diagram} (h : A ⊂ B) :
    antitranspose A ⊂ antitranspose B := by
  refine ⟨antitranspose_subset h.1, fun hh => h.2 ?_⟩
  intro y hy
  have := hh (show atVec y ∈ antitranspose B from by
    rw [mem_antitranspose]; simpa [atVec] using hy)
  rw [mem_antitranspose] at this
  simpa [atVec] using this

theorem minContent_antitranspose (D : Diagram) :
    minContent (antitranspose D) = minContent D := by
  unfold minContent
  rw [contents_antitranspose]

theorem maxContent_antitranspose (D : Diagram) :
    maxContent (antitranspose D) = maxContent D := by
  unfold maxContent
  rw [contents_antitranspose]

theorem sw_antitranspose {E : Diagram} (hE : IsConnectedSkew E) :
    sw (antitranspose E) = atVec (sw E) := by
  have hne := hE.2.1
  symm
  apply MarkedInner.eq_sw_of_content (isConnectedSkew_antitranspose hE)
  · rw [mem_antitranspose]
    simpa [atVec] using sw_mem hne
  · rw [minContent_antitranspose, content_atVec, content_sw hne]

theorem ne_antitranspose {E : Diagram} (hE : IsConnectedSkew E) :
    ne (antitranspose E) = atVec (ne E) := by
  have hne := hE.2.1
  symm
  apply MarkedInner.eq_ne_of_content (isConnectedSkew_antitranspose hE)
  · rw [mem_antitranspose]
    simpa [atVec] using ne_mem hne
  · rw [maxContent_antitranspose, content_atVec, content_ne hne]

namespace AttachCase

/-- Antitransposition exchanges horizontal and vertical attachments: (a) ↔ (b), (c) ↔ (d). -/
def anti : AttachCase → AttachCase
  | a => b
  | b => a
  | c => d
  | d => c

theorem anti_anti (x : AttachCase) : x.anti.anti = x := by cases x <;> rfl

theorem isMixed_anti {x : AttachCase} : x.anti.IsMixed ↔ x.IsMixed := by
  cases x <;> simp [anti, IsMixed]

end AttachCase

namespace MarkedInner

/-- Antitransposition of a marked inner: `E`, `W₋` and the displacement are antitransposed and
the attachment case is replaced by `AttachCase.anti`. -/
def anti (ω : MarkedInner) : MarkedInner where
  E := antitranspose ω.E
  W := antitranspose ω.W
  v := atVec ω.v
  case := ω.case.anti

@[simp] theorem anti_E (ω : MarkedInner) : ω.anti.E = antitranspose ω.E := rfl
@[simp] theorem anti_W (ω : MarkedInner) : ω.anti.W = antitranspose ω.W := rfl
@[simp] theorem anti_v (ω : MarkedInner) : ω.anti.v = atVec ω.v := rfl
@[simp] theorem anti_case (ω : MarkedInner) : ω.anti.case = ω.case.anti := rfl

theorem anti_anti (ω : MarkedInner) : ω.anti.anti = ω := by
  have h1 : ω.anti.anti.E = ω.E := antitranspose_antitranspose
  have h2 : ω.anti.anti.W = ω.W := antitranspose_antitranspose
  have h3 : ω.anti.anti.v = ω.v := atVec_atVec _
  have h4 : ω.anti.anti.case = ω.case := AttachCase.anti_anti _
  cases hω : ω
  simp_all [MarkedInner.anti]

theorem upper_anti (ω : MarkedInner) : ω.anti.upper = antitranspose ω.upper := by
  unfold upper
  simp only [anti_W, anti_v]
  rw [antitranspose_translate]

theorem middle_anti (ω : MarkedInner) : ω.anti.middle = antitranspose ω.middle := by
  unfold middle
  rw [upper_anti, anti_E, anti_W, antitranspose_sdiff, antitranspose_union]

theorem mem_middle_anti {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ ω.anti.middle ↔ atVec x ∈ ω.middle := by
  rw [middle_anti, mem_antitranspose']

theorem period_anti (ω : MarkedInner) : ω.anti.period = ω.period := by
  unfold period
  exact content_atVec _

theorem width_anti (ω : MarkedInner) : ω.anti.width = ω.width := by
  unfold width
  rw [anti_W, span_antitranspose]

theorem origin_anti {ω : MarkedInner} (h : ¬ ω.case.IsMixed) (D : Diagram) (d : ℤ × ℤ) :
    ω.anti.origin D d = atVec (ω.origin D d) := by
  unfold origin
  have hm : ω.case = .a ∨ ω.case = .b := by
    cases hc : ω.case <;> simp_all [AttachCase.IsMixed]
  rcases hm with hc | hc
  · simp only [anti_case, hc, AttachCase.anti, anti_v, atVec_add, atVec_smul, atVec_eCell]
    ext <;> simp <;> ring
  · simp only [anti_case, hc, AttachCase.anti, anti_v, atVec_sub, atVec_smul, atVec_eCell]
    ext <;> simp

theorem exists_min_anti {O S : Diagram} {f g : ℤ × ℤ → ℤ × ℤ}
    (hfg : ∀ y, f (atVec y) = atVec (g y)) :
    (∃ x ∈ antitranspose O, content x = minContent (antitranspose O) ∧
        f x ∈ antitranspose S) ↔
      ∃ y ∈ O, content y = minContent O ∧ g y ∈ S := by
  rw [minContent_antitranspose]
  constructor
  · rintro ⟨x, hx, hc, hf⟩
    refine ⟨atVec x, mem_antitranspose'.mp hx, by rw [content_atVec]; exact hc, ?_⟩
    have h1 := hfg (atVec x)
    rw [atVec_atVec] at h1
    rw [mem_antitranspose', h1, atVec_atVec] at hf
    exact hf
  · rintro ⟨y, hy, hc, hg⟩
    refine ⟨atVec y, mem_antitranspose'.mpr (by rw [atVec_atVec]; exact hy),
      by rw [content_atVec]; exact hc, ?_⟩
    rw [mem_antitranspose', hfg, atVec_atVec]
    exact hg

theorem exists_max_anti {O S : Diagram} {f g : ℤ × ℤ → ℤ × ℤ}
    (hfg : ∀ y, f (atVec y) = atVec (g y)) :
    (∃ x ∈ antitranspose O, content x = maxContent (antitranspose O) ∧
        f x ∈ antitranspose S) ↔
      ∃ y ∈ O, content y = maxContent O ∧ g y ∈ S := by
  rw [maxContent_antitranspose]
  constructor
  · rintro ⟨x, hx, hc, hf⟩
    refine ⟨atVec x, mem_antitranspose'.mp hx, by rw [content_atVec]; exact hc, ?_⟩
    have h1 := hfg (atVec x)
    rw [atVec_atVec] at h1
    rw [mem_antitranspose', h1, atVec_atVec] at hf
    exact hf
  · rintro ⟨y, hy, hc, hg⟩
    refine ⟨atVec y, mem_antitranspose'.mpr (by rw [atVec_atVec]; exact hy),
      by rw [content_atVec]; exact hc, ?_⟩
    rw [mem_antitranspose', hfg, atVec_atVec]
    exact hg

theorem lowerH_anti (ω : MarkedInner) : ω.anti.LowerH ↔ ω.LowerV := by
  unfold LowerH LowerV
  rw [middle_anti, anti_W]
  exact exists_min_anti (O := ω.middle) (S := ω.W) (f := fun x => (x.1, x.2 - 1))
    (g := fun y => (y.1 + 1, y.2)) (by intro y; ext <;> (simp [atVec]; try omega))

theorem lowerV_anti (ω : MarkedInner) : ω.anti.LowerV ↔ ω.LowerH := by
  unfold LowerH LowerV
  rw [middle_anti, anti_W]
  exact exists_min_anti (O := ω.middle) (S := ω.W) (f := fun x => (x.1 + 1, x.2))
    (g := fun y => (y.1, y.2 - 1)) (by intro y; ext <;> (simp [atVec]; try omega))

theorem upperH_anti (ω : MarkedInner) : ω.anti.UpperH ↔ ω.UpperV := by
  unfold UpperH UpperV
  rw [middle_anti, upper_anti]
  exact exists_max_anti (O := ω.middle) (S := ω.upper) (f := fun x => (x.1, x.2 + 1))
    (g := fun y => (y.1 - 1, y.2)) (by intro y; ext <;> (simp [atVec]; try omega))

theorem upperV_anti (ω : MarkedInner) : ω.anti.UpperV ↔ ω.UpperH := by
  unfold UpperH UpperV
  rw [middle_anti, upper_anti]
  exact exists_max_anti (O := ω.middle) (S := ω.upper) (f := fun x => (x.1 - 1, x.2))
    (g := fun y => (y.1, y.2 + 1)) (by intro y; ext <;> (simp [atVec]; try omega))

theorem attachmentMatches_anti (ω : MarkedInner) :
    ω.anti.AttachmentMatches ↔ ω.AttachmentMatches := by
  unfold AttachmentMatches
  rw [lowerH_anti, lowerV_anti, upperH_anti, upperV_anti, anti_case]
  cases hc : ω.case <;> simp [AttachCase.anti, and_comm]

theorem isNonemptyMark_anti {ω : MarkedInner} (hE : IsConnectedSkew ω.E)
    (h : ω.IsNonemptyMark) : ω.anti.IsNonemptyMark := by
  obtain ⟨hne, hW, hWE, hUE, hsw, hneU, hatt⟩ := h
  refine ⟨hne.image _, isConnectedSkew_antitranspose hW, antitranspose_subset hWE, ?_, ?_, ?_,
    (attachmentMatches_anti ω).mpr hatt⟩
  · rw [upper_anti]; exact antitranspose_subset hUE
  · rw [anti_E, anti_W, sw_antitranspose hE, mem_antitranspose', atVec_atVec]
    exact hsw
  · rw [anti_E, upper_anti, ne_antitranspose hE, mem_antitranspose', atVec_atVec]
    exact hneU

theorem isNarrow_anti {ω : MarkedInner} (h : ω.IsNarrow) : ω.anti.IsNarrow := by
  unfold IsNarrow at *
  rw [width_anti, period_anti]; exact h

theorem removalsConnected_anti {ω : MarkedInner} (h : ω.RemovalsConnected) :
    ω.anti.RemovalsConnected := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · change IsConnectedSkew (antitranspose ω.E \ antitranspose ω.W)
    rw [← antitranspose_sdiff]; exact isConnectedSkew_antitranspose h1
  · change IsConnectedSkew (antitranspose ω.E \ ω.anti.upper)
    rw [upper_anti, ← antitranspose_sdiff]; exact isConnectedSkew_antitranspose h2

theorem isWellFormed_anti {ω : MarkedInner} (h : ω.IsWellFormed) (hW : ω.W.Nonempty) :
    ω.anti.IsWellFormed := by
  obtain ⟨hE, hm⟩ := h
  refine ⟨isConnectedSkew_antitranspose hE, ?_⟩
  rcases hm with hm | hm
  · exact absurd hm.1 hW.ne_empty
  · exact Or.inr (isNonemptyMark_anti hE hm)

theorem isMaximalAtDisplacement_anti {ω : MarkedInner}
    (h : ω.IsMaximalAtDisplacement) : ω.anti.IsMaximalAtDisplacement := by
  intro X hX hlt hsk hc hsub
  have hXE : X ⊆ antitranspose ω.E := Finset.mem_powerset.mp hX
  have hZ : antitranspose X ⊆ ω.E := by
    intro y hy
    rw [mem_antitranspose'] at hy
    have := hXE hy
    rw [mem_antitranspose', atVec_atVec] at this
    exact this
  refine h (antitranspose X) (Finset.mem_powerset.mpr hZ) ?_ (isSkew_antitranspose hsk) ?_ ?_
  · have := antitranspose_ssubset (show antitranspose ω.W ⊂ X from hlt)
    rwa [antitranspose_antitranspose] at this
  · rw [contents_antitranspose]
    have hc' : contents X = contents (antitranspose ω.W) := hc
    rw [hc', contents_antitranspose]
  · intro z hz
    rw [mem_translate, mem_antitranspose', atVec_sub] at hz
    have h1 : atVec z ∈ SkewGluing.translate (atVec ω.v) X := by
      rw [mem_translate]; exact hz
    have h2 := hsub h1
    change atVec z ∈ antitranspose ω.E at h2
    rw [mem_antitranspose', atVec_atVec] at h2
    exact h2

theorem isMaximal_anti {ω : MarkedInner} (hwf : ω.IsWellFormed) (hW : ω.W.Nonempty)
    (h : ω.IsMaximal) : ω.anti.IsMaximal := by
  obtain ⟨hE, hm⟩ := hwf
  rcases hm with hemp | hnon
  · exact absurd hemp.1 hW.ne_empty
  · have hrot := isNonemptyMark_anti hE hnon
    have hat := h.atDisplacement hnon.2.2.2.2.2.1
    exact (isMaximalAtDisplacement_anti hat).isMaximal (isConnectedSkew_antitranspose hE) hrot

theorem mem_periodicUnion_anti {ω : MarkedInner} {x : ℤ × ℤ} :
    x ∈ ω.anti.periodicUnion ↔ atVec x ∈ ω.periodicUnion := by
  simp only [periodicUnion, Set.mem_ofPred_eq, anti_E, anti_v, mem_antitranspose']
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have e : atVec (x - k • atVec ω.v) = atVec x - k • ω.v := by
      rw [atVec_sub, atVec_smul, atVec_atVec]
    rwa [e] at hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have e : atVec (x - k • atVec ω.v) = atVec x - k • ω.v := by
      rw [atVec_sub, atVec_smul, atVec_atVec]
    rwa [e]

theorem noHatAdjacency_anti {ω : MarkedInner} (h : ω.NoHatAdjacency) :
    ω.anti.NoHatAdjacency := by
  intro k m x hx y hy hadj
  have hmid : ∀ u : ℤ × ℤ, u ∈ SkewGluing.translate (k • ω.anti.v) ω.anti.middle ↔
      atVec u ∈ SkewGluing.translate (k • ω.v) ω.middle := by
    intro u
    rw [middle_anti, anti_v, ← atVec_smul, ← antitranspose_translate,
      mem_antitranspose']
  have hmark : ∀ u : ℤ × ℤ, u ∈ SkewGluing.translate (m • ω.anti.v) ω.anti.W ↔
      atVec u ∈ SkewGluing.translate (m • ω.v) ω.W := by
    intro u
    rw [anti_W, anti_v, ← atVec_smul, ← antitranspose_translate,
      mem_antitranspose']
  obtain ⟨hx1, hx2⟩ := hx
  rw [hmid] at hx1 hx2
  have e1 : atVec (x + eCell) = atVec x - eCell := by
    rw [atVec_add, atVec_eCell]; abel
  rw [e1] at hx2
  refine h k m (atVec x - eCell) ⟨?_, ?_⟩ (atVec y - eCell) ?_ (cellAdj_sub eCell
    (cellAdj_atVec_iff.mpr hadj))
  · exact hx2
  · simpa only [sub_add_cancel] using hx1
  · have e2 : ∀ u : ℤ × ℤ, atVec (u + eCell) = atVec u - eCell := by
      intro u; rw [atVec_add, atVec_eCell]; abel
    rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · right
      refine ⟨?_, ?_⟩
      · have := (hmark _).mp hy2
        rwa [e2] at this
      · simpa only [sub_add_cancel] using mem_periodicUnion_anti.mp hy1
    · left
      refine ⟨?_, ?_⟩
      · have := mem_periodicUnion_anti.mp hy2
        rwa [e2] at this
      · simpa only [sub_add_cancel] using (hmark _).mp hy1

/-- Antitransposition preserves legality of a mark with a nonempty copy. -/
theorem isLegal_anti {ω : MarkedInner} (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ω.anti.IsLegal :=
  ⟨isWellFormed_anti h.1 hW, isMaximal_anti h.1 hW h.2.1, isNarrow_anti h.2.2.1,
    removalsConnected_anti h.2.2.2.1, noHatAdjacency_anti h.2.2.2.2⟩

/-- **Antitransposition of a composite with an ordinary mark.**  For an ordinary mark `ω` and a
nonempty outer `D`, `AT(D ∘_ω E) = D ∘_{ω^{AT}} AT(E)`: the same outer, since `AT` carries the copy
origin `L_ω(d)` to `L_{ω^{AT}}(d)`. -/
theorem antitranspose_compose {ω : MarkedInner} (h : ¬ ω.case.IsMixed) {D : Diagram}
    (hD : D.Nonempty) : antitranspose (ω.compose D) = ω.anti.compose D := by
  have h' : ¬ ω.anti.case.IsMixed := by
    rw [anti_case, AttachCase.isMixed_anti]; exact h
  ext x
  rw [mem_antitranspose, compose_of_ordinary hD h, compose_of_ordinary hD h']
  constructor
  · rintro ⟨d, hd, hx⟩
    refine ⟨d, hd, ?_⟩
    rw [mem_translate, origin_anti h, anti_E, mem_antitranspose]
    rw [mem_translate] at hx
    have e : (-(x - atVec (ω.origin D d)).2, -(x - atVec (ω.origin D d)).1) =
        (-x.2, -x.1) - ω.origin D d := by
      ext <;> simp [atVec] <;> ring
    rw [e]; exact hx
  · rintro ⟨d, hd, hx⟩
    refine ⟨d, hd, ?_⟩
    rw [mem_translate, origin_anti h, anti_E, mem_antitranspose] at hx
    rw [mem_translate]
    have e : (-(x - atVec (ω.origin D d)).2, -(x - atVec (ω.origin D d)).1) =
        (-x.2, -x.1) - ω.origin D d := by
      ext <;> simp [atVec] <;> ring
    rw [e] at hx; exact hx

end MarkedInner

end SkewGluing
