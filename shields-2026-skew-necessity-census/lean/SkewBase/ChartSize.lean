import SkewBase.Copied.Composition

/-!
# Size bounds for proper charts

Formalizes `shields-2026-skew-base-computational.tex`, «The geometry of a chart and two complete
searches» (`sec:roots`): `lem:size` and `lem:inner-size`.

A proper chart `F = D ∘_ω E` (`Chart.IsProperLegal`: connected factors of at least two cells and
a legal mark, Hypotheses I–IV) of period `q` and width `w` satisfies

* `|F| ≥ q |D| + w` and `q ≥ 2` (`card_compose_ge`, `size_of_proper`, `two_le_period`), hence
  `2 |D| ≤ |F|` and `|D| ≤ 17` when `|F| ≤ 35` (`two_mul_card_outer_le`,
  `card_outer_le_seventeen`);
* `3 |E| ≤ 2 |F| - 1` (`inner_size`), hence `|E| ≤ 23` when `|F| ≤ 35` (`card_inner_le_23`).

The proofs count cells by content, as in the paper.  For `lem:size` the cells
`z_j + L(d)`, `d ∈ D`, `0 ≤ j < q`, where `z_j` is a cell of `E` on its `j`-th content, together
with `z_j + L(d₁)`, `q ≤ j < q + w`, for the cell `d₁` on the greatest content of `D`, are
distinct cells of the composite.  For `lem:inner-size` the copies of the two extreme cells of
`D` overlap only on the contents `[c₀ + M q, c₀ + m q + q + w - 1]`, and the overlap is bounded by
the cells of `E` on the first `w` and on the last `w` contents.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

/-! ### Elementary facts -/

/-- A connected skew diagram with at least two cells occupies at least two contents: two cells
of a connected diagram are joined by a path, and adjacent cells have different contents.  (The
statement of `SkewGluing.two_le_span_of_two_le_card`, proved directly.) -/
theorem two_le_span_of_two_le_card {D : Diagram} (hD : IsConnectedSkew D) (hc : 2 ≤ D.card) :
    2 ≤ span D := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < D.card)
  rcases Relation.ReflTransGen.cases_head (hD.2.2 x hx y hy) with h | ⟨b, hb, -⟩
  · exact absurd h hxy
  · obtain ⟨-, hbD, hadj⟩ := hb
    have hne : content x ≠ content b := by
      rcases content_adj hadj with h | h <;> omega
    have hsub : ({content x, content b} : Finset ℤ) ⊆ contents D := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact content_mem_contents hx
      · exact content_mem_contents hbD
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at this
    exact this

/-- Two cells of one diagonal of the outer with the same copy origin are equal: the origin
`L_ω(d)` of `eq:gluing-offsets` determines the row of `d` once its content is fixed. -/
theorem origin_injective_on_diagonal (ω : MarkedInner) (D : Diagram) {d d' : ℤ × ℤ}
    (hc : content d = content d') (h : ω.origin D d = ω.origin D d') : d = d' := by
  have hrow : d.1 = d'.1 := by
    have h1 := congrArg Prod.fst h
    unfold MarkedInner.origin at h1
    rw [hc] at h1
    unfold content at hc
    split at h1 <;> simp [eCell, Prod.smul_def] at h1 <;> omega
  ext
  · exact hrow
  · unfold content at hc
    omega

/-- A legal mark has positive period, since `0 ≤ w < q`. -/
theorem period_pos {ω : MarkedInner} (hω : ω.IsLegal) : 0 < ω.period := by
  have := hω.2.2.1
  unfold MarkedInner.IsNarrow at this
  omega

/-! ### `lem:copies` (iii): spans -/

/-- **`lem:copies` (iii)**, first half.  A legal mark of period `q` and width `w` on a connected
outer `D` gives a composite of span `N_D q + w`. -/
theorem span_compose_eq {ω : MarkedInner} (hω : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) :
    (span (ω.compose D) : ℤ) = span D * ω.period + ω.width :=
  MarkedInner.span_compose hD hω

/-- **`lem:copies` (iii)**, second half.  The width is the residue of the span of the composite
modulo the period, and the outer has the quotient as its span: `w = N_F mod q` and
`N_D = ⌊N_F / q⌋`. -/
theorem width_eq_span_mod {ω : MarkedInner} (hω : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) :
    (ω.width : ℤ) = (span (ω.compose D) : ℤ) % ω.period ∧
      (span D : ℤ) = (span (ω.compose D) : ℤ) / ω.period := by
  have hspan := span_compose_eq hω hD
  have hq := period_pos hω
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  have hwq : (ω.width : ℤ) < ω.period := hω.2.2.1.2
  rw [hspan]
  constructor
  · rw [Int.add_comm, Int.add_mul_emod_self_right]
    exact (Int.emod_eq_of_lt hw0 hwq).symm
  · rw [Int.add_comm, Int.add_mul_ediv_right _ _ hq.ne', Int.ediv_eq_zero_of_lt hw0 hwq]
    ring

/-- The span of the inner is `N_E = q + w`. -/
theorem span_inner_eq {ω : MarkedInner} (hω : ω.IsLegal) :
    (span ω.E : ℤ) = ω.period + ω.width :=
  hω.1.span_eq

/-! ### `lem:size` -/

/-- **`lem:size`, before the passage to charts.**  For a legal mark of period `q` and width `w`
and a nonempty outer `D`, the composite has at least `q |D| + w` cells. -/
theorem card_compose_ge {ω : MarkedInner} (hω : ω.IsLegal) {D : Diagram} (hD : D.Nonempty) :
    (D.card : ℤ) * ω.period + ω.width ≤ (ω.compose D).card := by
  have hwf := hω.1
  have hnar := hω.2.2.1
  have hcE := hwf.contents_eq
  have hq0 := period_pos hω
  set c0 := minContent ω.E with hc0
  set q := ω.period with hq
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  have hwq : (ω.width : ℤ) < q := hnar.2
  have hrep : ∀ k : ℤ, k ∈ Finset.Icc c0 (c0 + q + ω.width - 1) →
      ∃ z ∈ ω.E, content z = k := by
    intro k hk
    have : k ∈ contents ω.E := by rw [hcE]; exact hk
    obtain ⟨i, hi⟩ := mem_contents_iff.mp this
    exact ⟨(i, i + k), hi, by simp [content]⟩
  choose! zf hzf1 hzf2 using hrep
  have hd1 : ne D ∈ D := ne_mem hD
  have hc1 : content (ne D) = maxContent D := content_ne hD
  set d1 := ne D with hd1def
  set M := maxContent D with hM
  let Φ : (ℤ × ℤ) × ℤ → ℤ × ℤ := fun p => zf (c0 + p.2) + ω.origin D p.1
  let S1 : Finset ((ℤ × ℤ) × ℤ) := D ×ˢ Finset.Ico (0 : ℤ) q
  let S2 : Finset ((ℤ × ℤ) × ℤ) := {d1} ×ˢ Finset.Ico q (q + ω.width)
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    rintro p hp1 hp2
    simp only [S1, S2, Finset.mem_product, Finset.mem_Ico] at hp1 hp2
    omega
  have hcard1 : (S1.card : ℤ) = D.card * q := by
    simp only [S1, Finset.card_product, Int.card_Ico, sub_zero]
    push_cast
    rw [Int.toNat_of_nonneg hq0.le]
  have hcard2 : (S2.card : ℤ) = ω.width := by
    simp only [S2, Finset.card_product, Int.card_Ico, Finset.card_singleton, one_mul]
    rw [show q + (ω.width : ℤ) - q = ω.width by ring, Int.toNat_of_nonneg hw0]
  have hcard : ((S1 ∪ S2).card : ℤ) = D.card * q + ω.width := by
    rw [Finset.card_union_of_disjoint hdisj]
    push_cast
    rw [hcard1, hcard2]
  have hkey : ∀ p ∈ S1 ∪ S2, p.1 ∈ D ∧ ((0 ≤ p.2 ∧ p.2 < q) ∨
      (p.1 = d1 ∧ q ≤ p.2 ∧ p.2 < q + ω.width)) := by
    intro p hp
    simp only [S1, S2, Finset.mem_union, Finset.mem_product, Finset.mem_Ico,
      Finset.mem_singleton] at hp
    rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨h1, Or.inl ⟨h2, h3⟩⟩
    · exact ⟨h1 ▸ hd1, Or.inr ⟨h1, h2, h3⟩⟩
  have hcontent : ∀ p ∈ S1 ∪ S2, content (Φ p) = c0 + p.2 + content p.1 * q := by
    intro p hp
    obtain ⟨-, hr⟩ := hkey p hp
    have hk : c0 + p.2 ∈ Finset.Icc c0 (c0 + q + ω.width - 1) := by
      rw [Finset.mem_Icc]
      rcases hr with ⟨h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    change content (zf (c0 + p.2) + ω.origin D p.1) = _
    rw [content_add, hzf2 _ hk, MarkedInner.content_origin]
  have hle : ∀ p ∈ S1 ∪ S2, content p.1 ≤ M := fun p hp =>
    le_maxContent (content_mem_contents (hkey p hp).1)
  have hinj : Set.InjOn Φ ↑(S1 ∪ S2) := by
    intro p hp p' hp' heq
    have hp_ : p ∈ S1 ∪ S2 := hp
    have hp'_ : p' ∈ S1 ∪ S2 := hp'
    have h1 : c0 + p.2 + content p.1 * q = c0 + p'.2 + content p'.1 * q := by
      rw [← hcontent p hp_, ← hcontent p' hp'_, heq]
    obtain ⟨hD1, hr1⟩ := hkey p hp_
    obtain ⟨hD2, hr2⟩ := hkey p' hp'_
    have hmax1 := hle p hp_
    have hmax2 := hle p' hp'_
    have hboth : p.2 = p'.2 ∧ content p.1 = content p'.1 := by
      rcases hr1 with ⟨a1, a2⟩ | ⟨e1, a1, a2⟩ <;> rcases hr2 with ⟨b1, b2⟩ | ⟨e2, b1, b2⟩
      · have hdvd : q ∣ p.2 - p'.2 := ⟨content p'.1 - content p.1, by linear_combination h1⟩
        have h0 := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by omega, by omega⟩)
        have hpp : p.2 = p'.2 := by omega
        refine ⟨hpp, ?_⟩
        rw [hpp] at h1
        exact mul_right_cancel₀ hq0.ne' (by linarith)
      · exfalso
        have := mul_le_mul_of_nonneg_right hmax1 hq0.le
        have hc2 : content p'.1 = M := by rw [e2, hc1]
        rw [hc2] at h1
        nlinarith
      · exfalso
        have := mul_le_mul_of_nonneg_right hmax2 hq0.le
        have hc2 : content p.1 = M := by rw [e1, hc1]
        rw [hc2] at h1
        nlinarith
      · have hc2 : content p'.1 = M := by rw [e2, hc1]
        have hc3 : content p.1 = M := by rw [e1, hc1]
        refine ⟨?_, by rw [hc2, hc3]⟩
        rw [hc2, hc3] at h1
        linarith
    obtain ⟨hpp, hcc⟩ := hboth
    have hor : ω.origin D p.1 = ω.origin D p'.1 := by
      have : zf (c0 + p.2) + ω.origin D p.1 = zf (c0 + p.2) + ω.origin D p'.1 := by
        have h2 : Φ p = Φ p' := heq
        simp only [Φ] at h2
        rw [hpp] at h2 ⊢
        exact h2
      exact add_left_cancel this
    have hfirst := origin_injective_on_diagonal ω D hcc hor
    exact Prod.ext hfirst hpp
  have hsub : (S1 ∪ S2).image Φ ⊆ ω.compose D := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hD1, hr⟩ := hkey p hp
    have hk : c0 + p.2 ∈ Finset.Icc c0 (c0 + q + ω.width - 1) := by
      rw [Finset.mem_Icc]
      rcases hr with ⟨h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    rw [MarkedInner.mem_compose hD]
    refine Or.inl ⟨p.1, hD1, mem_translate.mpr ?_⟩
    change zf (c0 + p.2) + ω.origin D p.1 - ω.origin D p.1 ∈ ω.E
    rw [add_sub_cancel_right]
    exact hzf1 _ hk
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at this
  have h2 : ((S1 ∪ S2).card : ℤ) ≤ (ω.compose D).card := by exact_mod_cast this
  rw [hcard] at h2
  exact h2

/-- A chart of `F` has as many cells as its parent. -/
theorem card_of_isChartOf {χ : Chart} {F : Diagram} (h : χ.IsChartOf F) :
    F.card = χ.parent.card := by
  obtain ⟨t, rfl⟩ := h
  exact Finset.card_image_of_injective _ (add_left_injective t)

/-- **`lem:size`.**  Every proper chart satisfies `|F| ≥ q |D| + w`. -/
theorem size_of_proper {χ : Chart} (h : χ.IsProperLegal) :
    (χ.D.card : ℤ) * χ.ω.period + χ.ω.width ≤ χ.parent.card :=
  card_compose_ge h.2.2.2 h.1.2.1

/-- The period of a proper chart is at least two: `N_E = q + w < 2 q` and `N_E ≥ 2`. -/
theorem two_le_period {χ : Chart} (h : χ.IsProperLegal) : 2 ≤ χ.ω.period := by
  obtain ⟨-, -, hE, hω⟩ := h
  have hspan := hω.1.span_eq
  have hE2 := two_le_span_of_two_le_card hω.1.1 hE
  have hwq := hω.2.2.1.2
  have hw0 : (0 : ℤ) ≤ χ.ω.width := by positivity
  omega

/-- `|D| ≤ |F| / 2` for every proper chart `F = D ∘_ω E`. -/
theorem two_mul_card_outer_le {χ : Chart} (h : χ.IsProperLegal) :
    2 * χ.D.card ≤ χ.parent.card := by
  have h1 := size_of_proper h
  have h2 := two_le_period h
  have hw0 : (0 : ℤ) ≤ χ.ω.width := by positivity
  have : (2 * χ.D.card : ℤ) ≤ χ.parent.card := by nlinarith [(by positivity : (0 : ℤ) ≤ χ.D.card)]
  exact_mod_cast this

/-- `|D| ≤ 17` for a proper chart of a diagram of at most `35` cells. -/
theorem card_outer_le_seventeen {χ : Chart} (h : χ.IsProperLegal) {F : Diagram}
    (hF : χ.IsChartOf F) (hn : F.card ≤ 35) : χ.D.card ≤ 17 := by
  have := two_mul_card_outer_le h
  rw [card_of_isChartOf hF] at hn
  omega

/-! ### `lem:inner-size` -/

/-- **`lem:inner-size`, before the passage to charts.**  For a legal mark and a connected outer
with at least two contents, `3 |E| ≤ 2 |F| - 1`, written `3 |E| + 1 ≤ 2 |F|`. -/
theorem inner_size_of_two_le_span {ω : MarkedInner} (hω : ω.IsLegal) {D : Diagram}
    (hD : IsConnectedSkew D) (hspan : 2 ≤ span D) :
    3 * ω.E.card + 1 ≤ 2 * (ω.compose D).card := by
  have hDne : D.Nonempty := hD.2.1
  have hwf := hω.1
  have hnar := hω.2.2.1
  have hcE := hwf.contents_eq
  have hq0 := period_pos hω
  have hw0 : (0 : ℤ) ≤ ω.width := by positivity
  have hwq : (ω.width : ℤ) < ω.period := hnar.2
  set c0 := minContent ω.E with hc0
  set q := ω.period with hq
  have hsp := span_eq_of_isConnectedSkew hD
  set m := minContent D with hm
  set M := maxContent D with hM
  have hMm : m + 1 ≤ M := by
    have : (2 : ℤ) ≤ span D := by exact_mod_cast hspan
    omega
  have hqMm : q ≤ (M - m) * q := by nlinarith
  set d0 := sw D with hd0def
  set d1 := ne D with hd1def
  have hd0 : d0 ∈ D := sw_mem hDne
  have hd1 : d1 ∈ D := ne_mem hDne
  have hc0' : content d0 = m := content_sw hDne
  have hc1' : content d1 = M := content_ne hDne
  set o0 := ω.origin D d0 with ho0
  set o1 := ω.origin D d1 with ho1
  have hco0 : content o0 = m * q := by rw [ho0, MarkedInner.content_origin, hc0']
  have hco1 : content o1 = M * q := by rw [ho1, MarkedInner.content_origin, hc1']
  have hE0 : translate o0 ω.E ⊆ ω.compose D := by
    intro x hx
    rw [MarkedInner.mem_compose hDne]
    exact Or.inl ⟨d0, hd0, hx⟩
  have hE1 : translate o1 ω.E ⊆ ω.compose D := by
    intro x hx
    rw [MarkedInner.mem_compose hDne]
    exact Or.inl ⟨d1, hd1, hx⟩
  have hcardT : ∀ t : ℤ × ℤ, (translate t ω.E).card = ω.E.card := fun t =>
    Finset.card_image_of_injective _ (add_left_injective t)
  have hcontE : ∀ z ∈ ω.E, c0 ≤ content z ∧ content z ≤ c0 + q + ω.width - 1 := by
    intro z hz
    have : content z ∈ contents ω.E := content_mem_contents hz
    rw [hcE, Finset.mem_Icc] at this
    exact this
  -- the cells of `E` on the first `w` contents, and on the last `w` contents
  set A := ω.E.filter (fun z => content z < c0 + ω.width) with hA
  set C := ω.E.filter (fun z => c0 + q ≤ content z) with hC
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro z hzA hzC
    simp only [hA, hC, Finset.mem_filter] at hzA hzC
    omega
  have hmid : ∃ z ∈ ω.E, content z = c0 + ω.width := by
    have : c0 + (ω.width : ℤ) ∈ contents ω.E := by
      rw [hcE, Finset.mem_Icc]; omega
    obtain ⟨i, hi⟩ := mem_contents_iff.mp this
    exact ⟨(i, i + (c0 + ω.width)), hi, by simp [content]⟩
  obtain ⟨zm, hzmE, hzm⟩ := hmid
  have hAC1 : A.card + C.card + 1 ≤ ω.E.card := by
    have hdisj : Disjoint (A ∪ C) {zm} := by
      rw [Finset.disjoint_singleton_right]
      intro hz
      simp only [hA, hC, Finset.mem_union, Finset.mem_filter] at hz
      omega
    have hsub : A ∪ C ∪ {zm} ⊆ ω.E := by
      intro z hz
      simp only [hA, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hz
      rcases hz with (⟨h, -⟩ | ⟨h, -⟩) | rfl
      · exact h
      · exact h
      · exact hzmE
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hAC,
      Finset.card_singleton] at this
    exact this
  -- the overlap of the two copies
  have hmemI : ∀ x ∈ translate o0 ω.E ∩ translate o1 ω.E,
      x - o0 ∈ ω.E ∧ x - o1 ∈ ω.E := by
    intro x hx
    rw [Finset.mem_inter, mem_translate, mem_translate] at hx
    exact hx
  have hIC : (translate o0 ω.E ∩ translate o1 ω.E).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun x => x - o0)
    · intro x hx
      obtain ⟨h0, h1⟩ := hmemI x hx
      simp only [hC, Finset.coe_filter, Set.mem_ofPred_eq]
      refine ⟨h0, ?_⟩
      have a1 := (hcontE _ h1).1
      rw [MarkedInner.content_sub, hco1] at a1
      rw [MarkedInner.content_sub, hco0]
      nlinarith
    · intro x _ y _ hxy
      simpa using hxy
  have hIA : (translate o0 ω.E ∩ translate o1 ω.E).card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun x => x - o1)
    · intro x hx
      obtain ⟨h0, h1⟩ := hmemI x hx
      simp only [hA, Finset.coe_filter, Set.mem_ofPred_eq]
      refine ⟨h1, ?_⟩
      have a0 := (hcontE _ h0).2
      rw [MarkedInner.content_sub, hco0] at a0
      rw [MarkedInner.content_sub, hco1]
      nlinarith
    · intro x _ y _ hxy
      simpa using hxy
  have hU := Finset.card_union_add_card_inter (translate o0 ω.E) (translate o1 ω.E)
  have hUle : (translate o0 ω.E ∪ translate o1 ω.E).card ≤ (ω.compose D).card :=
    Finset.card_le_card (Finset.union_subset hE0 hE1)
  rw [hcardT, hcardT] at hU
  omega

/-- **`lem:inner-size`.**  Every proper chart satisfies `3 |E| ≤ 2 |F| - 1`, written
`3 |E| + 1 ≤ 2 |F|`. -/
theorem inner_size {χ : Chart} (h : χ.IsProperLegal) :
    3 * χ.ω.E.card + 1 ≤ 2 * χ.parent.card :=
  inner_size_of_two_le_span h.2.2.2 h.1 (two_le_span_of_two_le_card h.1 h.2.1)

/-- `|E| ≤ 23` for a proper chart of a diagram of at most `35` cells. -/
theorem card_inner_le_23 {χ : Chart} (h : χ.IsProperLegal) {F : Diagram}
    (hF : χ.IsChartOf F) (hn : F.card ≤ 35) : χ.ω.E.card ≤ 23 := by
  have := inner_size h
  rw [card_of_isChartOf hF] at hn
  omega

end SkewBase
