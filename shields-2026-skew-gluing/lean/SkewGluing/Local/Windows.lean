import SkewGluing.Local.ComposeRotate

/-!
# The two windows of a composite

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`lem:gluing-local` (3)).

For a legal mark of width `w` and period `q` and a connected outer `D` with contents `[m, M]`, the
first `q` diagonals of `D ∘_ω E` are those of `E` placed at the origin of the southwest cell of
`D`; the last `q` diagonals are the diagonals `[w, q + w - 1]` of `E` placed at the origin of the
northeast cell of `D`.  For a mixed mark these two origins are `m v` and `M v`, so the second
window is the translate of the first by `(r - 1) v` with `r = N_D`.  The two windows determine `E`
up to translation.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem IsLegal.upper_content (hω : ω.IsLegal) {x : ℤ × ℤ} (hx : x ∈ ω.upper) :
    minContent ω.E + ω.period ≤ content x ∧
      content x ≤ minContent ω.E + ω.period + ω.width - 1 := by
  obtain ⟨hwf, -, -, -, -⟩ := hω
  rcases hwf.2 with hemp | hnon
  · exfalso
    simp [upper, hemp.1, translate] at hx
  · have hb := hnon.content_bounds hwf.1
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have := hb.1 y hy
    simp only [content_add]
    unfold period at *
    have e : content ω.v = ω.period := rfl
    omega

theorem IsLegal.copy_content (hω : ω.IsLegal) {y : ℤ × ℤ} (hy : y ∈ ω.E) :
    minContent ω.E ≤ content y ∧
      content y ≤ minContent ω.E + ω.period + ω.width - 1 := by
  have := hω.1.contents_eq
  have h2 := content_mem_contents hy
  rw [this, Finset.mem_Icc] at h2
  exact h2

/-- Any cell of the composite in one of the two supplemental/main families has relative content
in the range of the copy that produced it. -/
theorem IsLegal.mem_compose_content (hω : ω.IsLegal) (hD : IsConnectedSkew D) {x : ℤ × ℤ}
    (hx : x ∈ ω.compose D) :
    (∃ d ∈ D, minContent ω.E + content d * ω.period ≤ content x ∧
      content x ≤ minContent ω.E + content d * ω.period + ω.period + ω.width - 1 ∧
      x ∈ translate (ω.origin D d) ω.E) ∨
    (∃ d ∈ D, content d + 1 ≤ maxContent D ∧
      minContent ω.E + content d * ω.period + ω.period ≤ content x ∧
      content x ≤ minContent ω.E + content d * ω.period + ω.period + ω.width - 1) := by
  rcases (mem_compose hD.2.1).mp hx with ⟨d, hd, hxd⟩ | ⟨d, hd, hr, hxd⟩
  · left
    refine ⟨d, hd, ?_⟩
    have h1 := hω.copy_content (mem_translate.mp hxd)
    rw [content_sub, content_origin] at h1
    exact ⟨by omega, by omega, hxd⟩
  · right
    refine ⟨d, hd, ?_, ?_⟩
    · have hn := hr.1
      have := le_maxContent (content_mem_contents hn)
      have e : content (d.1 - 1, d.2) = content d + 1 := by simp [content]; ring
      omega
    · have h1 := hω.upper_content (mem_translate.mp hxd)
      rw [content_sub, content_add, content_origin, content_supplementalShift] at h1
      unfold period at *
      omega


theorem IsLegal.period_pos (hω : ω.IsLegal) : 0 < ω.period := by
  have := hω.2.2.1
  unfold IsNarrow at this
  omega

theorem IsLegal.period_toNat_cast (hω : ω.IsLegal) : ((ω.period.toNat : ℕ) : ℤ) = ω.period :=
  Int.toNat_of_nonneg hω.period_pos.le

/-- **`lem:gluing-local` (3), first window.**  The cells of `D ∘_ω E` on its first `q` diagonals
are the cells of `E` on its first `q` diagonals, placed at the origin of the southwest cell of
`D`. -/
theorem IsLegal.compose_first_window (hω : ω.IsLegal) (hD : IsConnectedSkew D) :
    (ω.compose D).filter
        (fun x => content x ≤ minContent ω.E + minContent D * ω.period + ω.period - 1) =
      translate (ω.origin D (sw D))
        (ω.E.filter fun y => content y ≤ minContent ω.E + ω.period - 1) := by
  have hq := hω.period_pos
  have hDne := hD.2.1
  ext x
  simp only [Finset.mem_filter, mem_translate]
  rw [content_sub, content_origin, content_sw hDne]
  constructor
  · rintro ⟨hxF, hxc⟩
    rcases hω.mem_compose_content hD hxF with ⟨d, hd, h1, h2, hxd⟩ | ⟨d, hd, hdM, h1, h2⟩
    · have hdm : minContent D ≤ content d := minContent_le (content_mem_contents hd)
      have hjm : content d ≤ minContent D := by
        by_contra hn
        have := mul_le_mul_of_nonneg_right (show minContent D + 1 ≤ content d by omega) hq.le
        nlinarith
      have hd' := eq_sw_of_content hD hd (by omega)
      subst hd'
      have := mem_translate.mp hxd
      refine ⟨this, ?_⟩
      omega
    · have hdm : minContent D ≤ content d := minContent_le (content_mem_contents hd)
      have := mul_le_mul_of_nonneg_right hdm hq.le
      nlinarith
  · rintro ⟨hxE, hxc⟩
    refine ⟨?_, by omega⟩
    rw [mem_compose hDne]
    left
    exact ⟨sw D, sw_mem hDne, mem_translate.mpr hxE⟩
  
/-- **`lem:gluing-local` (3), last window.**  The cells of `D ∘_ω E` on its last `q` diagonals
are the cells of `E` on its diagonals `[w, q + w - 1]`, placed at the origin of the northeast cell
of `D`. -/
theorem IsLegal.compose_last_window (hω : ω.IsLegal) (hD : IsConnectedSkew D) :
    (ω.compose D).filter
        (fun x => minContent ω.E + maxContent D * ω.period + ω.width ≤ content x) =
      translate (ω.origin D (ne D))
        (ω.E.filter fun y => minContent ω.E + ω.width ≤ content y) := by
  have hq := hω.period_pos
  have hDne := hD.2.1
  ext x
  simp only [Finset.mem_filter, mem_translate]
  rw [content_sub, content_origin, content_ne hDne]
  constructor
  · rintro ⟨hxF, hxc⟩
    rcases hω.mem_compose_content hD hxF with ⟨d, hd, h1, h2, hxd⟩ | ⟨d, hd, hdM, h1, h2⟩
    · have hdM : content d ≤ maxContent D := le_maxContent (content_mem_contents hd)
      have hjm : maxContent D ≤ content d := by
        by_contra hn
        have := mul_le_mul_of_nonneg_right (show content d + 1 ≤ maxContent D by omega) hq.le
        nlinarith
      have hd' := eq_ne_of_content hD hd (by omega)
      subst hd'
      have := mem_translate.mp hxd
      refine ⟨this, ?_⟩
      omega
    · have := mul_le_mul_of_nonneg_right hdM hq.le
      nlinarith
  · rintro ⟨hxE, hxc⟩
    refine ⟨?_, by omega⟩
    rw [mem_compose hDne]
    left
    exact ⟨ne D, ne_mem hDne, mem_translate.mpr hxE⟩

/-- The origins of the end cells of `D` for a mixed mark: `m v` and `M v` (the rank terms of
`eq:gluing-offsets` vanish on the singleton end diagonals). -/
theorem origin_ends_mixed (hmix : ω.case.IsMixed) (hD : IsConnectedSkew D) :
    ω.origin D (sw D) = minContent D • ω.v ∧ ω.origin D (ne D) = maxContent D • ω.v := by
  have hDne := hD.2.1
  have he := D_ends hD
  unfold AttachCase.IsMixed at hmix
  have e1 : content (sw D) = minContent D := content_sw hDne
  have e2 : content (ne D) = maxContent D := content_ne hDne
  have s1 : (sw D).1 = diagLo D (minContent D) := rfl
  have s2 : (ne D).1 = diagLo D (maxContent D) := rfl
  rcases hmix with hc | hc <;> unfold origin <;> rw [hc] <;> simp only [e1, e2, s1, s2] <;>
    simp [he.1, he.2]


theorem eq_of_singleton_diag {E : Diagram} {c : ℤ} (hs : diagLo E c = diagHi E c) {z z' : ℤ × ℤ}
    (hz : z ∈ E) (hz' : z' ∈ E) (hc : content z = c) (hc' : content z' = c) : z = z' := by
  have h1 := diagLo_le (D := E) (k := c) (i := z.1) (j := z.2) hz (by simpa [content] using hc)
  have h2 := le_diagHi (D := E) (k := c) (i := z.1) (j := z.2) hz (by simpa [content] using hc)
  have h3 := diagLo_le (D := E) (k := c) (i := z'.1) (j := z'.2) hz' (by simpa [content] using hc')
  have h4 := le_diagHi (D := E) (k := c) (i := z'.1) (j := z'.2) hz' (by simpa [content] using hc')
  simp only [content] at hc hc'
  ext <;> omega

/-- **The two windows determine `E` (`lem:gluing-local` (3)).**  Let `E`, `E'` be connected skew
diagrams of span `q + w` with `0 ≤ w < q` and singleton diagonal `w`.  If their first-`q`-diagonal
windows are translates of each other, and their windows on the diagonals `[w, q + w - 1]` are
translates of each other, then `E'` is a translate of `E`. -/
theorem eq_translate_of_windows {E E' : Diagram} {q w : ℤ} (hE : IsConnectedSkew E)
    (hE' : IsConnectedSkew E') (hs : (span E : ℤ) = q + w) (hs' : (span E' : ℤ) = q + w)
    (hw : 0 ≤ w) (hwq : w < q) (_hsing : diagLo E (minContent E + w) = diagHi E (minContent E + w))
    (hsing' : diagLo E' (minContent E' + w) = diagHi E' (minContent E' + w)) {δ₁ δ₂ : ℤ × ℤ}
    (h1 : translate δ₁ (E.filter fun y => content y ≤ minContent E + q - 1) =
      E'.filter fun y => content y ≤ minContent E' + q - 1)
    (h2 : translate δ₂ (E.filter fun y => minContent E + w ≤ content y) =
      E'.filter fun y => minContent E' + w ≤ content y) :
    ∃ δ, E' = translate δ E := by
  have hne := hE.2.1
  have hne' := hE'.2.1
  have sp := span_eq_of_isConnectedSkew hE
  have sp' := span_eq_of_isConnectedSkew hE'
  have hswE := sw_mem hne
  have hswE' := sw_mem hne'
  have hneE := ne_mem hne
  have hneE' := ne_mem hne'
  have cs := content_sw hne
  have cs' := content_sw hne'
  have cn := content_ne hne
  have cn' := content_ne hne'
  -- the content shift of the first window
  have c1 : content δ₁ = minContent E' - minContent E := by
    have f1 : sw E ∈ E.filter fun y => content y ≤ minContent E + q - 1 :=
      Finset.mem_filter.mpr ⟨hswE, by omega⟩
    have a1 : sw E + δ₁ ∈ E'.filter fun y => content y ≤ minContent E' + q - 1 := by
      rw [← h1]; exact Finset.mem_image_of_mem (fun x => x + δ₁) f1
    have a2 : sw E' ∈ translate δ₁ (E.filter fun y => content y ≤ minContent E + q - 1) := by
      rw [h1]; exact Finset.mem_filter.mpr ⟨hswE', by omega⟩
    have b1 := content_sw_le (Finset.mem_filter.mp a1).1
    have b2 := (Finset.mem_filter.mp (mem_translate.mp a2)).1
    have b3 := content_sw_le b2
    rw [content_add] at b1
    rw [content_sub] at b3
    omega
  have c2 : content δ₂ = minContent E' - minContent E := by
    have f1 : ne E ∈ E.filter fun y => minContent E + w ≤ content y :=
      Finset.mem_filter.mpr ⟨hneE, by omega⟩
    have a1 : ne E + δ₂ ∈ E'.filter fun y => minContent E' + w ≤ content y := by
      rw [← h2]; exact Finset.mem_image_of_mem (fun x => x + δ₂) f1
    have a2 : ne E' ∈ translate δ₂ (E.filter fun y => minContent E + w ≤ content y) := by
      rw [h2]; exact Finset.mem_filter.mpr ⟨hneE', by omega⟩
    have b1 := content_le_ne (Finset.mem_filter.mp a1).1
    have b2 := (Finset.mem_filter.mp (mem_translate.mp a2)).1
    have b3 := content_le_ne b2
    rw [content_add] at b1
    rw [content_sub] at b3
    omega
  -- the cell of the diagonal `w`
  have xw : (diagLo E (minContent E + w),
      diagLo E (minContent E + w) + (minContent E + w)) ∈ E := by
    have hk : minContent E + w ∈ contents E := by
      rw [(isConnectedSkew_iff_diagonal.mp hE).mem_contents_iff]; omega
    have := diagLo_mem hk
    simpa using this
  have xw' : (diagLo E' (minContent E' + w), diagLo E' (minContent E' + w) + (minContent E' + w))
      ∈ E' := by
    have hk : minContent E' + w ∈ contents E' := by
      rw [(isConnectedSkew_iff_diagonal.mp hE').mem_contents_iff]; omega
    have := diagLo_mem hk
    simpa using this
  set xw0 := (diagLo E (minContent E + w), diagLo E (minContent E + w) + (minContent E + w))
    with hxw0
  set xw1 := (diagLo E' (minContent E' + w), diagLo E' (minContent E' + w) + (minContent E' + w))
    with hxw1
  have cx : content xw0 = minContent E + w := by simp [hxw0, content]
  have cx' : content xw1 = minContent E' + w := by simp [hxw1, content]
  have y1 : xw0 + δ₁ ∈ E' := by
    have f1 : xw0 ∈ E.filter fun y => content y ≤ minContent E + q - 1 :=
      Finset.mem_filter.mpr ⟨xw, by omega⟩
    have : xw0 + δ₁ ∈ E'.filter fun y => content y ≤ minContent E' + q - 1 := by
      rw [← h1]; exact Finset.mem_image_of_mem (fun x => x + δ₁) f1
    exact (Finset.mem_filter.mp this).1
  have y2 : xw0 + δ₂ ∈ E' := by
    have f1 : xw0 ∈ E.filter fun y => minContent E + w ≤ content y :=
      Finset.mem_filter.mpr ⟨xw, by omega⟩
    have : xw0 + δ₂ ∈ E'.filter fun y => minContent E' + w ≤ content y := by
      rw [← h2]; exact Finset.mem_image_of_mem (fun x => x + δ₂) f1
    exact (Finset.mem_filter.mp this).1
  have e1 : xw0 + δ₁ = xw1 := eq_of_singleton_diag hsing' y1 xw' (by rw [content_add]; omega) cx'
  have e2 : xw0 + δ₂ = xw1 := eq_of_singleton_diag hsing' y2 xw' (by rw [content_add]; omega) cx'
  have hδ : δ₁ = δ₂ := add_left_cancel (e1.trans e2.symm)
  subst hδ
  refine ⟨δ₁, ?_⟩
  have cover : ∀ {F : Diagram}, IsConnectedSkew F → F = (F.filter fun y => content y ≤
      minContent F + q - 1) ∪ (F.filter fun y => minContent F + w ≤ content y) := by
    intro F hF
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hy
      by_cases hc : content y ≤ minContent F + q - 1
      · exact Or.inl ⟨hy, hc⟩
      · exact Or.inr ⟨hy, by omega⟩
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
  conv_lhs => rw [cover hE']
  rw [← h1, ← h2]
  conv_rhs => rw [cover hE]
  unfold translate
  rw [Finset.image_union]


theorem IsLegal.minContent_compose (hω : ω.IsLegal) (hD : IsConnectedSkew D) :
    minContent (ω.compose D) = minContent ω.E + minContent D * ω.period := by
  have hq := hω.period_pos
  have hDne := hD.2.1
  have hEne : ω.E.Nonempty := hω.1.1.2.1
  have hmem : sw ω.E + ω.origin D (sw D) ∈ ω.compose D := by
    rw [mem_compose hDne]
    left
    exact ⟨sw D, sw_mem hDne, mem_translate.mpr (by simpa using sw_mem hEne)⟩
  apply minContent_eq_of (k := minContent ω.E + minContent D * ω.period)
  · have := content_mem_contents hmem
    rwa [content_add, content_origin, content_sw hDne, content_sw hEne] at this
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    rcases hω.mem_compose_content hD hx with ⟨d, hd, h1, -, -⟩ | ⟨d, hd, -, h1, -⟩
    · have hdm : minContent D ≤ content d := minContent_le (content_mem_contents hd)
      have := mul_le_mul_of_nonneg_right hdm hq.le
      omega
    · have hdm : minContent D ≤ content d := minContent_le (content_mem_contents hd)
      have := mul_le_mul_of_nonneg_right hdm hq.le
      omega

theorem IsLegal.maxContent_compose (hω : ω.IsLegal) (hD : IsConnectedSkew D) :
    maxContent (ω.compose D) =
      minContent ω.E + maxContent D * ω.period + ω.period + ω.width - 1 := by
  have hq := hω.period_pos
  have hDne := hD.2.1
  have hEne : ω.E.Nonempty := hω.1.1.2.1
  have hmem : ne ω.E + ω.origin D (ne D) ∈ ω.compose D := by
    rw [mem_compose hDne]
    left
    exact ⟨ne D, ne_mem hDne, mem_translate.mpr (by simpa using ne_mem hEne)⟩
  have hspan := hω.1.span_eq
  have hsp := span_eq_of_isConnectedSkew hω.1.1
  apply maxContent_eq_of (k := minContent ω.E + maxContent D * ω.period + ω.period + ω.width - 1)
  · have := content_mem_contents hmem
    rw [content_add, content_origin, content_ne hDne, content_ne hEne] at this
    have e : maxContent ω.E = minContent ω.E + ω.period + ω.width - 1 := by omega
    rw [e] at this
    convert this using 1
    ring
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    rcases hω.mem_compose_content hD hx with ⟨d, hd, -, h1, -⟩ | ⟨d, hd, hdM, -, h1⟩
    · have hdM : content d ≤ maxContent D := le_maxContent (content_mem_contents hd)
      have := mul_le_mul_of_nonneg_right hdM hq.le
      omega
    · have := mul_le_mul_of_nonneg_right hdM hq.le
      have e : (content d + 1) * ω.period = content d * ω.period + ω.period := by ring
      nlinarith


/-- **`lem:gluing-local` (3), the two windows determine `E`.**  Let `ω`, `ω'` be legal marks with
nonempty copies, of the same period and width, and let `D`, `D'` be connected outers.  If the
first `q` diagonals of `D ∘_ω E` and `D' ∘_{ω'} E'` are translates of each other, and so are their
last `q` diagonals, then `E'` is a translate of `E`. -/
theorem IsLegalNonempty.windows_determine {ω ω' : MarkedInner} {D D' : Diagram}
    (h : ω.IsLegalNonempty) (h' : ω'.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') (hq : ω'.period = ω.period) (hw : ω'.widthZ = ω.widthZ)
    {σ₁ σ₂ : ℤ × ℤ}
    (h1 : translate σ₁ ((ω.compose D).filter fun x =>
        content x ≤ minContent (ω.compose D) + ω.period - 1) =
      (ω'.compose D').filter fun x => content x ≤ minContent (ω'.compose D') + ω.period - 1)
    (h2 : translate σ₂ ((ω.compose D).filter fun x =>
        maxContent (ω.compose D) - ω.period + 1 ≤ content x) =
      (ω'.compose D').filter fun x => maxContent (ω'.compose D') - ω.period + 1 ≤ content x) :
    ∃ δ, ω'.E = translate δ ω.E := by
  have hwn : (ω'.width : ℤ) = ω.width := hw
  have ec1 : ∀ {μ : MarkedInner} {B : Diagram}, μ.IsLegal → IsConnectedSkew B →
      ∀ x, (content x ≤ minContent (μ.compose B) + μ.period - 1) ↔
        content x ≤ minContent μ.E + minContent B * μ.period + μ.period - 1 := by
    intro μ B hμ hB x
    rw [hμ.minContent_compose hB]
  have ec2 : ∀ {μ : MarkedInner} {B : Diagram}, μ.IsLegal → IsConnectedSkew B →
      ∀ x, (maxContent (μ.compose B) - μ.period + 1 ≤ content x) ↔
        minContent μ.E + maxContent B * μ.period + μ.width ≤ content x := by
    intro μ B hμ hB x
    rw [hμ.maxContent_compose hB]; omega
  have f1 : (ω.compose D).filter (fun x => content x ≤ minContent (ω.compose D) + ω.period - 1) =
      (ω.compose D).filter (fun x =>
        content x ≤ minContent ω.E + minContent D * ω.period + ω.period - 1) :=
    Finset.filter_congr (fun x _ => ec1 h.1 hD x)
  have f1' : (ω'.compose D').filter (fun x =>
      content x ≤ minContent (ω'.compose D') + ω.period - 1) =
      (ω'.compose D').filter (fun x =>
        content x ≤ minContent ω'.E + minContent D' * ω'.period + ω'.period - 1) :=
    Finset.filter_congr (fun x _ => by rw [← hq]; exact ec1 h'.1 hD' x)
  have f2 : (ω.compose D).filter (fun x => maxContent (ω.compose D) - ω.period + 1 ≤ content x) =
      (ω.compose D).filter (fun x =>
        minContent ω.E + maxContent D * ω.period + ω.width ≤ content x) :=
    Finset.filter_congr (fun x _ => ec2 h.1 hD x)
  have f2' : (ω'.compose D').filter (fun x =>
      maxContent (ω'.compose D') - ω.period + 1 ≤ content x) =
      (ω'.compose D').filter (fun x =>
        minContent ω'.E + maxContent D' * ω'.period + ω'.width ≤ content x) :=
    Finset.filter_congr (fun x _ => by rw [← hq]; exact ec2 h'.1 hD' x)
  rw [f1, f1', h.1.compose_first_window hD, h'.1.compose_first_window hD', translate_translate]
    at h1
  rw [f2, f2', h.1.compose_last_window hD, h'.1.compose_last_window hD', translate_translate]
    at h2
  have tc : ∀ {a b : ℤ × ℤ} {A B : Diagram}, translate a A = translate b B →
      B = translate (-b + a) A := by
    intro a b A B hh
    have : translate (-b) (translate b B) = B := by
      rw [translate_translate]; simp [translate_zero]
    rw [← this, ← hh, translate_translate]
  rw [hwn] at h2
  have hs := h.span_eq
  have hs' := h'.span_eq
  have hws := h.width_lt_period
  have hws' := h'.width_lt_period
  have hs1 := h.lo_w_eq_hi_w
  have hs1' := h'.lo_w_eq_hi_w
  unfold lo hi widthZ at hs1 hs1'
  rw [hwn] at hs1'
  exact eq_translate_of_windows (E := ω.E) (E' := ω'.E) (q := ω.period) (w := (ω.width : ℤ))
    h.isConnectedSkew_E h'.isConnectedSkew_E (by unfold widthZ at hs; exact hs)
    (by unfold widthZ at hs'; rw [hq, hwn] at hs'; exact hs') (by have := h.width_pos; omega)
    (by unfold widthZ at hws; exact hws) hs1 hs1'
    (by have := (tc h1).symm; rw [hq] at this; exact this) (tc h2).symm

/-- First window as a membership slice: a cell of content at most `c₀ + q - 1` lies in the
composite iff its translate by `-origin` of the southwest cell of `D` lies in `E`. -/
theorem IsLegal.mem_compose_first (hω : ω.IsLegal) (hD : IsConnectedSkew D) {x : ℤ × ℤ}
    (hx : content x ≤ minContent ω.E + minContent D * ω.period + ω.period - 1) :
    x ∈ ω.compose D ↔ x - ω.origin D (sw D) ∈ ω.E := by
  have hw := hω.compose_first_window hD
  have hDne := hD.2.1
  have hco : content (ω.origin D (sw D)) = minContent D * ω.period := by
    rw [content_origin, content_sw hDne]
  have := congrArg (fun S => x ∈ S) hw
  simp only [Finset.mem_filter, mem_translate, eq_iff_iff] at this
  have hc : content (x - ω.origin D (sw D)) ≤ minContent ω.E + ω.period - 1 := by
    rw [content_sub, hco]; omega
  constructor
  · intro hxP
    exact ((this.mp ⟨hxP, hx⟩)).1
  · intro hxE
    exact (this.mpr ⟨hxE, hc⟩).1

/-- Last window as a membership slice. -/
theorem IsLegal.mem_compose_last (hω : ω.IsLegal) (hD : IsConnectedSkew D) {x : ℤ × ℤ}
    (hx : minContent ω.E + maxContent D * ω.period + ω.width ≤ content x) :
    x ∈ ω.compose D ↔ x - ω.origin D (ne D) ∈ ω.E := by
  have hw := hω.compose_last_window hD
  have hDne := hD.2.1
  have hco : content (ω.origin D (ne D)) = maxContent D * ω.period := by
    rw [content_origin, content_ne hDne]
  have := congrArg (fun S => x ∈ S) hw
  simp only [Finset.mem_filter, mem_translate, eq_iff_iff] at this
  have hc : minContent ω.E + ω.width ≤ content (x - ω.origin D (ne D)) := by
    rw [content_sub, hco]; omega
  constructor
  · intro hxP
    exact ((this.mp ⟨hxP, hx⟩)).1
  · intro hxE
    exact (this.mpr ⟨hxE, hc⟩).1

end MarkedInner

end SkewGluing
