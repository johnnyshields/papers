import SkewGluing.Aligned.Statement
import SkewGluing.Aligned.Lattice
import SkewGluing.Invariance

/-!
# The lattice map and reassociation of an ordinary `ω` with a mixed mark

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-reassociation`, `eq:gluing-ordinary-endpoints`).

The lattice map `lat` of an ordinary mark is injective and additive, and private sampling at the
singleton diagonal `w` of `E` reads `V` off `U = V ∘_ω E`.  For an ordinary `ω` and marks `μ`,
`η` of a mixed case whose displacement and upper copy are related through `lat`, the identity
`C ∘_η U = (C ∘_μ V) ∘_ω E` holds for every connected `C`
(`compose_reassoc_mixed_sign_one`, `compose_reassoc_mixed_sign_neg`).  `lowerMark` is the
candidate lower mark `(V, V ∩ (V - z), z)`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

namespace MixedEta

variable {ω η : MarkedInner} {V : Diagram}

theorem ordSign_cases (ω : MarkedInner) : ω.ordSign = 1 ∨ ω.ordSign = -1 := by
  unfold ordSign; split_ifs <;> simp

theorem lat_fst (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.lat t).1 = content t * ω.v.1 + ω.ordSign * t.1 := by
  unfold lat eCell; simp

theorem lat_snd (ω : MarkedInner) (t : ℤ × ℤ) :
    (ω.lat t).2 = content t * ω.v.2 + ω.ordSign * t.1 := by
  unfold lat eCell; simp

theorem content_lat (ω : MarkedInner) (t : ℤ × ℤ) :
    content (ω.lat t) = content t * ω.period := by
  have h1 := lat_fst ω t
  have h2 := lat_snd ω t
  have : content (ω.lat t) = (ω.lat t).2 - (ω.lat t).1 := rfl
  rw [this, h1, h2]
  simp only [period, content]; ring

theorem lat_zero (ω : MarkedInner) : ω.lat 0 = 0 := by
  unfold lat; simp [content]

theorem lat_neg (ω : MarkedInner) (t : ℤ × ℤ) : ω.lat (-t) = -ω.lat t := by
  have h := ω.lat_add t (-t)
  rw [add_neg_cancel, lat_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem lat_sub (ω : MarkedInner) (t u : ℤ × ℤ) : ω.lat (t - u) = ω.lat t - ω.lat u := by
  rw [sub_eq_add_neg, lat_add, lat_neg, ← sub_eq_add_neg]

theorem lat_injective (hq : 0 < ω.period) {t u : ℤ × ℤ} (h : ω.lat t = ω.lat u) : t = u := by
  have hc := congrArg content h
  rw [content_lat, content_lat] at hc
  have hcu : content t = content u := by
    have := mul_right_cancel₀ hq.ne' hc
    exact this
  have h1 := congrArg Prod.fst h
  rw [lat_fst, lat_fst, hcu] at h1
  have hs := ordSign_cases ω
  have h2 : t.1 = u.1 := by rcases hs with hs | hs <;> rw [hs] at h1 <;> omega
  unfold content at hcu
  ext <;> omega

/-! ### Private sampling -/

theorem lo_width_eq_hi_width (hω : ω.IsLegal) : ω.lo ω.widthZ = ω.hi ω.widthZ := by
  by_cases hW : ω.W = ∅
  · have h : ω.IsLegalEmpty := ⟨hω, hW⟩
    have := h.width_zero
    rw [this]
    exact h.ends.1
  · exact (show ω.IsLegalNonempty from ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩).lo_w_eq_hi_w

/-- The cell of the singleton private diagonal `w` of `E`. -/
def privCell (ω : MarkedInner) : ℤ × ℤ := ω.cell ω.widthZ (ω.lo ω.widthZ)

theorem content_privCell (ω : MarkedInner) : content (privCell ω) = minContent ω.E + ω.widthZ :=
  ω.content_cell _ _

theorem contents_E (hω : ω.IsLegal) :
    contents ω.E = Finset.Icc (minContent ω.E) (minContent ω.E + ω.period + ω.widthZ - 1) :=
  hω.1.contents_eq

theorem privCell_mem (hω : ω.IsLegal) : privCell ω ∈ ω.E := by
  have hq := hω.period_pos
  have hwq : ω.widthZ < ω.period := hω.2.2.1.2
  have hw0 : 0 ≤ ω.widthZ := by unfold widthZ; positivity
  have hk : minContent ω.E + ω.widthZ ∈ contents ω.E := by
    rw [contents_E hω, Finset.mem_Icc]; omega
  have := diagLo_mem hk
  have e : privCell ω = (diagLo ω.E (minContent ω.E + ω.widthZ),
      diagLo ω.E (minContent ω.E + ω.widthZ) + (minContent ω.E + ω.widthZ)) := rfl
  rw [e]; exact this

theorem content_privCell_add_lat (ω : MarkedInner) (t : ℤ × ℤ) :
    content (privCell ω + ω.lat t) = minContent ω.E + ω.widthZ + content t * ω.period := by
  rw [content_add, content_privCell, content_lat]

theorem privCell_add_lat_mem (hω : ω.IsLegal) {t : ℤ × ℤ} :
    privCell ω + ω.lat t ∈ ω.E ↔ t = 0 := by
  have hq := hω.period_pos
  have hwq : ω.widthZ < ω.period := hω.2.2.1.2
  have hw0 : 0 ≤ ω.widthZ := by unfold widthZ; positivity
  constructor
  · intro h
    have hk : content (privCell ω + ω.lat t) ∈ contents ω.E := content_mem_contents h
    rw [contents_E hω, Finset.mem_Icc, content_privCell_add_lat] at hk
    have hct : content t = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hg
      · have : content t * ω.period ≤ -ω.period := by nlinarith
        omega
      · have : ω.period ≤ content t * ω.period := by nlinarith
        omega
    have hcc : content (privCell ω + ω.lat t) = minContent ω.E + ω.widthZ := by
      rw [content_privCell_add_lat, hct]; ring
    have hs := lo_width_eq_hi_width hω
    have hl : diagLo ω.E (minContent ω.E + ω.widthZ) ≤ (privCell ω + ω.lat t).1 :=
      diagLo_le h (by rw [← hcc]; rfl)
    have hh : (privCell ω + ω.lat t).1 ≤ diagHi ω.E (minContent ω.E + ω.widthZ) :=
      le_diagHi h (by rw [← hcc]; rfl)
    have hlo : ω.lo ω.widthZ = diagLo ω.E (minContent ω.E + ω.widthZ) := rfl
    have hhi : ω.hi ω.widthZ = diagHi ω.E (minContent ω.E + ω.widthZ) := rfl
    have hfst : (privCell ω + ω.lat t).1 = ω.lo ω.widthZ + (ω.lat t).1 := rfl
    have h1 := lat_fst ω t
    have hsg := ordSign_cases ω
    have ht1 : t.1 = 0 := by
      rw [hfst, h1, hct] at hh
      rw [hfst, h1, hct] at hl
      rcases hsg with hs' | hs' <;> rw [hs'] at hl hh <;> omega
    have hct' : t.2 - t.1 = 0 := hct
    ext <;> simp <;> omega
  · rintro rfl
    rw [lat_zero, add_zero]
    exact privCell_mem hω

/-- **Private sampling.**  The cell `P + L_ω(y)`, with `P` the private cell of `E`, lies in
`V ∘_ω E` exactly when `y ∈ V`. -/
theorem sample_mem (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed) (hV : V.Nonempty)
    {y : ℤ × ℤ} : privCell ω + ω.lat y ∈ ω.compose V ↔ y ∈ V := by
  rw [compose_of_ordinary hV hord]
  constructor
  · rintro ⟨d, hd, hx⟩
    rw [mem_translate, origin_eq_lat hord] at hx
    have e : privCell ω + ω.lat y - ω.lat d = privCell ω + ω.lat (y - d) := by
      rw [lat_sub]; abel
    rw [e, privCell_add_lat_mem hω] at hx
    rwa [sub_eq_zero.mp hx] 
  · intro hy
    refine ⟨y, hy, ?_⟩
    rw [mem_translate, origin_eq_lat hord]
    have e : privCell ω + ω.lat y - ω.lat y = privCell ω := by abel
    rw [e]; exact privCell_mem hω

/-! ### The reassociation identity for an ordinary `ω` of case (a) -/

theorem mem_compose_lat (hord : ¬ ω.case.IsMixed) {A : Diagram} (hA : A.Nonempty)
    {x : ℤ × ℤ} : x ∈ ω.compose A ↔ ∃ y ∈ A, x - ω.lat y ∈ ω.E := by
  rw [compose_of_ordinary hA hord]
  simp only [mem_translate, origin_eq_lat hord]

theorem mem_compose_translate (hord : ¬ ω.case.IsMixed) {A : Diagram} (hA : A.Nonempty)
    (t : ℤ × ℤ) {x : ℤ × ℤ} :
    x ∈ ω.compose (SkewGluing.translate t A) ↔ x - ω.lat t ∈ ω.compose A := by
  have hA' : (SkewGluing.translate t A).Nonempty := hA.image _
  rw [mem_compose_lat hord hA', mem_compose_lat hord hA]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨y - t, ?_, ?_⟩
    · simpa [mem_translate] using hy
    · rw [lat_sub]
      have e : x - ω.lat t - (ω.lat y - ω.lat t) = x - ω.lat y := by abel
      rw [e]; exact hx
  · rintro ⟨y, hy, hx⟩
    refine ⟨y + t, ?_, ?_⟩
    · rw [mem_translate]; simpa using hy
    · rw [lat_add]
      have e : x - (ω.lat y + ω.lat t) = x - ω.lat t - ω.lat y := by abel
      rw [e]; exact hx

theorem lat_smul (ω : MarkedInner) (n : ℤ) (t : ℤ × ℤ) : ω.lat (n • t) = n • ω.lat t := by
  unfold lat
  ext <;> simp [content, eCell] <;> ring

theorem lat_origin_of_sign_one (hs : ω.ordSign = 1) {μ : MarkedInner}
    (hv : η.v = ω.lat μ.v) (hc : η.case = μ.case) (C : Diagram) (d : ℤ × ℤ) :
    ω.lat (μ.origin C d) = η.origin C d := by
  have he : ω.lat eCell = eCell := by rw [lat_eCell, hs]; simp
  unfold origin
  rw [hc, hv]
  cases μ.case <;> simp only [lat_add, lat_sub, lat_smul, he]

theorem lat_supplementalShift_of_sign_one (hs : ω.ordSign = 1) {μ : MarkedInner}
    (hc : η.case = μ.case) : ω.lat μ.supplementalShift = η.supplementalShift := by
  have he : ω.lat eCell = eCell := by rw [lat_eCell, hs]; simp
  unfold supplementalShift
  rw [hc]
  cases μ.case <;> simp only [lat_neg, he]

theorem sameRibbon_iff_of_case {μ : MarkedInner} (hc : η.case = μ.case) (C : Diagram)
    (d : ℤ × ℤ) : η.SameRibbon C d ↔ μ.SameRibbon C d := by
  unfold SameRibbon
  rw [hc]

/-- Membership in `ω ∘ (μ ∘ C)` for an ordinary `ω`: the copies of `U = V ∘_ω E` placed at the
lattice images of the origins of `μ`, and the supplemental copies of `ω ∘ W₊`. -/
theorem mem_compose_compose (hord : ¬ ω.case.IsMixed) {μ : MarkedInner} (hV : V.Nonempty)
    (hμV : μ.E = V) (hWne : μ.upper.Nonempty) {C : Diagram} (hC : C.Nonempty) {x : ℤ × ℤ} :
    x ∈ ω.compose (μ.compose C) ↔
      (∃ d ∈ C, x - ω.lat (μ.origin C d) ∈ ω.compose V) ∨
      ∃ d ∈ C, μ.SameRibbon C d ∧
        x - ω.lat (μ.origin C d + μ.supplementalShift) ∈ ω.compose μ.upper := by
  have hX : (μ.compose C).Nonempty := by
    obtain ⟨d, hd⟩ := hC
    obtain ⟨y, hy⟩ := hV
    refine ⟨y + μ.origin C d, ?_⟩
    rw [mem_compose ⟨d, hd⟩]
    exact Or.inl ⟨d, hd, by rw [mem_translate, hμV]; simpa using hy⟩
  rw [mem_compose_lat hord hX]
  constructor
  · rintro ⟨y, hy, hP⟩
    rw [mem_compose hC] at hy
    rcases hy with ⟨d, hd, hyd⟩ | ⟨d, hd, hr, hyd⟩
    · left
      refine ⟨d, hd, ?_⟩
      rw [mem_compose_lat hord hV]
      refine ⟨y - μ.origin C d, ?_, ?_⟩
      · rw [mem_translate, hμV] at hyd; exact hyd
      · rw [lat_sub]
        have e : x - ω.lat (μ.origin C d) - (ω.lat y - ω.lat (μ.origin C d)) =
            x - ω.lat y := by abel
        rw [e]; exact hP
    · right
      refine ⟨d, hd, hr, ?_⟩
      rw [mem_compose_lat hord hWne]
      refine ⟨y - (μ.origin C d + μ.supplementalShift), ?_, ?_⟩
      · rw [mem_translate] at hyd; exact hyd
      · rw [lat_sub]
        have e : x - ω.lat (μ.origin C d + μ.supplementalShift) -
            (ω.lat y - ω.lat (μ.origin C d + μ.supplementalShift)) = x - ω.lat y := by abel
        rw [e]; exact hP
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hr, hx⟩)
    · rw [mem_compose_lat hord hV] at hx
      obtain ⟨y, hy, hP⟩ := hx
      refine ⟨y + μ.origin C d, ?_, ?_⟩
      · rw [mem_compose hC]
        exact Or.inl ⟨d, hd, by rw [mem_translate, hμV]; simpa using hy⟩
      · rw [lat_add]
        have e : x - (ω.lat y + ω.lat (μ.origin C d)) = x - ω.lat (μ.origin C d) - ω.lat y := by
          abel
        rw [e]; exact hP
    · rw [mem_compose_lat hord hWne] at hx
      obtain ⟨y, hy, hP⟩ := hx
      refine ⟨y + (μ.origin C d + μ.supplementalShift), ?_, ?_⟩
      · rw [mem_compose hC]
        exact Or.inr ⟨d, hd, hr, by rw [mem_translate]; simpa using hy⟩
      · rw [lat_add]
        have e : x - (ω.lat y + ω.lat (μ.origin C d + μ.supplementalShift)) =
            x - ω.lat (μ.origin C d + μ.supplementalShift) - ω.lat y := by abel
        rw [e]; exact hP

/-- **`eq:gluing-reassociation`, ordinary `ω` of case (a), mixed marks of the same case.**  If
`η` on `U = V ∘_ω E` has displacement `L_ω(v_μ)`, the same mixed case as `μ`, and `W_η + v_η`
is `W_μ + v_μ` composed with `ω`, then `C ∘_η U = (C ∘_μ V) ∘_ω E` for every nonempty `C`. -/
theorem compose_reassoc_mixed_sign_one (hord : ¬ ω.case.IsMixed) (hs : ω.ordSign = 1)
    {μ : MarkedInner} (hV : V.Nonempty) (hμV : μ.E = V) (hU : η.E = ω.compose V)
    (hv : η.v = ω.lat μ.v) (hc : η.case = μ.case) (hWne : μ.upper.Nonempty)
    (hup : η.upper = ω.compose μ.upper) {C : Diagram} (hC : C.Nonempty) :
    η.compose C = ω.compose (μ.compose C) := by
  ext x
  rw [mem_compose_compose hord hV hμV hWne hC, mem_compose hC]
  have hl : ∀ d, ω.lat (μ.origin C d) = η.origin C d := fun d =>
    lat_origin_of_sign_one hs hv hc C d
  have hsh := lat_supplementalShift_of_sign_one hs hc
  have hl2 : ∀ d, ω.lat (μ.origin C d + μ.supplementalShift) =
      η.origin C d + η.supplementalShift := by
    intro d; rw [lat_add, hl, hsh]
  simp only [hl, hl2, mem_translate, hU, hup, sameRibbon_iff_of_case hc]

/-- A cell of a connected skew diagram, with its diagonal data. -/
theorem cell_data {C : Diagram} (hC : IsConnectedSkew C) {d : ℤ × ℤ} (hd : d ∈ C) :
    content d ∈ contents C ∧ diagLo C (content d) ≤ d.1 ∧ d.1 ≤ diagHi C (content d) := by
  have hs := isConnectedSkew_iff_diagonal.mp hC
  have := hs.mem_iff (k := content d) (i := d.1)
  have e : (d.1, d.1 + content d) = d := by
    ext <;> simp [content]
  rw [e] at this
  exact this.mp hd

theorem mk_cell {C : Diagram} (hC : IsConnectedSkew C) {c i : ℤ} (hc : c ∈ contents C)
    (h1 : diagLo C c ≤ i) (h2 : i ≤ diagHi C c) : (i, i + c) ∈ C := by
  have hs := isConnectedSkew_iff_diagonal.mp hC
  exact hs.mem_iff.mpr ⟨hc, h1, h2⟩

theorem content_mk (i c : ℤ) : content (i, i + c) = c := by simp [content]

theorem b_core {C : Diagram} (hC : IsConnectedSkew C) (S T : ℤ → ℤ → Prop)
    (hT1 : ∀ c k, T c k → S c k) (hT2 : ∀ c k, T c k → S (c + 1) k) :
    ((∃ d ∈ C, S (content d) (diagHi C (content d) - d.1)) ∨
      (∃ d ∈ C, (d.1 - 1, d.2) ∈ C ∧
        diagHi C (content d) - d.1 = diagHi C (content d + 1) - (d.1 - 1) ∧
        T (content d) (diagHi C (content d) - d.1 + 1))) ↔
    ((∃ d ∈ C, S (content d) (d.1 - diagLo C (content d))) ∨
      (∃ d ∈ C, (d.1 - 1, d.2) ∈ C ∧
        d.1 - diagLo C (content d) = (d.1 - 1) - diagLo C (content d + 1) ∧
        T (content d) (d.1 - diagLo C (content d) + 1))) := by
  have hs := isConnectedSkew_iff_diagonal.mp hC
  -- a cell of the diagonal `c` at distance `k` from the southeast end / northwest end
  have fromHi : ∀ c k : ℤ, c ∈ contents C → 0 ≤ k → k ≤ diagHi C c - diagLo C c →
      ∃ d ∈ C, content d = c ∧ diagHi C c - d.1 = k := by
    intro c k hc h0 h1
    refine ⟨(diagHi C c - k, diagHi C c - k + c), mk_cell hC hc (by omega) (by omega), ?_, ?_⟩
    · exact content_mk _ _
    · simp
  have fromLo : ∀ c k : ℤ, c ∈ contents C → 0 ≤ k → k ≤ diagHi C c - diagLo C c →
      ∃ d ∈ C, content d = c ∧ d.1 - diagLo C c = k := by
    intro c k hc h0 h1
    refine ⟨(diagLo C c + k, diagLo C c + k + c), mk_cell hC hc (by omega) (by omega), ?_, ?_⟩
    · exact content_mk _ _
    · simp
  have north : ∀ d ∈ C, (d.1 - 1, d.2) ∈ C → content d + 1 ∈ contents C ∧
      diagLo C (content d + 1) ≤ d.1 - 1 ∧ d.1 - 1 ≤ diagHi C (content d + 1) := by
    intro d hd hn
    have := cell_data hC hn
    have e : content (d.1 - 1, d.2) = content d + 1 := by simp [content]; ring
    rw [e] at this
    exact this
  have bits : ∀ c, c ∈ contents C → c + 1 ∈ contents C →
      (diagLo C c - diagLo C (c + 1) = 0 ∨ diagLo C c - diagLo C (c + 1) = 1) ∧
      (diagHi C c - diagHi C (c + 1) = 0 ∨ diagHi C c - diagHi C (c + 1) = 1) := by
    intro c h1 h2
    have := hs.2.2.2.1 (c + 1) h2 (by simpa using h1)
    simp only [bitA, bitB, Finset.mem_insert, Finset.mem_singleton] at this
    simpa using this
  have hmainEq : (∃ d ∈ C, S (content d) (diagHi C (content d) - d.1)) ↔
      (∃ d ∈ C, S (content d) (d.1 - diagLo C (content d))) := by
    constructor
    · rintro ⟨d, hd, hS⟩
      obtain ⟨h0, h1, h2⟩ := cell_data hC hd
      obtain ⟨d', hd', h3, h4⟩ := fromLo (content d) (diagHi C (content d) - d.1) h0
        (by omega) (by omega)
      exact ⟨d', hd', by rw [h3, h4]; exact hS⟩
    · rintro ⟨d, hd, hS⟩
      obtain ⟨h0, h1, h2⟩ := cell_data hC hd
      obtain ⟨d', hd', h3, h4⟩ := fromHi (content d) (d.1 - diagLo C (content d)) h0
        (by omega) (by omega)
      exact ⟨d', hd', by rw [h3, h4]; exact hS⟩
  constructor
  · rintro (hS | ⟨d, hd, hn, hr, hT⟩)
    · exact Or.inl (hmainEq.mp hS)
    · obtain ⟨h0, h1, h2⟩ := cell_data hC hd
      obtain ⟨n0, n1, n2⟩ := north d hd hn
      have hb := bits (content d) h0 n0
      by_cases hlt : diagLo C (content d) < d.1
      · left
        refine hmainEq.mp ⟨(d.1 - 1, d.1 - 1 + content d), mk_cell hC h0 (by omega) (by omega), ?_⟩
        rw [content_mk]
        have := hT1 _ _ hT
        simp only
        have e : diagHi C (content d) - (d.1 - 1) = diagHi C (content d) - d.1 + 1 := by ring
        rw [e]; exact this
      · right
        have hi : d.1 = diagLo C (content d) := by omega
        have hlo1 : diagLo C (content d + 1) = diagLo C (content d) - 1 := by omega
        have hhi1 : diagHi C (content d + 1) = diagHi C (content d) - 1 := by omega
        have hle := diagLo_le_diagHi h0
        refine ⟨(diagHi C (content d), diagHi C (content d) + content d), ?_, ?_, ?_, ?_⟩
        · exact mk_cell hC h0 (by omega) (le_refl _)
        · have : (diagHi C (content d) - 1, diagHi C (content d) + content d) =
              (diagHi C (content d) - 1, diagHi C (content d) - 1 + (content d + 1)) := by
            ext <;> simp
          simp only
          rw [this]
          exact mk_cell hC n0 (by omega) (by omega)
        · rw [content_mk]
          simp only
          omega
        · rw [content_mk]
          simp only
          have e : diagHi C (content d) - diagLo C (content d) + 1 =
              diagHi C (content d) - d.1 + 1 := by omega
          rw [e]; exact hT
  · rintro (hS | ⟨d, hd, hn, hr, hT⟩)
    · exact Or.inl (hmainEq.mpr hS)
    · obtain ⟨h0, h1, h2⟩ := cell_data hC hd
      obtain ⟨n0, n1, n2⟩ := north d hd hn
      have hb := bits (content d) h0 n0
      by_cases hlt : d.1 < diagHi C (content d)
      · left
        refine hmainEq.mpr ⟨(d.1 + 1, d.1 + 1 + content d), mk_cell hC h0 (by omega) (by omega), ?_⟩
        rw [content_mk]
        have := hT1 _ _ hT
        simp only
        have e : d.1 + 1 - diagLo C (content d) = d.1 - diagLo C (content d) + 1 := by ring
        rw [e]; exact this
      · have hi : d.1 = diagHi C (content d) := by omega
        have hlo1 : diagLo C (content d + 1) = diagLo C (content d) - 1 := by omega
        have hle := diagLo_le_diagHi h0
        rcases hb.2 with hb1 | hb1
        · -- `h_{c+1} = h_c`: the supplemental piece lies in the diagonal `c + 1`
          left
          have hT' := hT2 _ _ hT
          refine ⟨(diagLo C (content d) - 1, diagLo C (content d) - 1 + (content d + 1)), ?_, ?_⟩
          · exact mk_cell hC n0 (by omega) (by omega)
          · rw [content_mk]
            simp only
            have e : diagHi C (content d + 1) - (diagLo C (content d) - 1) =
                d.1 - diagLo C (content d) + 1 := by omega
            rw [e]; exact hT'
        · right
          refine ⟨(diagLo C (content d), diagLo C (content d) + content d), ?_, ?_, ?_, ?_⟩
          · exact mk_cell hC h0 (le_refl _) (by omega)
          · have : (diagLo C (content d) - 1, diagLo C (content d) + content d) =
                (diagLo C (content d) - 1, diagLo C (content d) - 1 + (content d + 1)) := by
              ext <;> simp
            simp only
            rw [this]
            exact mk_cell hC n0 (by omega) (by omega)
          · rw [content_mk]
            simp only
            omega
          · rw [content_mk]
            simp only
            have e : diagHi C (content d) - diagLo C (content d) + 1 =
                d.1 - diagLo C (content d) + 1 := by omega
            rw [e]; exact hT


theorem lat_origin_c_of_sign_neg (hs : ω.ordSign = -1) {μ : MarkedInner}
    (hv : η.v = ω.lat μ.v) (hcμ : μ.case = .c) (C : Diagram) (d : ℤ × ℤ) :
    ω.lat (μ.origin C d) = content d • η.v - (d.1 - diagLo C (content d)) • eCell := by
  have he : ω.lat eCell = -eCell := by rw [lat_eCell, hs]; simp
  unfold origin
  rw [hcμ, hv]
  simp only [lat_add, lat_smul, he, smul_neg]
  abel

theorem compose_reassoc_mixed_sign_neg (hord : ¬ ω.case.IsMixed) (hs : ω.ordSign = -1)
    {μ : MarkedInner} (hV : V.Nonempty) (hμV : μ.E = V) (hU : η.E = ω.compose V)
    (hv : η.v = ω.lat μ.v) (hcη : η.case = .d) (hcμ : μ.case = .c) (hWne : μ.upper.Nonempty)
    (hup : η.upper = ω.compose μ.upper) (hupE : η.upper ⊆ η.E) (hWE : η.W ⊆ η.E)
    {C : Diagram} (hC : IsConnectedSkew C) :
    η.compose C = ω.compose (μ.compose C) := by
  have hCne := hC.2.1
  ext x
  rw [mem_compose_compose hord hV hμV hWne hCne, mem_compose hCne]
  have he : ω.lat eCell = -eCell := by rw [lat_eCell, hs]; simp
  have hsrη : ∀ d : ℤ × ℤ, η.SameRibbon C d ↔ ((d.1 - 1, d.2) ∈ C ∧
      diagHi C (content d) - d.1 = diagHi C (content d + 1) - (d.1 - 1)) := by
    intro d; unfold SameRibbon; rw [hcη]
  have hsrμ : ∀ d : ℤ × ℤ, μ.SameRibbon C d ↔ ((d.1 - 1, d.2) ∈ C ∧
      d.1 - diagLo C (content d) = (d.1 - 1) - diagLo C (content d + 1)) := by
    intro d; unfold SameRibbon; rw [hcμ]
  have hoη : ∀ d : ℤ × ℤ, η.origin C d =
      content d • η.v - (diagHi C (content d) - d.1) • eCell := by
    intro d; unfold origin; rw [hcη]
  have hσμ : μ.supplementalShift = eCell := by simp [supplementalShift, hcμ]
  have hση : η.supplementalShift = -eCell := by simp [supplementalShift, hcη]
  have key := b_core hC (fun c k => x - c • η.v + k • eCell ∈ η.E)
    (fun c k => x - c • η.v + k • eCell ∈ η.upper)
    (fun c k h => hupE h) (by
      intro c k h
      have h1 : x - c • η.v + k • eCell - η.v ∈ η.W := by
        have := mem_translate.mp (show x - c • η.v + k • eCell ∈ η.upper from h)
        simpa using this
      have e : x - (c + 1) • η.v + k • eCell = x - c • η.v + k • eCell - η.v := by
        rw [add_smul, one_smul]; abel
      change x - (c + 1) • η.v + k • eCell ∈ η.E
      rw [e]; exact hWE h1)
  simp only [hsrη, hsrμ, hoη, lat_origin_c_of_sign_neg hs hv hcμ, hσμ, hση, lat_add, he,
    ← hU, ← hup, mem_translate] at key ⊢
  have e1 : ∀ (a : ℤ × ℤ) (k : ℤ), x - (a - k • eCell) = x - a + k • eCell := by
    intro a k; abel
  have e2 : ∀ (a : ℤ × ℤ) (k : ℤ), x - (a - k • eCell + -eCell) = x - a + (k + 1) • eCell := by
    intro a k; rw [add_smul, one_smul]; abel
  simp only [e1, e2, and_assoc]
  exact key


/-! ### The lower mark and the assembly -/

/-- The candidate lower mark of `lem:gluing-aligned` on `V`: the lower copy `Z = V ∩ (V - z)`,
the displacement `z` and the attachment case `κ`. -/
def lowerMark (V : Diagram) (z : ℤ × ℤ) (κ : AttachCase) : MarkedInner where
  E := V
  W := V.filter fun y => y + z ∈ V
  v := z
  case := κ

/-- The attachment case of the lower mark: that of `η` for `ω` of case (a), the interchanged
(c)/(d) for `ω` of case (b), where `L_ω(e) = -e`. -/
def lowerCase (ω : MarkedInner) : AttachCase := if ω.ordSign = 1 then .d else .c

theorem exists_lat_preimage {a : ℤ} (ha : content η.v = a * ω.period) :
    ∃ z : ℤ × ℤ, ω.lat z = η.v ∧ content z = a := by
  have hs := ordSign_cases ω
  refine ⟨(ω.ordSign * (η.v.1 - a * ω.v.1), ω.ordSign * (η.v.1 - a * ω.v.1) + a), ?_, ?_⟩
  · have hc : η.v.2 - η.v.1 = a * ω.period := ha
    have hper : ω.period = ω.v.2 - ω.v.1 := rfl
    ext
    · rw [lat_fst]
      simp only [content]
      rcases hs with h | h <;> rw [h] <;> ring
    · rw [lat_snd]
      have hc' : η.v.2 - η.v.1 = a * (ω.v.2 - ω.v.1) := by rw [← hper]; exact hc
      simp only [content]
      rcases hs with h | h <;> rw [h] <;> linear_combination (-1 : ℤ) * hc'
  · simp [content]


end MixedEta

end MarkedInner

end SkewGluing
