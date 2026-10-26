-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/Local/Middle.lean
import GluingCore.Local.Tails

/-!
# The middle of a legal mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-local`,
assertions (1) and (2)).

For a legal mark with a nonempty copy this file proves: the middle has at most one cell on each
marked diagonal; the private diagonals `w` and `q - 1` are singletons; the middle occupies the
contents `[s, q + t - 1]` with `1 ≤ s ≤ w` and `0 ≤ t < w`, where the lower tail lives on the
marked residues `[s, w - 1]` and the upper tail on `[0, t - 1]`; the side of each tail is fixed by
the attachment case; for mixed marks `t < s`; in case (d) both copies are southeast-justified,
and in case (c) northwest-justified.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω : MarkedInner}

theorem IsLegalNonempty.upperH_dHi (h : ω.IsLegalNonempty) (hH : ω.UpperH) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.dHi a ≤ 0 := by
  have hH' : ω.rotate.LowerH := (lowerH_rotate ω).mpr hH
  have := h.rotate.lowerH_dLo hH' (a := ω.widthZ - 1 - a) (by omega)
    (by rw [widthZ_rotate]; omega)
  rw [h.dLo_rotate] at this
  exact this

theorem IsLegalNonempty.upperV_dLo (h : ω.IsLegalNonempty) (hV : ω.UpperV) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : 0 ≤ ω.dLo a := by
  have hV' : ω.rotate.LowerV := (lowerV_rotate ω).mpr hV
  have := h.rotate.lowerV_dHi hV' (a := ω.widthZ - 1 - a) (by omega)
    (by rw [widthZ_rotate]; omega)
  rw [h.dHi_rotate] at this
  exact this

/-- The attachment case read off `ω`: the attachments hold for the stated case. -/
theorem IsLegalNonempty.attach (h : ω.IsLegalNonempty) : ω.AttachmentMatches :=
  h.nonemptyMark.2.2.2.2.2.2

/-- Sides of the middle tails, case (a): lower tail southeast, upper tail northwest. -/
theorem IsLegalNonempty.sides_a (h : ω.IsLegalNonempty) (hc : ω.case = .a) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.dLo a ≤ 0 ∧ ω.dHi a ≤ 0 := by
  obtain ⟨hl, hu⟩ := h.attach.1 hc
  exact ⟨h.lowerH_dLo hl h0 h1, h.upperH_dHi hu h0 h1⟩

/-- Sides of the middle tails, case (b): lower tail northwest, upper tail southeast. -/
theorem IsLegalNonempty.sides_b (h : ω.IsLegalNonempty) (hc : ω.case = .b) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : 0 ≤ ω.dLo a ∧ 0 ≤ ω.dHi a := by
  obtain ⟨hl, hu⟩ := h.attach.2.1 hc
  exact ⟨h.upperV_dLo hu h0 h1, h.lowerV_dHi hl h0 h1⟩

/-- Sides of the middle tails, case (c): both tails southeast, so `ℓ_{a+q} = ℓ_a + p`. -/
theorem IsLegalNonempty.sides_c (h : ω.IsLegalNonempty) (hc : ω.case = .c) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.dLo a = 0 := by
  obtain ⟨hl, hu⟩ := h.attach.2.2.1 hc
  have := h.lowerH_dLo hl h0 h1
  have := h.upperV_dLo hu h0 h1
  omega

/-- Sides of the middle tails, case (d): both tails northwest, so `h_{a+q} = h_a + p`. -/
theorem IsLegalNonempty.sides_d (h : ω.IsLegalNonempty) (hc : ω.case = .d) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.dHi a = 0 := by
  obtain ⟨hl, hu⟩ := h.attach.2.2.2 hc
  have := h.lowerV_dHi hl h0 h1
  have := h.upperH_dHi hu h0 h1
  omega

theorem IsLegalNonempty.dLo_step (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 1 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.dLo a - ω.dLo (a - 1) ≤ 1 ∧ -1 ≤ ω.dLo a - ω.dLo (a - 1) := by
  have hq := h.width_lt_period
  have b1 := h.bit_lo' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
  have b2 := h.bit_lo' (a := a - 1 + ω.period) (b := a + ω.period) (by ring) (by omega)
    (by omega)
  unfold dLo
  omega

theorem IsLegalNonempty.dHi_step (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 1 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.dHi a - ω.dHi (a - 1) ≤ 1 ∧ -1 ≤ ω.dHi a - ω.dHi (a - 1) := by
  have hq := h.width_lt_period
  have b1 := h.bit_hi' (a := a - 1) (b := a) (by ring) (by omega) (by omega)
  have b2 := h.bit_hi' (a := a - 1 + ω.period) (b := a + ω.period) (by ring) (by omega)
    (by omega)
  unfold dHi
  omega

/-- No lower tail on the first marked diagonal and no upper tail on the last one. -/
theorem IsLegalNonempty.not_tail_ends (h : ω.IsLegalNonempty) :
    ¬ ω.TailLower 0 ∧ ¬ ω.TailUpper (ω.widthZ - 1) := by
  have h1 := h.dLo_zero_le
  have h2 := h.last_dLo
  unfold TailLower TailUpper
  omega


/-! ### The phases `s` and `t` -/

/-- `s` and `t` are the middle phases: the lower tail occupies the marked residues `[s, w - 1]`
and the upper tail the residues `[0, t - 1]`. -/
def IsPhases (ω : MarkedInner) (s t : ℤ) : Prop :=
  1 ≤ s ∧ s ≤ ω.widthZ ∧ 0 ≤ t ∧ t < ω.widthZ ∧
    (∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 → (ω.TailLower a ↔ s ≤ a)) ∧
    (∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 → (ω.TailUpper a ↔ a < t))

theorem IsLegalNonempty.exists_phases (h : ω.IsLegalNonempty) : ∃ s t, ω.IsPhases s t := by
  have hw := h.width_pos
  have hnt := h.not_tail_ends
  obtain ⟨s, hs1, hs2, hs3⟩ : ∃ s, 1 ≤ s ∧ s ≤ ω.widthZ ∧
      ∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 → (ω.TailLower a ↔ s ≤ a) := by
    by_cases hex : ∃ a, 0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.TailLower a
    · obtain ⟨s, hs1, hs2, hst, hmin⟩ := h.first_tail hex
      refine ⟨s, hs1, by omega, fun a ha0 ha1 => ⟨fun hat => ?_, fun hsa => ?_⟩⟩
      · by_contra hlt
        exact hmin a ha0 (by omega) hat
      · exact h.tail_mono (by omega) hsa ha1 hst
    · refine ⟨ω.widthZ, hw, le_refl _, fun a ha0 ha1 => ⟨fun hat => ?_, fun hsa => ?_⟩⟩
      · exact absurd ⟨a, ha0, ha1, hat⟩ hex
      · omega
  obtain ⟨t, ht1, ht2, ht3⟩ : ∃ t, 0 ≤ t ∧ t < ω.widthZ ∧
      ∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 → (ω.TailUpper a ↔ a < t) := by
    by_cases hex : ∃ a, 0 ≤ a ∧ a ≤ ω.widthZ - 1 ∧ ω.TailUpper a
    · obtain ⟨m, ⟨hm0, hm1, hmt⟩, hmax⟩ := Int.exists_greatest_of_bdd
        (P := fun z => 0 ≤ z ∧ z ≤ ω.widthZ - 1 ∧ ω.TailUpper z) ⟨ω.widthZ - 1, fun z hz => hz.2.1⟩
        hex
      have hm2 : m ≠ ω.widthZ - 1 := fun he => hnt.2 (he ▸ hmt)
      refine ⟨m + 1, by omega, by omega, fun a ha0 ha1 => ⟨fun hat => ?_, fun hsa => ?_⟩⟩
      · have := hmax a ⟨ha0, ha1, hat⟩
        omega
      · exact h.tail_mono_upper ha0 (by omega) hm1 hmt
    · refine ⟨0, le_refl _, hw, fun a ha0 ha1 => ⟨fun hat => ?_, fun hsa => ?_⟩⟩
      · exact absurd ⟨a, ha0, ha1, hat⟩ hex
      · omega
  exact ⟨s, t, hs1, hs2, ht1, ht2, hs3, ht3⟩

theorem IsLegalNonempty.mem_middle_upper (h : ω.IsLegalNonempty) {b r : ℤ} (h0 : 0 ≤ b)
    (h1 : b ≤ ω.widthZ - 1) :
    ω.cell (b + ω.period) r ∈ ω.middle ↔
      (ω.lo (b + ω.period) ≤ r ∧ r ≤ ω.hi (b + ω.period)) ∧
      ¬ (ω.lo b ≤ r - ω.rowShift ∧ r - ω.rowShift ≤ ω.hi b ∧ ω.lo (b + ω.period) ≤ r ∧
        r ≤ ω.hi (b + ω.period)) := by
  have hq := h.width_lt_period
  rw [h.mem_middle, h.mem_E, h.mem_W, h.mem_upper, h.mem_W]
  constructor
  · rintro ⟨⟨_, _, h3, h4⟩, -, h6⟩
    refine ⟨⟨h3, h4⟩, fun hc => h6 ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩⟩ <;> omega
  · rintro ⟨⟨h3, h4⟩, h6⟩
    refine ⟨⟨by omega, by omega, h3, h4⟩, by omega, fun hc => h6 ⟨?_, ?_, ?_, ?_⟩⟩ <;> omega

theorem IsLegalNonempty.mem_middle_private (h : ω.IsLegalNonempty) {a r : ℤ} (h0 : ω.widthZ ≤ a)
    (h1 : a < ω.period) : ω.cell a r ∈ ω.middle ↔ ω.lo a ≤ r ∧ r ≤ ω.hi a := by
  have hw := h.width_pos
  rw [h.mem_middle_lt h1, h.mem_E, h.mem_W]
  omega

theorem IsLegalNonempty.contents_middle (h : ω.IsLegalNonempty) {s t : ℤ} (hp : ω.IsPhases s t) :
    contents ω.middle =
      Finset.Icc (minContent ω.E + s) (minContent ω.E + ω.period + t - 1) := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hp
  have hq := h.width_lt_period
  have hw := h.width_pos
  ext k
  rw [Finset.mem_Icc, mem_contents_iff]
  have hcell : ∀ r, (r, r + k) = ω.cell (k - minContent ω.E) r := by
    intro r; simp only [cell]; ext
    · rfl
    · simp only; ring
  constructor
  · rintro ⟨r, hr⟩
    rw [hcell] at hr
    set a := k - minContent ω.E with ha
    have hE := (h.mem_E).mp (h.mem_middle.mp hr).1
    by_cases hlt : a ≤ ω.widthZ - 1
    · have := h.tail_of_cell (r := r) (by omega) hlt
        (Finset.mem_sdiff.mpr ⟨(h.mem_middle.mp hr).1, (h.mem_middle.mp hr).2.1⟩)
      have := (hS a (by omega) hlt).mp this
      omega
    · by_cases hlt2 : a < ω.period
      · omega
      · have e : a = (a - ω.period) + ω.period := by ring
        rw [e, h.mem_middle_upper (by omega) (by omega)] at hr
        have hb : ω.TailUpper (a - ω.period) := by
          unfold TailUpper dLo dHi
          omega
        have := (hT _ (by omega) (by omega)).mp hb
        omega
  · rintro ⟨hk1, hk2⟩
    set a := k - minContent ω.E with ha
    by_cases hlt : a ≤ ω.widthZ - 1
    · have hat := (hS a (by omega) hlt).mpr (by omega)
      obtain ⟨r, hr⟩ := h.exists_tail_cell (by omega) hlt hat
      exact ⟨r, by rw [hcell]; exact (h.mem_middle_lt (by omega)).mpr (Finset.mem_sdiff.mp hr)⟩
    · by_cases hlt2 : a < ω.period
      · have := h.lo_le_hi (a := a) (by omega) (by omega)
        exact ⟨ω.lo a, by rw [hcell, h.mem_middle_private (by omega) hlt2]; omega⟩
      · obtain ⟨b, hbq⟩ : ∃ b, a = b + ω.period := ⟨a - ω.period, by ring⟩
        have hb := (hT b (by omega) (by omega)).mpr (by omega)
        have := h.lo_le_hi (a := b + ω.period) (by omega) (by omega)
        unfold TailUpper dLo dHi at hb
        by_cases hd : ω.lo (b + ω.period) - ω.rowShift - ω.lo b < 0
        · refine ⟨ω.lo (b + ω.period), ?_⟩
          rw [hcell, hbq, h.mem_middle_upper (by omega) (by omega)]
          omega
        · refine ⟨ω.hi (b + ω.period), ?_⟩
          rw [hcell, hbq, h.mem_middle_upper (by omega) (by omega)]
          omega


/-- **`lem:gluing-local` (1), second assertion.**  The middle has at most one cell on each marked
diagonal (the contents `[c₀, c₀ + w - 1]` of the lower copy and `[c₀ + q, c₀ + q + w - 1]` of the
upper copy). -/
theorem IsLegalNonempty.middle_thin (h : ω.IsLegalNonempty) {x y : ℤ × ℤ} (hx : x ∈ ω.middle)
    (hy : y ∈ ω.middle) (hc : content x = content y)
    (hm : content x ≤ minContent ω.E + ω.widthZ - 1 ∨ minContent ω.E + ω.period ≤ content x) :
    x = y := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨a, r, rfl⟩ := ω.exists_cell x
  obtain ⟨a', r', rfl⟩ := ω.exists_cell y
  rw [content_cell] at hm
  rw [content_cell, content_cell] at hc
  have haa : a = a' := by omega
  subst haa
  suffices hr : r = r' by rw [hr]
  by_cases hlow : a ≤ ω.widthZ - 1
  · rw [h.mem_middle_lower (by omega)] at hx hy
    obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row (a := a) (by omega) hlow
    have := h.thin_lower a (by omega) hlow
    have hint := h.interval_lower (a := a) (by omega) hlow
    unfold dLo dHi at *
    omega
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + ω.period := ⟨a - ω.period, by omega⟩
    have hxE := (h.mem_E).mp (h.mem_middle.mp hx).1
    rw [h.mem_middle_upper (by omega) (by omega)] at hx hy
    obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row (a := b) (by omega) (by omega)
    have := h.thin_upper (a := b) (by omega) (by omega)
    have hint := h.interval_upper (a := b) (by omega) (by omega)
    unfold dLo dHi at *
    omega

/-- **`lem:gluing-local` (2), mixed marks.**  For a mixed mark, `t < s`: some marked residue meets
neither middle tail.  **Differs from the paper's route.**  The paper excludes `t = s` by a
southwest/northeast cell argument; here `t < s` follows from the bounded steps of the offsets
`ℓ_{a+q} - p - ℓ_a` (or `h_{a+q} - p - h_a`), which cannot jump from `-1` to `1`. -/
theorem IsLegalNonempty.phases_lt (h : ω.IsLegalNonempty) (hmix : ω.case.IsMixed) {s t : ℤ}
    (hp : ω.IsPhases s t) : t < s := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hp
  by_contra hts
  have hts' : s ≤ t := by omega
  have hsw : s ≤ ω.widthZ - 1 := by omega
  have hTs : ω.TailLower s := (hS s (by omega) hsw).mpr (le_refl _)
  have hTs1 : ω.TailUpper (s - 1) := (hT (s - 1) (by omega) (by omega)).mpr (by omega)
  have hstep := h.dLo_step (a := s) (by omega) hsw
  have hstep' := h.dHi_step (a := s) (by omega) hsw
  unfold AttachCase.IsMixed at hmix
  rcases hmix with hc | hc
  · have e1 := h.sides_c hc (a := s) (by omega) hsw
    have e2 := h.sides_c hc (a := s - 1) (by omega) (by omega)
    unfold TailLower at hTs
    unfold TailUpper at hTs1
    by_cases hst : s < t
    · have hTs2 := (hT s (by omega) hsw).mpr hst
      unfold TailUpper at hTs2
      omega
    · omega
  · have e1 := h.sides_d hc (a := s) (by omega) hsw
    have e2 := h.sides_d hc (a := s - 1) (by omega) (by omega)
    unfold TailLower at hTs
    unfold TailUpper at hTs1
    by_cases hst : s < t
    · have hTs2 := (hT s (by omega) hsw).mpr hst
      unfold TailUpper at hTs2
      omega
    · omega

/-! ### Justification of the marked copies -/

theorem IsLegalNonempty.diagHi_W (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    diagHi ω.W (minContent ω.E + a) = min (ω.hi a) (ω.hi (a + ω.period) - ω.rowShift) := by
  obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row h0 h1
  have hmem : ω.cell a (min (ω.hi a) (ω.hi (a + ω.period) - ω.rowShift)) ∈ ω.W :=
    h.mem_W.mpr ⟨h0, h1, by omega, by omega, by omega, by omega⟩
  exact diagHi_eq_of (l := min (ω.hi a) (ω.hi (a + ω.period) - ω.rowShift)) hmem (fun i hi => by
    have := h.mem_W.mp (show ω.cell a i ∈ ω.W from hi)
    omega)

theorem IsLegalNonempty.diagLo_W (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    diagLo ω.W (minContent ω.E + a) = max (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift) := by
  obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row h0 h1
  have hmem : ω.cell a (max (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift)) ∈ ω.W :=
    h.mem_W.mpr ⟨h0, h1, by omega, by omega, by omega, by omega⟩
  exact diagLo_eq_of (l := max (ω.lo a) (ω.lo (a + ω.period) - ω.rowShift)) hmem (fun i hi => by
    have := h.mem_W.mp (show ω.cell a i ∈ ω.W from hi)
    omega)

theorem IsLegalNonempty.diagHi_upper (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    diagHi ω.upper (minContent ω.E + (a + ω.period)) =
      min (ω.hi a + ω.rowShift) (ω.hi (a + ω.period)) := by
  obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row h0 h1
  have hmem : ω.cell (a + ω.period) (min (ω.hi a + ω.rowShift) (ω.hi (a + ω.period))) ∈
      ω.upper := by
    rw [h.mem_upper]
    exact h.mem_W.mpr ⟨h0, h1, by omega, by omega, by omega, by omega⟩
  exact diagHi_eq_of (l := min (ω.hi a + ω.rowShift) (ω.hi (a + ω.period))) hmem (fun i hi => by
    have := h.mem_W.mp ((h.mem_upper).mp (show ω.cell (a + ω.period) i ∈ ω.upper from hi))
    omega)

theorem IsLegalNonempty.diagLo_upper (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    diagLo ω.upper (minContent ω.E + (a + ω.period)) =
      max (ω.lo a + ω.rowShift) (ω.lo (a + ω.period)) := by
  obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row h0 h1
  have hmem : ω.cell (a + ω.period) (max (ω.lo a + ω.rowShift) (ω.lo (a + ω.period))) ∈
      ω.upper := by
    rw [h.mem_upper]
    exact h.mem_W.mpr ⟨h0, h1, by omega, by omega, by omega, by omega⟩
  exact diagLo_eq_of (l := max (ω.lo a + ω.rowShift) (ω.lo (a + ω.period))) hmem (fun i hi => by
    have := h.mem_W.mp ((h.mem_upper).mp (show ω.cell (a + ω.period) i ∈ ω.upper from hi))
    omega)

/-- Both copies are southeast-justified: on every marked diagonal their last row is the last row
of `E`. -/
def SEJustified (ω : MarkedInner) : Prop :=
  ∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 →
    diagHi ω.W (minContent ω.E + a) = diagHi ω.E (minContent ω.E + a) ∧
    diagHi ω.upper (minContent ω.E + (a + ω.period)) =
      diagHi ω.E (minContent ω.E + (a + ω.period))

/-- Both copies are northwest-justified: on every marked diagonal their first row is the first
row of `E`. -/
def NWJustified (ω : MarkedInner) : Prop :=
  ∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 →
    diagLo ω.W (minContent ω.E + a) = diagLo ω.E (minContent ω.E + a) ∧
    diagLo ω.upper (minContent ω.E + (a + ω.period)) =
      diagLo ω.E (minContent ω.E + (a + ω.period))

theorem IsLegalNonempty.seJustified (h : ω.IsLegalNonempty) (hc : ω.case = .d) : ω.SEJustified := by
  intro a h0 h1
  have := h.sides_d hc h0 h1
  unfold dHi hi at this
  rw [h.diagHi_W h0 h1, h.diagHi_upper h0 h1]
  unfold hi
  exact ⟨by omega, by omega⟩

theorem IsLegalNonempty.nwJustified (h : ω.IsLegalNonempty) (hc : ω.case = .c) : ω.NWJustified := by
  intro a h0 h1
  have := h.sides_c hc h0 h1
  unfold dLo lo at this
  rw [h.diagLo_W h0 h1, h.diagLo_upper h0 h1]
  unfold lo
  exact ⟨by omega, by omega⟩
end MarkedInner

end GluingCore
