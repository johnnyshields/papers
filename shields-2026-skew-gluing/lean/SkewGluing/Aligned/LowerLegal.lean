import SkewGluing.Aligned.LowerGlue

/-!
# Legality of the lower mark `μ = (V, V ∩ (V - z), z)`

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, ordinary case, `b > 0`: the legality checks for `Z`).

From the hypotheses `GlueData V z` this file proves the case-free clauses of the legality of
`muOf V z cs`: the lower copy is connected skew of span `b`, condition II, the complements
(condition III, the upper complement by rotation), the thinness of the middle on the marked
diagonals, and condition IV.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {V : Diagram} {z : ℤ × ℤ}

theorem upper_muOf (cs : AttachCase) : (muOf V z cs).upper = translate z (lowerCopy V z) := rfl

theorem rotate_upper_lowerCopy (V : Diagram) (z : ℤ × ℤ) :
    SkewGluing.rotate (translate z (lowerCopy V z)) = lowerCopy (SkewGluing.rotate V) z := by
  ext x
  rw [mem_rotate, mem_translate, mem_lowerCopy, mem_lowerCopy, mem_rotate, mem_rotate]
  have e : -x - z = -(x + z) := by abel
  have e2 : -(x + z) + z = -x := by abel
  rw [e, e2]
  tauto

theorem muOf_rotate (V : Diagram) (z : ℤ × ℤ) (cs : AttachCase) :
    (muOf V z cs).rotate = muOf (SkewGluing.rotate V) z cs.rotate := by
  change MarkedInner.mk (SkewGluing.rotate V) (SkewGluing.rotate (translate z (lowerCopy V z))) z
      cs.rotate = MarkedInner.mk (SkewGluing.rotate V) (lowerCopy (SkewGluing.rotate V) z) z
      cs.rotate
  rw [rotate_upper_lowerCopy]

namespace GlueData

/-- The contents of the lower copy are the contents `[m, M - α]`. -/
theorem contents_lowerCopy (G : GlueData V z) :
    contents (lowerCopy V z) = Finset.Icc (minContent V) (maxContent V - content z) := by
  have hV := G.conn
  have hα := G.alpha_pos
  ext J
  rw [Finset.mem_Icc, mem_contents_iff]
  constructor
  · rintro ⟨i, hi⟩
    have := (lowerCopy_row hV).mp (show (i, i + J) ∈ lowerCopy V z from hi)
    omega
  · rintro ⟨h1, h2⟩
    have hne := G.nonempty J h1 h2
    refine ⟨max (diagLo V J) (diagLo V (J + content z) - z.1), ?_⟩
    rw [lowerCopy_row hV]
    have hl := diagLo_le_diagHi (D := V) (k := J) (by
      have := isConnectedSkew_iff_diagonal.mp hV
      rw [this.mem_contents_iff]; omega)
    omega

theorem span_lowerCopy (G : GlueData V z) :
    (span (lowerCopy V z) : ℤ) = (span V : ℤ) - content z := by
  have h1 := G.contents_lowerCopy
  have h2 := G.span_eq
  have hle := G.le_max
  have hc : span (lowerCopy V z) =
      (maxContent V - content z + 1 - minContent V).toNat := by
    unfold span; rw [h1, Int.card_Icc]
  omega

theorem minContent_lowerCopy (G : GlueData V z) :
    minContent (lowerCopy V z) = minContent V := by
  have hle := G.le_max
  apply minContent_eq_of (k := minContent V)
  · rw [G.contents_lowerCopy, Finset.mem_Icc]; omega
  · intro k hk
    rw [G.contents_lowerCopy, Finset.mem_Icc] at hk
    omega

theorem maxContent_lowerCopy (G : GlueData V z) :
    maxContent (lowerCopy V z) = maxContent V - content z := by
  have hle := G.le_max
  apply maxContent_eq_of (k := maxContent V - content z)
  · rw [G.contents_lowerCopy, Finset.mem_Icc]; omega
  · intro k hk
    rw [G.contents_lowerCopy, Finset.mem_Icc] at hk
    omega

theorem width_muOf (G : GlueData V z) (cs : AttachCase) :
    ((muOf V z cs).width : ℤ) = (span V : ℤ) - content z := G.span_lowerCopy

theorem period_muOf (cs : AttachCase) : (muOf V z cs).period = content z := rfl

/-- The upper complement `V \ (Z + z)` is connected skew (by rotation, from `GlueData` of the
rotated diagram). -/
theorem isConnectedSkew_sdiff_upper (G' : GlueData (SkewGluing.rotate V) z) :
    IsConnectedSkew (V \ translate z (lowerCopy V z)) := by
  have h := G'.isConnectedSkew_sdiff_lower
  rw [← rotate_upper_lowerCopy, ← rotate_sdiff] at h
  have := isConnectedSkew_rotate h
  rwa [SkewGluing.rotate_rotate] at this

theorem mem_upper_row (hV : IsConnectedSkew V) {i J : ℤ} :
    (i, i + J) ∈ translate z (lowerCopy V z) ↔
      (minContent V ≤ J - content z ∧ J - content z ≤ maxContent V ∧
        diagLo V (J - content z) ≤ i - z.1 ∧ i - z.1 ≤ diagHi V (J - content z)) ∧
      (minContent V ≤ J ∧ J ≤ maxContent V ∧ diagLo V J ≤ i ∧ i ≤ diagHi V J) := by
  rw [mem_translate]
  have e : (i, i + J) - z = (i - z.1, (i - z.1) + (J - content z)) := by
    ext
    · simp
    · simp only [Prod.snd_sub, content]; ring
  rw [e, lowerCopy_row hV]
  have e1 : J - content z + content z = J := by ring
  have e2 : i - z.1 + z.1 = i := by ring
  rw [e1, e2]

/-- Two middle cells of `μ` on one marked diagonal coincide. -/
theorem middle_row_unique (G : GlueData V z) {i i' J : ℤ}
    (hx : (i, i + J) ∈ V ∧ (i, i + J) ∉ lowerCopy V z ∧
      (i, i + J) ∉ translate z (lowerCopy V z))
    (hy : (i', i' + J) ∈ V ∧ (i', i' + J) ∉ lowerCopy V z ∧
      (i', i' + J) ∉ translate z (lowerCopy V z))
    (hmark : J ≤ maxContent V - content z ∨ minContent V + content z ≤ J) : i = i' := by
  have hV := G.conn
  have hα := G.alpha_pos
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  rw [mem_D hV] at hx1 hy1
  rw [lowerCopy_row hV] at hx2 hy2
  rw [mem_upper_row hV] at hx3 hy3
  rcases hmark with hm | hm
  · have t := G.thin_lo J (by omega) hm
    simp only [gapLo, gapHi] at t
    omega
  · have t := G.thin_up (J - content z) (by omega) (by omega)
    simp only [gapLo, gapHi, sub_add_cancel] at t
    omega

theorem middleSubsingleton (G : GlueData V z) (cs : AttachCase) :
    (muOf V z cs).MiddleSubsingleton := by
  intro x hx y hy hxy hmark
  rw [mem_middle] at hx hy
  have hw := G.width_muOf cs
  have hmin : minContent (muOf V z cs).E = minContent V := rfl
  have hper := period_muOf (V := V) (z := z) cs
  have hspan := G.span_eq
  have hmark' : content x ≤ maxContent V - content z ∨ minContent V + content z ≤ content x := by
    rcases hmark with h | h
    · left; rw [hmin] at h; omega
    · right; rw [hmin, hper] at h; omega
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  have ex : (x1, x2) = (x1, x1 + content (x1, x2)) := by simp [content]
  have ey : (y1, y2) = (y1, y1 + content (y1, y2)) := by simp [content]
  have hxy' : content (y1, y2) = content (x1, x2) := hxy.symm
  rw [ex] at hx
  rw [ey, hxy'] at hy
  have := G.middle_row_unique (J := content (x1, x2)) (i := x1) (i' := y1) hx hy hmark'
  have h1 : x1 = y1 := this
  have h2 : x2 - x1 = y2 - y1 := hxy
  ext
  · exact h1
  · change x2 = y2
    omega

/-- **Condition IV in finite-window form**, from the thinness of the middle and the two singleton
junction diagonals. -/
theorem hatWindowClear (G : GlueData V z) (cs : AttachCase) : (muOf V z cs).HatWindowClear := by
  have hMS := G.middleSubsingleton cs
  have hα := G.alpha_pos
  have hspan := G.span_eq
  have hle := G.le_max
  have hV := G.conn
  have hw := G.width_muOf cs
  intro k hk x hx y hy hadj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rw [Finset.mem_filter] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hx0 : x - k • z ∈ (muOf V z cs).middle := mem_translate.mp hx1
  have hx0' : x - k • z + eCell ∈ (muOf V z cs).middle := by
    have : x + eCell - k • z ∈ (muOf V z cs).middle := mem_translate.mp hx2
    have e : x + eCell - k • z = x - k • z + eCell := by abel
    rwa [e] at this
  set x0 := x - k • z with hx0def
  have hc0 : content (x0 + eCell) = content x0 := content_eCell_add x0
  have hxV : x0 ∈ V := (mem_middle.mp hx0).1
  have hxV' : x0 + eCell ∈ V := (mem_middle.mp hx0').1
  have hJ0 := content_mem_contents hxV
  have hVsh := isConnectedSkew_iff_diagonal.mp hV
  rw [hVsh.mem_contents_iff] at hJ0
  -- the diagonal of `x0` is not marked
  have hne : x0 ≠ x0 + eCell := by
    intro h
    have := congrArg Prod.fst h
    simp [eCell] at this
  have hunm : ¬ (content x0 ≤ minContent (muOf V z cs).E + (muOf V z cs).width - 1 ∨
      minContent (muOf V z cs).E + (muOf V z cs).period ≤ content x0) := by
    intro hm
    exact hne (hMS x0 hx0 (x0 + eCell) hx0' hc0.symm hm)
  have hmin : minContent (muOf V z cs).E = minContent V := rfl
  have hper := period_muOf (V := V) (z := z) cs
  rw [hmin, hper] at hunm
  have hwz : ((muOf V z cs).width : ℤ) = (span V : ℤ) - content z := hw
  -- the content of `y`
  have hyc : minContent V ≤ content y ∧ content y ≤ maxContent V - content z := by
    have hW : ∀ u : ℤ × ℤ, u ∈ lowerCopy V z → content u = content y →
        minContent V ≤ content y ∧ content y ≤ maxContent V - content z := by
      intro u hu hcu
      have := content_mem_contents hu
      rw [G.contents_lowerCopy, Finset.mem_Icc] at this
      omega
    simp only [hatMarkWindow, Finset.mem_union, Finset.mem_filter] at hy
    rcases hy with ⟨-, hy2⟩ | ⟨hy1, -⟩
    · exact hW (y + eCell) hy2 (content_eCell_add y)
    · exact hW y hy1 rfl
  have hca := content_adj hadj
  have hsingle : ∀ J : ℤ, diagLo V J = diagHi V J → content x0 = J → False := by
    intro J hJ hcJ
    have h1 := diagLo_le (D := V) (k := J) (i := x0.1) (j := x0.2) hxV (by
      simpa [content] using hcJ)
    have h2 := le_diagHi (D := V) (k := J) (i := (x0 + eCell).1) (j := (x0 + eCell).2) hxV' (by
      have := hcJ
      simp only [content, Prod.snd_add, Prod.fst_add, eCell] at this ⊢
      omega)
    simp only [Prod.fst_add, eCell] at h2
    omega
  have hcx : content x = content x0 + k * content z := by
    have : x = x0 + k • z := by rw [hx0def]; abel
    rw [this, content_add, content_smul]
  rcases hk with rfl | rfl
  · -- `k = -1`
    have hcx' : content x = content x0 - content z := by rw [hcx]; ring
    have hj : content x0 = minContent V + content z - 1 := by omega
    exact hsingle _ G.sing_a hj
  · have hcx' : content x = content x0 := by rw [hcx]; ring
    have hj : content x0 = maxContent V - content z + 1 := by omega
    exact hsingle _ G.sing_b hj

theorem sw_mem_lowerCopy (G : GlueData V z) : sw V ∈ lowerCopy V z := by
  have hV := G.conn
  have hends := D_ends hV
  have hne := G.nonempty (minContent V) le_rfl G.le_max
  have hα := G.alpha_pos
  have hlt := G.alpha_lt
  have hsp := G.span_eq
  have hl := diagLo_le_diagHi (D := V) (minContent_mem hV.2.1)
  have e : sw V = ((sw V).1, (sw V).1 + minContent V) := by
    ext
    · rfl
    · simp [sw]
  rw [e, lowerCopy_row hV]
  have hs : (sw V).1 = diagLo V (minContent V) := rfl
  rw [hs]
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  omega

theorem ne_mem_upper (G : GlueData V z) : ne V ∈ translate z (lowerCopy V z) := by
  have hV := G.conn
  have hends := D_ends hV
  have hne := G.nonempty (maxContent V - content z) G.le_max le_rfl
  have hα := G.alpha_pos
  have hle := G.le_max
  have hl := diagLo_le_diagHi (D := V) (maxContent_mem hV.2.1)
  simp only [sub_add_cancel] at hne
  have e : ne V = ((ne V).1, (ne V).1 + maxContent V) := by
    ext
    · rfl
    · simp [ne]
  rw [e, mem_upper_row hV]
  have hs : (ne V).1 = diagLo V (maxContent V) := rfl
  rw [hs]
  have hmM : minContent V ≤ maxContent V := minContent_le (maxContent_mem hV.2.1)
  omega

theorem isNarrow_muOf (G : GlueData V z) (cs : AttachCase) : (muOf V z cs).IsNarrow := by
  have hw := G.width_muOf cs
  have hlt := G.alpha_lt
  have hsep := G.sep
  unfold IsNarrow
  rw [period_muOf]
  omega

/-- The case-free part of the legality of `μ`, with the attachments and maximality as the two
remaining hypotheses. -/
theorem isWellFormed_muOf (G : GlueData V z) (cs : AttachCase)
    (hatt : (muOf V z cs).AttachmentMatches) : (muOf V z cs).IsWellFormed := by
  have hZ := G.isConnectedSkew_lowerCopy
  refine ⟨G.conn, Or.inr ⟨hZ.2.1, hZ, ?_, ?_, ?_, ?_, hatt⟩⟩
  · exact Finset.filter_subset _ _
  · intro y hy
    have h0 : y - z ∈ lowerCopy V z := mem_translate.mp hy
    have h1 := (mem_lowerCopy.mp h0).2
    have e : y - z + z = y := by abel
    rw [e] at h1
    exact h1
  · exact G.sw_mem_lowerCopy
  · exact G.ne_mem_upper

theorem isLegal_muOf (G : GlueData V z) (G' : GlueData (SkewGluing.rotate V) z) (cs : AttachCase)
    (hatt : (muOf V z cs).AttachmentMatches) (hI : (muOf V z cs).IsMaximal) :
    (muOf V z cs).IsLegal := by
  have hwf := G.isWellFormed_muOf cs hatt
  have hII := G.isNarrow_muOf cs
  exact ⟨hwf, hI, hII, ⟨G.isConnectedSkew_sdiff_lower, isConnectedSkew_sdiff_upper G'⟩,
    (noHatAdjacency_iff_window hwf hII).mpr (G.hatWindowClear cs)⟩

end GlueData

end MarkedInner

end SkewGluing
