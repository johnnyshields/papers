import SkewGluing.OlsonHarris.Plan.MurnaghanNakayama.LeftDeriv

/-!
# The derivation form of the Murnaghan–Nakayama rule

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis Cor. 5.1.15 (`OlsonHarris2024HopfApplications`).

`pDeriv_cellSchur_left` and `pDeriv_cellSchur_right`: for every skew diagram `X` and `m > 0`,
`∂_m s_X` is the signed sum of `s_{X \ Y}` over the ribbons `Y` of size `m` removable on the left,
respectively on the right.  The left form for a diagram `λ / μ` of Young diagrams is
`pDeriv_cellSchur_left_young`; a general skew diagram is a translate of one
(`ribbonSumLeft_translate`), and the right form follows by rotation
(`ribbonSumRight_eq_ribbonSumLeft_rotate`).

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace MN

open MvPolynomial

/-! ### Translation -/

theorem numRows_translate (v : ℤ × ℤ) (D : Diagram) : numRows (translate v D) = numRows D := by
  have : rowSet (translate v D) = (rowSet D).image (· + v.1) := by
    ext a
    simp only [rowSet, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_translate] at hp
      exact ⟨(p - v).1, ⟨p - v, hp, rfl⟩, by simp⟩
    · rintro ⟨a', ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q + v, mem_translate.mpr (by simpa using hq), rfl⟩
  unfold numRows
  rw [this, Finset.card_image_of_injective _ (add_left_injective _)]

theorem card_translate (v : ℤ × ℤ) (D : Diagram) : (translate v D).card = D.card :=
  Finset.card_image_of_injective _ (add_left_injective _)

theorem isRibbon_translate (v : ℤ × ℤ) {Y : Diagram} : IsRibbon (translate v Y) ↔ IsRibbon Y := by
  unfold IsRibbon
  rw [isConnectedSkew_translate_iff, card_translate, span_translate]

theorem isDownsetIn_translate (v : ℤ × ℤ) {X Y : Diagram} (h : IsDownsetIn X Y) :
    IsDownsetIn (translate v X) (translate v Y) := by
  refine ⟨Finset.image_subset_image h.1, ?_⟩
  intro x hx y hy h1 h2
  rw [mem_translate] at hx hy ⊢
  exact h.2 _ hx _ hy (by simp only [Prod.fst_sub] at *; omega)
    (by simp only [Prod.snd_sub] at *; omega)

theorem mem_leftRibbons_translate {X Y : Diagram} {m : ℕ} (v : ℤ × ℤ) (h : Y ∈ leftRibbons X m) :
    translate v Y ∈ leftRibbons (translate v X) m := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_leftRibbons.mp h
  exact mem_leftRibbons.mpr ⟨Finset.image_subset_image h1, by rw [card_translate, h2],
    (isRibbon_translate v).mpr h3, isDownsetIn_translate v h4⟩

theorem leftRibbons_translate (v : ℤ × ℤ) (X : Diagram) (m : ℕ) :
    leftRibbons (translate v X) m = (leftRibbons X m).image (translate v) := by
  ext Z
  rw [Finset.mem_image]
  constructor
  · intro hZ
    refine ⟨translate (-v) Z, ?_, ?_⟩
    · have := mem_leftRibbons_translate (-v) hZ
      rwa [translate_neg_translate_cancel] at this
    · rw [translate_translate]
      simp [translate_zero]
  · rintro ⟨Y, hY, rfl⟩
    exact mem_leftRibbons_translate v hY

theorem ribbonSign_translate (v : ℤ × ℤ) (Y : Diagram) :
    ribbonSign (translate v Y) = ribbonSign Y := by
  unfold ribbonSign ribbonHeight
  rw [numRows_translate]

theorem ribbonSumLeft_translate (v : ℤ × ℤ) (X : Diagram) (m : ℕ) :
    ribbonSumLeft cellSchur (translate v X) m = ribbonSumLeft cellSchur X m := by
  unfold ribbonSumLeft
  rw [leftRibbons_translate, Finset.sum_image (fun A _ B _ h => translate_injective' v h)]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [ribbonSign_translate]
  congr 1
  have : translate v X \ translate v Y = translate v (X \ Y) := by
    unfold translate
    rw [Finset.image_sdiff _ _ (add_left_injective _)]
  rw [this, cellSchur_translate]

/-! ### Rotation -/

theorem numRows_rotate (D : Diagram) : numRows (rotate D) = numRows D := by
  have : rowSet (rotate D) = (rowSet D).image (fun a => -a) := by
    ext a
    simp only [rowSet, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_rotate] at hp
      exact ⟨(-p).1, ⟨-p, hp, rfl⟩, by simp⟩
    · rintro ⟨a', ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨-q, mem_rotate.mpr (by simpa using hq), rfl⟩
  unfold numRows
  rw [this, Finset.card_image_of_injective _ neg_injective]

theorem card_rotate (D : Diagram) : (rotate D).card = D.card :=
  Finset.card_image_of_injective _ neg_injective

theorem isRibbon_rotate {Y : Diagram} : IsRibbon (rotate Y) ↔ IsRibbon Y := by
  unfold IsRibbon
  rw [isConnectedSkew_rotate_iff, card_rotate, span_rotate]

theorem isDownsetIn_rotate_of_isUpsetIn {X Y : Diagram} (h : IsUpsetIn X Y) :
    IsDownsetIn (rotate X) (rotate Y) := by
  refine ⟨Finset.image_subset_image h.1, ?_⟩
  intro x hx y hy h1 h2
  rw [mem_rotate] at hx hy ⊢
  have := h.2 _ hx _ hy
  simp only [Prod.fst_neg, Prod.snd_neg] at *
  exact this (by omega) (by omega)

theorem isUpsetIn_of_isDownsetIn_rotate {X Y : Diagram} (h : IsDownsetIn (rotate X) (rotate Y)) :
    IsUpsetIn X Y := by
  refine ⟨?_, ?_⟩
  · intro y hy
    have := h.1 (mem_rotate.mpr (by simpa using hy) : -y ∈ rotate Y)
    rw [mem_rotate] at this
    simpa using this
  · intro x hx y hy h1 h2
    have hx' : -x ∈ rotate X := mem_rotate.mpr (by simpa using hx)
    have hy' : -y ∈ rotate Y := mem_rotate.mpr (by simpa using hy)
    have := h.2 _ hx' _ hy' (by simp only [Prod.fst_neg]; omega)
      (by simp only [Prod.snd_neg]; omega)
    rw [mem_rotate] at this
    simpa using this

theorem rightRibbons_eq_image_rotate (X : Diagram) (m : ℕ) :
    leftRibbons (rotate X) m = (rightRibbons X m).image rotate := by
  ext Z
  rw [Finset.mem_image]
  constructor
  · intro hZ
    obtain ⟨h1, h2, h3, h4⟩ := mem_leftRibbons.mp hZ
    refine ⟨rotate Z, mem_rightRibbons.mpr ⟨?_, ?_, ?_, ?_⟩, rotate_rotate⟩
    · intro y hy
      have := h1 (mem_rotate.mp hy)
      rw [mem_rotate] at this
      simpa using this
    · rw [card_rotate, h2]
    · exact isRibbon_rotate.mpr h3
    · apply isUpsetIn_of_isDownsetIn_rotate
      rwa [rotate_rotate]
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_rightRibbons.mp hY
    exact mem_leftRibbons.mpr ⟨Finset.image_subset_image h1, by rw [card_rotate, h2],
      isRibbon_rotate.mpr h3, isDownsetIn_rotate_of_isUpsetIn h4⟩

theorem ribbonSumRight_eq_ribbonSumLeft_rotate (X : Diagram) (m : ℕ) :
    ribbonSumRight cellSchur X m = ribbonSumLeft cellSchur (rotate X) m := by
  unfold ribbonSumLeft ribbonSumRight
  rw [rightRibbons_eq_image_rotate, Finset.sum_image (fun A _ B _ h => rotate_injective h)]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have e1 : ribbonSign (rotate Y) = ribbonSign Y := by
    unfold ribbonSign ribbonHeight
    rw [numRows_rotate]
  rw [e1]
  congr 1
  have : rotate X \ rotate Y = rotate (X \ Y) := by
    unfold rotate
    rw [Finset.image_sdiff _ _ neg_injective]
  rw [this, cellSchur_rotate]

/-! ### The theorems -/

/-- Every skew diagram is a translate of a skew diagram of two Young diagrams. -/
theorem exists_translate_skewDiagram {X : Diagram} (hX : IsSkew X) :
    ∃ (v : ℤ × ℤ) (lam mu : YoungDiagram), mu ≤ lam ∧ translate v X = skewDiagram lam mu := by
  set N : ℤ := ∑ x ∈ X, (|x.1| + |x.2|) with hN
  have hb : ∀ x ∈ X, |x.1| ≤ N ∧ |x.2| ≤ N := by
    intro x hx
    have : |x.1| + |x.2| ≤ N :=
      Finset.single_le_sum (f := fun x : ℤ × ℤ => |x.1| + |x.2|) (fun _ _ => by positivity) hx
    constructor <;> linarith [abs_nonneg x.1, abs_nonneg x.2]
  obtain ⟨lam, mu, hmu, h⟩ := exists_young_pair_of_isSkew (isSkew_translate (N, N) hX) (by
    intro x hx
    rw [mem_translate] at hx
    have := hb _ hx
    simp only [Prod.fst_sub, Prod.snd_sub] at hx this ⊢
    constructor <;> linarith [abs_le.mp this.1, abs_le.mp this.2])
  exact ⟨(N, N), lam, mu, hmu, h.symm⟩

/-- **Murnaghan–Nakayama, derivation form, left.**  For a skew diagram `X` and `m > 0`,
`∂_m s_X = Σ_{Y ∈ leftRibbons X m} (-1)^{ht Y} s_{X \ Y}`. -/
theorem pDeriv_cellSchur_left_of_isSkew {X : Diagram} (hX : IsSkew X) {m : ℕ} (hm : 0 < m) :
    pDeriv m (cellSchur X) = ribbonSumLeft cellSchur X m := by
  obtain ⟨v, lam, mu, hmu, h⟩ := exists_translate_skewDiagram hX
  rw [← ribbonSumLeft_translate v X m, ← cellSchur_translate v X, h]
  exact pDeriv_cellSchur_left_young hmu hm

/-- **Murnaghan–Nakayama, derivation form, right.** -/
theorem pDeriv_cellSchur_right_of_isSkew {X : Diagram} (hX : IsSkew X) {m : ℕ} (hm : 0 < m) :
    pDeriv m (cellSchur X) = ribbonSumRight cellSchur X m := by
  rw [ribbonSumRight_eq_ribbonSumLeft_rotate,
    ← pDeriv_cellSchur_left_of_isSkew (isSkew_rotate hX) hm, cellSchur_rotate]

end MN

end Plan

end SkewGluing
