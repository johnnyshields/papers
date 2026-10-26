import SkewGluing.OlsonHarris.Plan.MurnaghanNakayama.RibbonCells

/-!
# Adding a ribbon to a Young diagram, row by row

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1.3 (`OlsonHarris2024HopfApplications`), the
description of a ribbon `ν / μ` of `m` cells by its rows.

`RowMove μ ν j i₁ m` says that `ν` is obtained from `μ` by adding a ribbon of `m` cells whose
southwestern cell is in row `j` and whose northeastern cell is in row `i₁`:
the rows outside `[i₁, j]` agree, `ν_i = μ_{i-1} + 1` for `i₁ < i ≤ j`, and
`ν_{i₁} = μ_j + m - (j - i₁)`.  In terms of the β-numbers `μ_i - i` this raises the entry at
`j` by `m` and moves it to the position `i₁` (the sorted position).

* `RowMove.isRibbon`: a row move (with `m > 0`) adds a ribbon with `m` cells and `j - i₁ + 1`
  rows.
* `RowMove.of_isRibbon`: every ribbon `ν / μ` arises this way.
* `RowMove.unique`: the rows `j`, `i₁` are determined by `μ`, `ν`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace MN

/-- `ν` is obtained from `μ` by adding a ribbon of `m` cells, with southwest row `j` and
northeast row `i₁`. -/
structure RowMove (mu nu : YoungDiagram) (j i1 m : ℕ) : Prop where
  i1_le : i1 ≤ j
  outside : ∀ i, (i < i1 ∨ j < i) → nu.rowLen i = mu.rowLen i
  top : (nu.rowLen i1 : ℤ) = mu.rowLen j + m - (j - i1 : ℕ)
  inner : ∀ i, i1 < i → i ≤ j → nu.rowLen i = mu.rowLen (i - 1) + 1

namespace RowMove

variable {mu nu : YoungDiagram} {j i1 m : ℕ}

theorem row_lt (h : RowMove mu nu j i1 m) (hm : 0 < m) {i : ℕ} (h1 : i1 ≤ i) (h2 : i ≤ j) :
    mu.rowLen i < nu.rowLen i := by
  rcases Nat.eq_or_lt_of_le h1 with heq | hlt
  · subst heq
    rcases Nat.eq_or_lt_of_le h2 with heq2 | hlt2
    · subst heq2
      have := h.top
      simp only [Nat.sub_self, Nat.cast_zero] at this
      omega
    · have h3 := h.inner (i1 + 1) (by omega) (by omega)
      have h4 := nu.rowLen_anti i1 (i1 + 1) (by omega)
      have h5 := mu.rowLen_anti (i1) (i1 + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h3
      omega
  · have h3 := h.inner i hlt h2
    have h4 := mu.rowLen_anti (i - 1) i (by omega)
    omega

theorem row_le (h : RowMove mu nu j i1 m) (hm : 0 < m) (i : ℕ) : mu.rowLen i ≤ nu.rowLen i := by
  by_cases hi : i1 ≤ i ∧ i ≤ j
  · exact (h.row_lt hm hi.1 hi.2).le
  · rw [h.outside i (by omega)]

theorem le (h : RowMove mu nu j i1 m) (hm : 0 < m) : mu ≤ nu := by
  intro c hc
  obtain ⟨i, x⟩ := c
  rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
  have := h.row_le hm i
  omega

/-- The key inequality: a later row of `ν` is no longer than an earlier row of `μ` plus the
distance between them. -/
theorem nu_le_mu_add (h : RowMove mu nu j i1 m) {i i' : ℕ} (hii : i < i') :
    nu.rowLen i' ≤ mu.rowLen i + (i' - i) := by
  by_cases h1 : i1 < i' ∧ i' ≤ j
  · have := h.inner i' h1.1 h1.2
    have := mu.rowLen_anti i (i' - 1) (by omega)
    omega
  · by_cases h2 : i' = i1
    · have := h.outside i (by omega)
      have := nu.rowLen_anti i i' hii.le
      omega
    · rw [h.outside i' (by omega)]
      have := mu.rowLen_anti i i' hii.le
      omega

theorem row_mem (h : RowMove mu nu j i1 m) {i x : ℕ} (hx1 : mu.rowLen i ≤ x)
    (hx2 : x < nu.rowLen i) : i1 ≤ i ∧ i ≤ j := by
  by_contra hcon
  have := h.outside i (by omega)
  omega

theorem content_bounds (h : RowMove mu nu j i1 m) (hm : 0 < m) {i x : ℕ}
    (hx1 : mu.rowLen i ≤ x) (hx2 : x < nu.rowLen i) :
    (mu.rowLen j : ℤ) - j ≤ (x : ℤ) - i ∧ (x : ℤ) - i < (mu.rowLen j : ℤ) - j + m := by
  obtain ⟨h1, h2⟩ := h.row_mem hx1 hx2
  have hj := mu.rowLen_anti i j h2
  have htop := h.top
  have hlt := h.row_lt hm (le_refl i1) h.i1_le
  have hjn : ((j - i1 : ℕ) : ℤ) = (j : ℤ) - i1 := by omega
  rw [hjn] at htop
  refine ⟨by omega, ?_⟩
  rcases Nat.eq_or_lt_of_le h1 with heq | hlt1
  · subst heq; omega
  · have e1 := h.inner i hlt1 h2
    have e2 := mu.rowLen_anti i1 (i - 1) (by omega)
    omega

theorem exists_cell (h : RowMove mu nu j i1 m) {k : ℤ}
    (hk1 : (mu.rowLen j : ℤ) - j ≤ k) (hk2 : k < (mu.rowLen j : ℤ) - j + m) :
    ∃ i x : ℕ, mu.rowLen i ≤ x ∧ x < nu.rowLen i ∧ (x : ℤ) - i = k := by
  classical
  have hP : ∃ i, i1 ≤ i ∧ i ≤ j ∧ (mu.rowLen i : ℤ) - i ≤ k := ⟨j, h.i1_le, le_refl j, hk1⟩
  obtain ⟨i, hi1, hi2, hi3, hmin⟩ : ∃ i, i1 ≤ i ∧ i ≤ j ∧ (mu.rowLen i : ℤ) - i ≤ k ∧
      ∀ i' < i, ¬ (i1 ≤ i' ∧ i' ≤ j ∧ (mu.rowLen i' : ℤ) - i' ≤ k) :=
    ⟨Nat.find hP, (Nat.find_spec hP).1, (Nat.find_spec hP).2.1, (Nat.find_spec hP).2.2,
      fun i' hi' => Nat.find_min hP hi'⟩
  have htop := h.top
  have hjn : ((j - i1 : ℕ) : ℤ) = (j : ℤ) - i1 := by omega
  rw [hjn] at htop
  refine ⟨i, (k + i).toNat, by omega, ?_, by omega⟩
  rcases Nat.eq_or_lt_of_le hi1 with heq | hlt1
  · rw [← heq]; omega
  · have e1 := h.inner i hlt1 hi2
    have := hmin (i - 1) (by omega)
    omega

theorem contents_eq (h : RowMove mu nu j i1 m) (hm : 0 < m) :
    contents (skewDiagram nu mu) =
      Finset.Ico ((mu.rowLen j : ℤ) - j) ((mu.rowLen j : ℤ) - j + m) := by
  ext k
  rw [mem_contents_iff, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨i', x', h1, h2, h3, h4⟩ := mem_skewDiagram_iff.mp hi
    have := h.content_bounds hm h3 h4
    subst h1
    omega
  · rintro ⟨hk1, hk2⟩
    obtain ⟨i, x, hx1, hx2, hx3⟩ := h.exists_cell hk1 hk2
    refine ⟨i, mem_skewDiagram_iff.mpr ⟨i, x, rfl, ?_, hx1, hx2⟩⟩
    omega

theorem injOn_content (h : RowMove mu nu j i1 m) :
    Set.InjOn content (skewDiagram nu mu : Set (ℤ × ℤ)) := by
  rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq hc
  obtain ⟨i, x, rfl, rfl, h1, h2⟩ := mem_skewDiagram_iff.mp (Finset.mem_coe.mp hp)
  obtain ⟨i', x', rfl, rfl, h1', h2'⟩ := mem_skewDiagram_iff.mp (Finset.mem_coe.mp hq)
  simp only [content] at hc
  have hii : i = i' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := h.nu_le_mu_add hlt
      omega
    · have := h.nu_le_mu_add hlt
      omega
  subst hii
  have : x = x' := by omega
  subst this
  rfl

theorem rowSet_eq (h : RowMove mu nu j i1 m) (hm : 0 < m) :
    rowSet (skewDiagram nu mu) = Finset.Icc (i1 : ℤ) j := by
  ext a
  rw [Finset.mem_Icc]
  simp only [rowSet, Finset.mem_image, Prod.exists]
  constructor
  · rintro ⟨a', b, hab, rfl⟩
    obtain ⟨i, x, rfl, rfl, h1, h2⟩ := mem_skewDiagram_iff.mp hab
    have := h.row_mem h1 h2
    omega
  · rintro ⟨h1, h2⟩
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, a = i := ⟨a.toNat, by omega⟩
    have := h.row_lt hm (i := i) (by omega) (by omega)
    exact ⟨i, mu.rowLen i, mem_skewDiagram_iff.mpr ⟨i, mu.rowLen i, rfl, rfl, le_refl _, this⟩, rfl⟩

/-- **A row move adds a ribbon.**  For `m > 0`, `ν / μ` is a ribbon with `m` cells and
`j - i₁ + 1` rows. -/
theorem isRibbon (h : RowMove mu nu j i1 m) (hm : 0 < m) :
    IsRibbon (skewDiagram nu mu) := by
  have hne : (skewDiagram nu mu).Nonempty := by
    have hmem : ((j : ℤ), (mu.rowLen j : ℤ)) ∈ skewDiagram nu mu :=
      (mem_skewDiagram_nat_iff _ _).mpr ⟨le_refl _, h.row_lt hm h.i1_le (le_refl j)⟩
    exact ⟨_, hmem⟩
  refine isRibbon_of_injOn_interval (isSkew_skewDiagram nu mu) hne (h.injOn_content) ?_
  intro x hx y hy k hk
  have hx' : content x ∈ contents (skewDiagram nu mu) := content_mem_contents hx
  have hy' : content y ∈ contents (skewDiagram nu mu) := content_mem_contents hy
  rw [h.contents_eq hm, Finset.mem_Ico] at hx' hy' ⊢
  rw [Finset.mem_Icc] at hk
  omega

theorem card_eq (h : RowMove mu nu j i1 m) (hm : 0 < m) : (skewDiagram nu mu).card = m := by
  have := (Finset.card_image_of_injOn (h.injOn_content)).symm
  change (skewDiagram nu mu).card = (contents (skewDiagram nu mu)).card at this
  rw [this, h.contents_eq hm, Int.card_Ico]
  omega

theorem numRows_eq (h : RowMove mu nu j i1 m) (hm : 0 < m) :
    numRows (skewDiagram nu mu) = j - i1 + 1 := by
  unfold numRows
  rw [h.rowSet_eq hm, Int.card_Icc]
  have := h.i1_le
  omega

end RowMove

/-- **The row description of a ribbon, from its cells.**  If the cells of `ν / μ` have pairwise
distinct contents filling an interval `[c, c + m)`, then `ν` is obtained from `μ` by a row move. -/
theorem exists_rowMove_of_cells {mu nu : YoungDiagram} (hle : mu ≤ nu) {m : ℕ} (c : ℤ)
    (hm : 0 < m)
    (P1 : ∀ i i' x x' : ℕ, mu.rowLen i ≤ x → x < nu.rowLen i → mu.rowLen i' ≤ x' →
      x' < nu.rowLen i' → (x : ℤ) - i = x' - i' → i = i')
    (P2 : ∀ k : ℤ, (∃ i x : ℕ, mu.rowLen i ≤ x ∧ x < nu.rowLen i ∧ (x : ℤ) - i = k) ↔
      c ≤ k ∧ k < c + m) :
    ∃ j i1, RowMove mu nu j i1 m := by
  have hrow : ∀ i, mu.rowLen i ≤ nu.rowLen i := fun i => by
    by_contra hcon
    have : (i, nu.rowLen i) ∈ mu := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have h2 := hle this
    rw [YoungDiagram.mem_iff_lt_rowLen] at h2
    omega
  have hex : ∀ k : ℤ, ∃ i : ℕ, (c ≤ k ∧ k < c + m) →
      ∃ x : ℕ, mu.rowLen i ≤ x ∧ x < nu.rowLen i ∧ (x : ℤ) - i = k := by
    intro k
    by_cases hk : c ≤ k ∧ k < c + m
    · obtain ⟨i, x, h⟩ := (P2 k).mpr hk
      exact ⟨i, fun _ => ⟨x, h⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose r hr using hex
  -- the cell of content `k`
  have hr' : ∀ k, c ≤ k → k < c + m →
      (mu.rowLen (r k) : ℤ) ≤ k + r k ∧ k + r k < nu.rowLen (r k) := by
    intro k h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hr k ⟨h1, h2⟩
    constructor <;> omega
  have hrow_eq : ∀ i x : ℕ, mu.rowLen i ≤ x → x < nu.rowLen i →
      c ≤ (x : ℤ) - i ∧ (x : ℤ) - i < c + m ∧ r ((x : ℤ) - i) = i := by
    intro i x hx1 hx2
    have hk := (P2 ((x : ℤ) - i)).mp ⟨i, x, hx1, hx2, rfl⟩
    refine ⟨hk.1, hk.2, ?_⟩
    obtain ⟨x', h1, h2, h3⟩ := hr ((x : ℤ) - i) hk
    exact (P1 _ _ _ _ h1 h2 hx1 hx2 h3)
  -- consecutive rows differ by at most one
  have hbit : ∀ k, c < k → k < c + m → r (k - 1) = r k ∨ r (k - 1) = r k + 1 := by
    intro k h1 h2
    obtain ⟨a1, a2⟩ := hr' k (by omega) h2
    obtain ⟨b1, b2⟩ := hr' (k - 1) (by omega) (by omega)
    have an1 := nu.rowLen_anti
    by_contra hcon
    push Not at hcon
    rcases lt_or_gt_of_ne hcon.1 with hlt | hgt
    · -- `r (k-1) < r k`
      have hm1 := nu.rowLen_anti (r (k - 1)) (r k) hlt.le
      have := P1 (r (k - 1)) (r k) (k + r (k - 1)).toNat (k + r k).toNat (by omega) (by omega)
        (by omega) (by omega) (by omega)
      omega
    · -- `r k + 2 ≤ r (k-1)`
      have hr2 : r k + 2 ≤ r (k - 1) := by omega
      have hm1 := nu.rowLen_anti (r (k - 1) - 1) (r (k - 1)) (by omega)
      have hm2 := mu.rowLen_anti (r k) (r (k - 1) - 1) (by omega)
      have := P1 (r (k - 1)) (r (k - 1) - 1) (k - 1 + r (k - 1)).toNat
        (k - 1 + r (k - 1) - 1).toNat (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
  -- the rows are monotone in the content
  have hanti : ∀ k k' : ℤ, c ≤ k → k ≤ k' → k' < c + m → r k' ≤ r k := by
    intro k k' hk hkk' hk'
    induction k', hkk' using Int.leInduction with
    | base => exact le_rfl
    | succ k' hk'' ih =>
      have := hbit (k' + 1) (by omega) hk'
      simp only [add_sub_cancel_right] at this
      have := ih (by omega)
      omega
  -- every row between the extreme ones is attained
  have hivt : ∀ k' : ℤ, c ≤ k' → k' < c + m → ∀ i : ℕ, r k' ≤ i → i ≤ r c →
      ∃ k : ℤ, c ≤ k ∧ k ≤ k' ∧ r k = i := by
    intro k' hk'
    induction k', hk' using Int.leInduction with
    | base =>
      intro _ i h1 h2
      exact ⟨c, le_rfl, le_rfl, by omega⟩
    | succ k' hk'' ih =>
      intro hk i h1 h2
      have hb := hbit (k' + 1) (by omega) hk
      simp only [add_sub_cancel_right] at hb
      by_cases hi : r k' ≤ i
      · obtain ⟨k, hk1, hk2, hk3⟩ := ih (by omega) i hi h2
        exact ⟨k, hk1, by omega, hk3⟩
      · exact ⟨k' + 1, by omega, le_rfl, by omega⟩
  set K : ℤ := c + m - 1 with hK
  have hcK : c ≤ K := by omega
  have hKm : K < c + m := by omega
  have hi1j : r K ≤ r c := hanti c K le_rfl hcK hKm
  have hrange : ∀ i x : ℕ, mu.rowLen i ≤ x → x < nu.rowLen i → r K ≤ i ∧ i ≤ r c := by
    intro i x hx1 hx2
    obtain ⟨h1, h2, h3⟩ := hrow_eq i x hx1 hx2
    have a1 := hanti c ((x : ℤ) - i) le_rfl h1 h2
    have a2 := hanti ((x : ℤ) - i) K h1 (by omega) hKm
    omega
  have hmuj : (mu.rowLen (r c) : ℤ) = c + r c := by
    obtain ⟨a1, a2⟩ := hr' c le_rfl (by omega)
    by_contra hcon
    have h3 := hrow_eq (r c) (c + r c - 1).toNat (by omega) (by omega)
    omega
  have hnuK : (nu.rowLen (r K) : ℤ) = K + r K + 1 := by
    obtain ⟨a1, a2⟩ := hr' K hcK hKm
    by_contra hcon
    have h3 := hrow_eq (r K) (K + r K + 1).toNat (by omega) (by omega)
    omega
  refine ⟨r c, r K, ?_⟩
  refine ⟨hi1j, ?_, ?_, ?_⟩
  · intro i hi
    by_contra hcon
    have hlt : mu.rowLen i < nu.rowLen i := lt_of_le_of_ne (hrow i) (fun h => hcon h.symm)
    have := hrange i (mu.rowLen i) le_rfl hlt
    omega
  · have : ((r c - r K : ℕ) : ℤ) = (r c : ℤ) - r K := by omega
    rw [this]
    omega
  · intro i hi1 hi2
    obtain ⟨k, hk1, hk2, hk3⟩ := hivt K hcK hKm i (by omega) hi2
    obtain ⟨a1, a2⟩ := hr' k hk1 (by omega)
    rw [hk3] at a1 a2
    have hlt : mu.rowLen i < nu.rowLen i := by omega
    have hl1 : 1 ≤ nu.rowLen i := by omega
    obtain ⟨b1, b2, b3⟩ := hrow_eq i (nu.rowLen i - 1) (by omega) (by omega)
    have hκ : ((nu.rowLen i - 1 : ℕ) : ℤ) - i = (nu.rowLen i : ℤ) - 1 - i := by omega
    rw [hκ] at b1 b2 b3
    have hκK : (nu.rowLen i : ℤ) - 1 - i < K := by
      by_contra hcon
      have : (nu.rowLen i : ℤ) - 1 - i = K := by omega
      rw [this] at b3
      omega
    have hb := hbit ((nu.rowLen i : ℤ) - 1 - i + 1) (by omega) (by omega)
    simp only [add_sub_cancel_right] at hb
    obtain ⟨d1, d2⟩ := hr' ((nu.rowLen i : ℤ) - 1 - i + 1) (by omega) (by omega)
    rw [b3] at hb
    rcases hb with hb | hb
    · rw [← hb] at d2
      omega
    · have hr1 : r ((nu.rowLen i : ℤ) - 1 - i + 1) = i - 1 := by omega
      rw [hr1] at d1
      have hm1 := nu.rowLen_anti (i - 1) i (by omega)
      by_contra hcon
      have hlt2 : mu.rowLen (i - 1) + 2 ≤ nu.rowLen i := by
        have : (i - 1 : ℕ) + 1 = i := by omega
        push_cast [Nat.cast_sub (show 1 ≤ i by omega)] at d1
        omega
      have := P1 i (i - 1) (nu.rowLen i - 1) (nu.rowLen i - 2) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      omega

namespace RowMove

/-- **Every ribbon `ν / μ` is a row move.** -/
theorem of_isRibbon {mu nu : YoungDiagram} (hle : mu ≤ nu)
    (hR : IsRibbon (skewDiagram nu mu)) :
    ∃ j i1, RowMove mu nu j i1 (skewDiagram nu mu).card := by
  have hinj := isRibbon_injOn_content hR
  have hcont := isRibbon_contents_eq hR
  have hne : (skewDiagram nu mu).Nonempty := hR.1.2.1
  have hcard : (skewDiagram nu mu).card = (contents (skewDiagram nu mu)).card := by
    have := hR.2
    unfold span at this
    exact this
  have hpos : 0 < (skewDiagram nu mu).card := Finset.card_pos.mpr hne
  refine exists_rowMove_of_cells hle (minContent (skewDiagram nu mu)) hpos ?_ ?_
  · intro i i' x x' h1 h2 h3 h4 h5
    have := hinj (Finset.mem_coe.mpr ((mem_skewDiagram_nat_iff i x).mpr ⟨h1, h2⟩))
      (Finset.mem_coe.mpr ((mem_skewDiagram_nat_iff i' x').mpr ⟨h3, h4⟩))
      (by simp [content, h5])
    have := congrArg Prod.fst this
    simpa using this
  · intro k
    have hmem : (∃ i x : ℕ, mu.rowLen i ≤ x ∧ x < nu.rowLen i ∧ (x : ℤ) - i = k) ↔
        k ∈ contents (skewDiagram nu mu) := by
      rw [mem_contents_iff]
      constructor
      · rintro ⟨i, x, h1, h2, h3⟩
        exact ⟨i, mem_skewDiagram_iff.mpr ⟨i, x, rfl, by omega, h1, h2⟩⟩
      · rintro ⟨i, hi⟩
        obtain ⟨i', x', h1, h2, h3, h4⟩ := mem_skewDiagram_iff.mp hi
        exact ⟨i', x', h3, h4, by omega⟩
    rw [hmem, hcont, Finset.mem_Icc]
    have hc : (contents (skewDiagram nu mu)).card = (skewDiagram nu mu).card := hcard.symm
    rw [hcont, Int.card_Icc] at hc
    have := minContent_le (maxContent_mem hne)
    omega

/-- The southwest row of a row move is determined by `μ` and `ν`. -/
theorem unique_j {mu nu : YoungDiagram} {j i1 j' i1' m : ℕ} (hm : 0 < m)
    (h : RowMove mu nu j i1 m) (h' : RowMove mu nu j' i1' m) : j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have a1 := h'.row_lt hm (i := j') h'.i1_le (le_refl j')
    have a2 := h.outside j' (by omega)
    omega
  · have a1 := h.row_lt hm (i := j) h.i1_le (le_refl j)
    have a2 := h'.outside j (by omega)
    omega

/-- The northeast row of a row move is the smallest row whose β-number lies below the raised
one. -/
theorem i1_bounds {mu nu : YoungDiagram} {j i1 m : ℕ} (hm : 0 < m) (h : RowMove mu nu j i1 m) :
    (mu.rowLen i1 : ℤ) - i1 < mu.rowLen j - j + m ∧
      (∀ i, i < i1 → (mu.rowLen j : ℤ) - j + m < mu.rowLen i - i) := by
  have htop := h.top
  have hjn : ((j - i1 : ℕ) : ℤ) = (j : ℤ) - i1 := by have := h.i1_le; omega
  rw [hjn] at htop
  constructor
  · have := h.row_lt hm (le_refl i1) h.i1_le
    omega
  · intro i hi
    have a1 := nu.rowLen_anti i i1 hi.le
    have a2 := h.outside i (Or.inl hi)
    omega

/-- The row move from `μ` to `ν` with a given southwest row is unique. -/
theorem unique_nu {mu nu nu' : YoungDiagram} {j i1 i1' m : ℕ} (hm : 0 < m)
    (h : RowMove mu nu j i1 m) (h' : RowMove mu nu' j i1' m) : nu = nu' := by
  have hi : i1 = i1' := by
    by_contra hne
    obtain ⟨a1, a2⟩ := h.i1_bounds hm
    obtain ⟨b1, b2⟩ := h'.i1_bounds hm
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := b2 i1 hlt
      omega
    · have := a2 i1' hlt
      omega
  subst hi
  have hrows : ∀ i, nu.rowLen i = nu'.rowLen i := by
    intro i
    by_cases h1 : i < i1 ∨ j < i
    · rw [h.outside i h1, h'.outside i h1]
    · by_cases h2 : i = i1
      · subst h2
        have := h.top
        have := h'.top
        omega
      · rw [h.inner i (by omega) (by omega), h'.inner i (by omega) (by omega)]
  ext ⟨i, x⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, hrows i]

end RowMove

/-- The skew diagram `ν / μ` determines `ν`. -/
theorem skewDiagram_injective {mu nu nu' : YoungDiagram} (h : mu ≤ nu) (h' : mu ≤ nu')
    (heq : skewDiagram nu mu = skewDiagram nu' mu) : nu = nu' := by
  have hrow : ∀ (a b : YoungDiagram), mu ≤ a → mu ≤ b →
      skewDiagram a mu = skewDiagram b mu → ∀ i, a.rowLen i ≤ b.rowLen i := by
    intro a b ha hb hab i
    by_contra hcon
    push Not at hcon
    have hmu : mu.rowLen i ≤ b.rowLen i := by
      by_contra hc
      push Not at hc
      have h1 : (i, b.rowLen i) ∈ mu := YoungDiagram.mem_iff_lt_rowLen.mpr hc
      have h2 := hb h1
      rw [YoungDiagram.mem_iff_lt_rowLen] at h2
      omega
    have hmem : ((i : ℤ), ((a.rowLen i - 1 : ℕ) : ℤ)) ∈ skewDiagram a mu :=
      (mem_skewDiagram_nat_iff _ _).mpr ⟨by omega, by omega⟩
    rw [hab, mem_skewDiagram_nat_iff] at hmem
    omega
  ext ⟨i, x⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen]
  have := hrow nu nu' h h' heq i
  have := hrow nu' nu h' h heq.symm i
  omega

end MN

end Plan

end SkewGluing
