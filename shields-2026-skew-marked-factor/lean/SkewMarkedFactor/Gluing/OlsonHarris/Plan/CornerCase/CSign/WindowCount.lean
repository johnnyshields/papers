/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/CSign/WindowCount.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.CornerCase.CSign.Removal

/-!
# Northbound cells of a ribbon

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the count of the northbound boxes of a ribbon `A` removable on
the right or on the left from a connected `D` in the proof of thesis Lemma 5.5.11
(`OlsonHarris2024HopfApplications`).

* `card_window_nwNorth`: the border strip of the last cells of the diagonals `n₀, …, n₀ + m - 1`
  has `ℓ_{n₀} - ℓ_{min(n₀ + m, M)}` cells with a northern neighbor on the same northwest ribbon;
* `card_left_seNorth`: a ribbon of size `m` removable on the left, with least content `n₀`,
  is the strip of the first cells of the diagonals `n₀, …, n₀ + m - 1`
  (`mem_leftRibbons_iff`); the number of cells of `D` whose northern neighbor lies in it on the
  same southeast ribbon is `h_{max(n₀ - 1, μ)} - h_{n₀ + m - 1}`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace Corner

namespace CSign

variable {D : Diagram}

/-- The telescoping sum of the first rows with the end cut off at the greatest content. -/
theorem sum_telescope (f : ℤ → ℤ) (M n0 : ℤ) (hn0 : n0 ≤ M) (m : ℕ) :
    ∑ i ∈ Finset.range m, (if n0 + i + 1 ≤ M then f (n0 + i) - f (n0 + i + 1) else 0) =
      f n0 - f (min (n0 + m) M) := by
  induction m with
  | zero => simp [min_eq_left hn0]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have e : n0 + ((m + 1 : ℕ) : ℤ) = n0 + m + 1 := by push_cast; ring
    rw [e]
    by_cases h : n0 + m + 1 ≤ M
    · simp only [h, ite_true]
      rw [min_eq_left (by omega), min_eq_left h]; ring
    · simp only [h, ite_false]
      rw [min_eq_right (by omega), min_eq_right (by omega)]; ring

theorem nwNorth_last_iff (hD : IsConnectedSkew D) {c : ℤ} (hc : c ∈ contents D) :
    nwNorth D (diagHi D c, diagHi D c + c) ↔
      c + 1 ∈ contents D ∧ diagLo D c - diagLo D (c + 1) = 1 := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hlh := diagLo_le_diagHi hc
  unfold nwNorth
  have hcont : content (diagHi D c, diagHi D c + c) = c := by simp [content]
  simp only [hcont]
  constructor
  · rintro ⟨hn, hr⟩
    have e : (diagHi D c - 1, diagHi D c + c) ∈ D := hn
    rw [mem_iff_of_eq (hs := hs) (k := c + 1) (by ring)] at e
    exact ⟨e.1, by omega⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨hA, hB⟩ := bits_of_mem (hs := hs) hc h1
    have hlh1 := diagLo_le_diagHi h1
    refine ⟨?_, by omega⟩
    show (diagHi D c - 1, diagHi D c + c) ∈ D
    rw [mem_iff_of_eq (hs := hs) (k := c + 1) (by ring)]
    exact ⟨h1, by omega, by omega⟩

theorem card_window_nwNorth (hD : IsConnectedSkew D) {n0 : ℤ} {m : ℕ}
    (h0 : n0 ∈ contents D) (h1 : n0 + m - 1 ∈ contents D) :
    (((windowRibbon D n0 m).filter (nwNorth D)).card : ℤ) =
      diagLo D n0 - diagLo D (min (n0 + m) (maxContent D)) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  unfold windowRibbon
  rw [Finset.filter_image, Finset.card_image_of_injective _ (fun x y h => by
    simp only [Prod.mk.injEq] at h; omega)]
  have hsum : (((Finset.Ico n0 (n0 + m)).filter
      (fun c => nwNorth D (diagHi D c, diagHi D c + c))).card : ℤ) =
      ∑ i ∈ Finset.range m, (if n0 + i + 1 ≤ maxContent D then
        diagLo D (n0 + i) - diagLo D (n0 + i + 1) else 0) := by
    rw [Finset.card_filter, sum_Ico_int, show (n0 + m - n0).toNat = m by omega]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hci : n0 + i ∈ contents D :=
      hs.mem_contents_iff.mpr ⟨by have := (hs.mem_contents_iff.mp h0).1; omega, by
        have := (hs.mem_contents_iff.mp h1).2; omega⟩
    by_cases hM : n0 + i + 1 ≤ maxContent D
    · have hc1 : n0 + i + 1 ∈ contents D :=
        hs.mem_contents_iff.mpr ⟨by have := (hs.mem_contents_iff.mp h0).1; omega, hM⟩
      obtain ⟨hA, -⟩ := bits_of_mem (hs := hs) hci hc1
      simp only [hM, ite_true]
      by_cases hA1 : diagLo D (n0 + i) - diagLo D (n0 + i + 1) = 1
      · have := (nwNorth_last_iff hD hci).mpr ⟨hc1, hA1⟩
        simp only [this, ite_true, hA1]
      · have : ¬ nwNorth D (diagHi D (n0 + i), diagHi D (n0 + i) + (n0 + i)) :=
          fun h => hA1 ((nwNorth_last_iff hD hci).mp h).2
        simp only [this, ite_false]
        omega
    · have : ¬ nwNorth D (diagHi D (n0 + i), diagHi D (n0 + i) + (n0 + i)) := fun h => hM (by
        have := (nwNorth_last_iff hD hci).mp h
        have := (hs.mem_contents_iff.mp this.1).2; omega)
      simp only [hM, this, ite_false]
  rw [hsum, sum_telescope (fun c => diagLo D c) (maxContent D) n0
    (hs.mem_contents_iff.mp h0).2]

/-- **A ribbon removable on the left is a strip of first cells.**  A ribbon of size `m` removable
on the left from a connected `D`, with least content `n₀`, consists of the first cells of the
diagonals `n₀, …, n₀ + m - 1`. -/
theorem mem_leftRibbons_iff (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {A : Diagram}
    (hA : A ∈ leftRibbons D m) {n0 : ℤ} (hn0 : minContent A = n0) (y : ℤ × ℤ) :
    y ∈ A ↔ n0 ≤ content y ∧ content y < n0 + m ∧ y.1 = diagLo D (content y) := by
  subst hn0
  obtain ⟨j', -, -, -, -, hw⟩ := left_eq_rotate_window hD hm hA
  have hne : D.Nonempty := hD.2.1
  have hmc := minContent_of_rotate_window hD hm hw
  have hsp := span_eq_of_isConnectedSkew hD
  have hmin' := minContent_rotate hne
  have hyA : y ∈ A ↔ -y ∈ rotate A := by
    rw [mem_rotate, neg_neg]
  rw [hyA, hw, mem_windowRibbon, diagHi_rotate]
  have hc : content (-y) = -content y := by simp [content]; ring
  rw [hc, neg_neg]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, by omega, ?_⟩
    simp only [Prod.fst_neg] at h3
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, by omega, ?_⟩
    simp only [Prod.fst_neg]
    omega

theorem sum_telescope_hi (f : ℤ → ℤ) (μ n0 : ℤ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (if μ + 1 ≤ n0 + i then f (n0 + i - 1) - f (n0 + i) else 0) =
      f (max (n0 - 1) μ) - f (max (n0 + m - 1) μ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have e : n0 + ((m + 1 : ℕ) : ℤ) = n0 + m + 1 := by push_cast; ring
    rw [e]
    by_cases h : μ + 1 ≤ n0 + m
    · simp only [h, ite_true]
      rw [max_eq_left (by omega : μ ≤ n0 + m - 1),
        max_eq_left (by omega : μ ≤ n0 + m + 1 - 1)]
      have : n0 + (m : ℤ) + 1 - 1 = n0 + m := by ring
      rw [this]; ring
    · simp only [h, ite_false]
      rw [max_eq_right (by omega : n0 + (m : ℤ) - 1 ≤ μ),
        max_eq_right (by omega : n0 + (m : ℤ) + 1 - 1 ≤ μ)]
      ring

theorem card_left_seNorth (hD : IsConnectedSkew D) {m : ℕ} (hm : 0 < m) {A : Diagram}
    (hA : A ∈ leftRibbons D m) {j : ℤ} (hj0 : 0 ≤ j) (hjm : j + m ≤ span D)
    (hn0 : minContent A = minContent D + j) :
    ((((D.filter (seNorth D)).filter (fun d => (d.1 - 1, d.2) ∈ A)).card : ℕ) : ℤ) =
      diagHi D (max (minContent D + j - 1) (minContent D)) -
        diagHi D (minContent D + j + m - 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hmem := mem_leftRibbons_iff hD hm hA hn0
  set μ := minContent D with hμ
  set n0 := μ + j with hn0'
  have hcont : ∀ c, μ ≤ c → c ≤ maxContent D → c ∈ contents D :=
    fun c h1 h2 => hs.mem_contents_iff.mpr ⟨h1, h2⟩
  have hset : (D.filter (seNorth D)).filter (fun d => (d.1 - 1, d.2) ∈ A) =
      ((Finset.Ico n0 (n0 + m)).filter
        (fun c => μ + 1 ≤ c ∧ diagHi D (c - 1) - diagHi D c = 1)).image
        (fun c => (diagLo D c + 1, diagLo D c + c)) := by
    ext ⟨i, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
    simp only [seNorth, content, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hd, hn, hr⟩, hnA⟩
      have h1 := (hmem (i - 1, b)).mp hnA
      simp only [content] at h1
      refine ⟨b - (i - 1), ⟨⟨by omega, by omega⟩, ?_, ?_⟩, ?_, ?_⟩
      · have := content_mem_contents hd
        have := minContent_le this
        simp only [content] at this
        omega
      · have e : b - (i - 1) - 1 = b - i := by ring
        rw [e]
        have e2 : b - (i - 1) = b - i + 1 := by ring
        rw [e2]; omega
      · rw [← h1.2.2]; ring
      · rw [← h1.2.2]; ring
    · rintro ⟨c, ⟨⟨hc1, hc2⟩, hc3, hc4⟩, rfl, rfl⟩
      have hcM : c ≤ maxContent D := by omega
      have hc0 : c ∈ contents D := hcont c (by omega) hcM
      have hc1' : c - 1 ∈ contents D := hcont (c - 1) (by omega) (by omega)
      obtain ⟨hA', -⟩ := bits_of_mem (hs := hs) hc1' (by simpa using hc0)
      have hlh := diagLo_le_diagHi hc0
      have hlh1 := diagLo_le_diagHi hc1'
      have hnmem : (diagLo D c, diagLo D c + c) ∈ D := diagLo_mem hc0
      have ee : c - 1 + 1 = c := by ring
      simp only [ee] at hA'
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [mem_iff_of_eq (hs := hs) (k := c - 1) (by ring)]
        exact ⟨hc1', by omega, by omega⟩
      · simpa using hnmem
      · have e1 : diagLo D c + c - (diagLo D c + 1) = c - 1 := by ring
        rw [e1, ee]; omega
      · rw [hmem]
        simp only [content]
        refine ⟨by omega, by omega, by simp⟩
  rw [hset, Finset.card_image_of_injective _ (fun x y h => by
    simp only [Prod.mk.injEq] at h; omega)]
  rw [Finset.card_filter, sum_Ico_int, show (n0 + m - n0).toNat = m by omega]
  push_cast
  have hterm : ∀ i ∈ Finset.range m,
      (if μ + 1 ≤ n0 + i ∧ diagHi D (n0 + i - 1) - diagHi D (n0 + i) = 1 then (1 : ℤ) else 0) =
      (if μ + 1 ≤ n0 + i then diagHi D (n0 + i - 1) - diagHi D (n0 + i) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases h1 : μ + 1 ≤ n0 + i
    · have hc1 : n0 + i - 1 ∈ contents D := hcont _ (by omega) (by omega)
      have hc0 : n0 + i ∈ contents D := hcont _ (by omega) (by omega)
      obtain ⟨-, hB⟩ := bits_of_mem (hs := hs) hc1 (by simpa using hc0)
      have ee : n0 + i - 1 + 1 = n0 + i := by ring
      simp only [ee] at hB
      simp only [h1, true_and, ite_true]
      by_cases h2 : diagHi D (n0 + i - 1) - diagHi D (n0 + i) = 1
      · simp only [h2, ite_true]
      · simp only [h2, ite_false]; omega
    · simp [h1]
  have := sum_telescope_hi (fun c => diagHi D c) μ n0 m
  rw [Finset.sum_congr rfl hterm, this]
  have e : n0 + (m : ℤ) - 1 = μ + j + m - 1 := by rw [hn0']
  rw [e, max_eq_left (by omega : μ ≤ μ + j + m - 1)]

/-! ### Checked examples -/

section Examples

/-- The strip of the last cells of the diagonals `-1, 0, 1` of `(3, 3, 2) / (1, 1)` has
`ℓ_{-1} - ℓ_{min(2, M)}` cells with a northern neighbor on the same northwest ribbon. -/
example : ((windowRibbon (skewOf [3, 3, 2] [1, 1]) (-1) 3).filter
      (nwNorth (skewOf [3, 3, 2] [1, 1]))).card = 2 ∧
    diagLo (skewOf [3, 3, 2] [1, 1]) (-1) -
      diagLo (skewOf [3, 3, 2] [1, 1]) (min (-1 + 3) (maxContent (skewOf [3, 3, 2] [1, 1]))) =
        2 := by
  decide +kernel

/-- A ribbon removable on the left is the strip of the first cells of its diagonals. -/
example : ∀ A ∈ leftRibbons (skewOf [4, 3, 3] [2, 1]) 2, ∀ y ∈ A,
    y.1 = diagLo (skewOf [4, 3, 3] [2, 1]) (content y) := by
  decide +kernel

end Examples

end CSign

end Corner

end Plan

end SkewMarkedFactor.Gluing
