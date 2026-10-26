-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/CSign/Counts.lean
import GluingCore.OlsonHarris.Plan.CornerCase.CSign.Northbound

/-!
# Counting the northbound cells diagonal by diagonal

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis Lemma 5.5.10 (`OlsonHarris2024HopfApplications`),
`ξ(D) = ξ(D*)`: in a connected skew diagram `C` with first rows `ℓ_c` and last rows `h_c`, the
number of cells with a cell to the north on the same northwest ribbon, and the number of cells
with a cell to the north on the same southeast ribbon, are both read diagonal by diagonal:

* `card_nwNorth`: `Σ_c [ℓ_c - ℓ_{c+1} = 1] (h_c - ℓ_{c+1})`;
* `card_seNorth`: `Σ_c [h_c - h_{c+1} = 1] (h_c - ℓ_{c+1})`;

over `minContent C ≤ c < maxContent C`.  The two sums agree because
`2 (A - B)(h_c - ℓ_{c+1}) = (x_{c+1}^2 - x_c^2) + (A^2 - B^2)` for `A = ℓ_c - ℓ_{c+1}`,
`B = h_c - h_{c+1}` and `x_c = h_c - ℓ_c`, and the end diagonals are singletons
(`card_nwNorth_eq_card_seNorth`).

**Differs from the paper's route.**  The thesis proves `ξ(D) = ξ(D*)` by induction on the
ribbon decomposition; here a telescoping identity on the diagonal words is used.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

namespace CSign

variable {C : Diagram}

theorem sum_Ico_int {M : Type*} [AddCommMonoid M] (f : ℤ → M) (p q : ℤ) :
    ∑ c ∈ Finset.Ico p q, f c = ∑ i ∈ Finset.range (q - p).toNat, f (p + i) := by
  refine Finset.sum_nbij' (fun c => (c - p).toNat) (fun i => p + i) ?_ ?_ ?_ ?_ ?_
  · intro c hc; simp only [Finset.mem_Ico] at hc; simp only [Finset.mem_range]; omega
  · intro i hi; simp only [Finset.mem_Ico]; simp only [Finset.mem_range] at hi; omega
  · intro c hc; simp only [Finset.mem_Ico] at hc; omega
  · intro i hi; simp
  · intro c hc; simp only [Finset.mem_Ico] at hc; congr 1; omega

theorem mem_iff_of_eq {hs : HasDiagonalShape C} {i j k : ℤ} (h : j = i + k) :
    (i, j) ∈ C ↔ k ∈ contents C ∧ diagLo C k ≤ i ∧ i ≤ diagHi C k := by
  subst h
  exact hs.mem_iff

/-- The bits of two consecutive diagonals of a connected skew diagram. -/
theorem bits_of_mem {hs : HasDiagonalShape C} {c : ℤ} (h0 : c ∈ contents C)
    (h1 : c + 1 ∈ contents C) :
    (diagLo C c - diagLo C (c + 1) = 0 ∨ diagLo C c - diagLo C (c + 1) = 1) ∧
      (diagHi C c - diagHi C (c + 1) = 0 ∨ diagHi C c - diagHi C (c + 1) = 1) := by
  have := hs.2.2.2.1 (c + 1) h1 (by simpa using h0)
  simpa [bitA, bitB] using this

theorem card_nwNorth (hC : IsConnectedSkew C) :
    ((C.filter (nwNorth C)).card : ℤ) = ∑ c ∈ Finset.Ico (minContent C) (maxContent C),
      (if diagLo C c - diagLo C (c + 1) = 1 then diagHi C c - diagLo C (c + 1) else 0) := by
  have hs := isConnectedSkew_iff_diagonal.mp hC
  rw [Finset.card_eq_sum_card_fiberwise (f := content) (t := Finset.Ico (minContent C)
    (maxContent C)) ?_]
  · push_cast
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_Ico] at hc
    have hc0 : c ∈ contents C := hs.mem_contents_iff.mpr ⟨hc.1, by omega⟩
    have hc1 : c + 1 ∈ contents C := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
    obtain ⟨hA', hB⟩ := bits_of_mem (hs := hs) hc0 hc1
    have hlh := diagLo_le_diagHi hc0
    have hfib : (C.filter (nwNorth C)).filter (fun a => content a = c) =
        if diagLo C c - diagLo C (c + 1) = 1 then
          (Finset.Icc (diagLo C c) (diagHi C c)).image (fun i => (i, i + c)) else ∅ := by
      ext ⟨i, b⟩
      simp only [Finset.mem_filter]
      simp only [nwNorth, content]
      split_ifs with hA
      · simp only [Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          have hb : b = i + c := by omega
          subst hb
          rw [mem_iff_of_eq (hs := hs) rfl] at h1
          exact ⟨i, ⟨h1.2.1, h1.2.2⟩, rfl, rfl⟩
        · rintro ⟨i', ⟨h1, h2⟩, rfl, hb⟩
          have hb' : b = i' + c := hb.symm
          subst hb'
          refine ⟨⟨?_, ?_, ?_⟩, by omega⟩
          · rw [mem_iff_of_eq (hs := hs) rfl]; exact ⟨hc0, h1, h2⟩
          · rw [mem_iff_of_eq (hs := hs) (k := c + 1) (by ring)]
            exact ⟨hc1, by omega, by omega⟩
          · have : i' + c - i' = c := by ring
            rw [this]; omega
      · simp only [Finset.notMem_empty, iff_false]
        rintro ⟨⟨h1, h2, h3⟩, h4⟩
        have hb : b = i + c := by omega
        subst hb
        have : i + c - i = c := by ring
        rw [this] at h3
        omega
    rw [hfib]
    split_ifs with hA
    · rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), Int.card_Icc]
      omega
    · simp
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    obtain ⟨hxC, hn, -⟩ := hx
    have h1 := minContent_le (content_mem_contents hxC)
    have h2 := le_maxContent (content_mem_contents hn)
    rw [content_north] at h2
    rw [Finset.mem_coe, Finset.mem_Ico]; omega

theorem card_seNorth (hC : IsConnectedSkew C) :
    ((C.filter (seNorth C)).card : ℤ) = ∑ c ∈ Finset.Ico (minContent C) (maxContent C),
      (if diagHi C c - diagHi C (c + 1) = 1 then diagHi C c - diagLo C (c + 1) else 0) := by
  have hs := isConnectedSkew_iff_diagonal.mp hC
  rw [Finset.card_eq_sum_card_fiberwise (f := content) (t := Finset.Ico (minContent C)
    (maxContent C)) ?_]
  · push_cast
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_Ico] at hc
    have hc0 : c ∈ contents C := hs.mem_contents_iff.mpr ⟨hc.1, by omega⟩
    have hc1 : c + 1 ∈ contents C := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
    obtain ⟨hA', hB⟩ := bits_of_mem (hs := hs) hc0 hc1
    have hlh := diagLo_le_diagHi hc0
    have hlh1 := diagLo_le_diagHi hc1
    have hfib : (C.filter (seNorth C)).filter (fun a => content a = c) =
        if diagHi C c - diagHi C (c + 1) = 1 then
          (Finset.Icc (diagLo C (c + 1) + 1) (diagHi C c)).image (fun i => (i, i + c)) else ∅ := by
      ext ⟨i, b⟩
      simp only [Finset.mem_filter]
      simp only [seNorth, content]
      split_ifs with hA
      · simp only [Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          have hb : b = i + c := by omega
          subst hb
          rw [mem_iff_of_eq (hs := hs) rfl] at h1
          rw [mem_iff_of_eq (hs := hs) (k := c + 1) (by ring)] at h2
          exact ⟨i, ⟨by omega, h1.2.2⟩, rfl, rfl⟩
        · rintro ⟨i', ⟨h1, h2⟩, rfl, hb⟩
          have hb' : b = i' + c := hb.symm
          subst hb'
          refine ⟨⟨?_, ?_, ?_⟩, by omega⟩
          · rw [mem_iff_of_eq (hs := hs) rfl]; exact ⟨hc0, by omega, h2⟩
          · rw [mem_iff_of_eq (hs := hs) (k := c + 1) (by ring)]
            exact ⟨hc1, by omega, by omega⟩
          · have : i' + c - i' = c := by ring
            rw [this]; omega
      · simp only [Finset.notMem_empty, iff_false]
        rintro ⟨⟨h1, h2, h3⟩, h4⟩
        have hb : b = i + c := by omega
        subst hb
        have : i + c - i = c := by ring
        rw [this] at h3
        omega
    rw [hfib]
    split_ifs with hA
    · rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), Int.card_Icc]
      omega
    · simp
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    obtain ⟨hxC, hn, -⟩ := hx
    have h1 := minContent_le (content_mem_contents hxC)
    have h2 := le_maxContent (content_mem_contents hn)
    rw [content_north] at h2
    rw [Finset.mem_coe, Finset.mem_Ico]; omega

/-- The telescoping identity behind `ξ(D) = ξ(D*)`. -/
theorem sum_identity (a b : ℤ → ℤ) (p : ℤ) (n : ℕ)
    (hA : ∀ i : ℕ, i < n → (b (p + i) - b (p + i + 1) = 0 ∨ b (p + i) - b (p + i + 1) = 1))
    (hB : ∀ i : ℕ, i < n → (a (p + i) - a (p + i + 1) = 0 ∨ a (p + i) - a (p + i + 1) = 1)) :
    2 * ∑ i ∈ Finset.range n, (((b (p + i) - b (p + i + 1)) - (a (p + i) - a (p + i + 1))) *
        (a (p + i) - b (p + i + 1))) =
      ((a (p + n) - b (p + n)) ^ 2 - (a p - b p) ^ 2) +
        ((b p - b (p + n)) - (a p - a (p + n))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih (fun i hi => hA i (by omega))
      (fun i hi => hB i (by omega))]
    have h1 := hA n (by omega)
    have h2 := hB n (by omega)
    have e : (p + ((n + 1 : ℕ) : ℤ)) = p + n + 1 := by push_cast; ring
    rw [e]
    have key : 2 * (((b (p + n) - b (p + n + 1)) - (a (p + n) - a (p + n + 1))) *
        (a (p + n) - b (p + n + 1))) =
        ((a (p + n + 1) - b (p + n + 1)) ^ 2 - (a (p + n) - b (p + n)) ^ 2) +
          ((b (p + n) - b (p + n + 1)) - (a (p + n) - a (p + n + 1))) := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      · have e1 : b (p + n + 1) = b (p + n) - (b (p + n) - b (p + n + 1)) := by ring
        have e2 : a (p + n + 1) = a (p + n) - (a (p + n) - a (p + n + 1)) := by ring
        rw [e1, e2, h1, h2]; ring
    linarith

/-- **Thesis Lemma 5.5.10.**  In a connected skew diagram the number of cells with a cell to the
north on the same northwest ribbon equals the number of those on the same southeast ribbon:
`ξ(D) = ξ(D*)`. -/
theorem card_nwNorth_eq_card_seNorth (hC : IsConnectedSkew C) :
    (C.filter (nwNorth C)).card = (C.filter (seNorth C)).card := by
  have hs := isConnectedSkew_iff_diagonal.mp hC
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hs.1)
  have h1 := card_nwNorth hC
  have h2 := card_seNorth hC
  rw [sum_Ico_int] at h1 h2
  set n := (maxContent C - minContent C).toNat with hn
  have hnn : minContent C + n = maxContent C := by omega
  have hbits : ∀ i : ℕ, i < n →
      (diagLo C (minContent C + i) - diagLo C (minContent C + i + 1) = 0 ∨
        diagLo C (minContent C + i) - diagLo C (minContent C + i + 1) = 1) ∧
      (diagHi C (minContent C + i) - diagHi C (minContent C + i + 1) = 0 ∨
        diagHi C (minContent C + i) - diagHi C (minContent C + i + 1) = 1) := by
    intro i hi
    exact bits_of_mem (hs := hs) (hs.mem_contents_iff.mpr ⟨by omega, by omega⟩)
      (hs.mem_contents_iff.mpr ⟨by omega, by omega⟩)
  have hid := sum_identity (fun c => diagHi C c) (fun c => diagLo C c) (minContent C) n
    (fun i hi => (hbits i hi).1) (fun i hi => (hbits i hi).2)
  simp only [hnn] at hid
  have he := MarkedInner.D_ends hC
  rw [← he.1, ← he.2] at hid
  have hdiff : ∑ i ∈ Finset.range n,
      ((if diagLo C (minContent C + i) - diagLo C (minContent C + i + 1) = 1 then
        diagHi C (minContent C + i) - diagLo C (minContent C + i + 1) else 0) -
      (if diagHi C (minContent C + i) - diagHi C (minContent C + i + 1) = 1 then
        diagHi C (minContent C + i) - diagLo C (minContent C + i + 1) else 0)) =
      ∑ i ∈ Finset.range n, (((diagLo C (minContent C + i) - diagLo C (minContent C + i + 1)) -
        (diagHi C (minContent C + i) - diagHi C (minContent C + i + 1))) *
        (diagHi C (minContent C + i) - diagLo C (minContent C + i + 1))) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hA, hB⟩ := hbits i (Finset.mem_range.mp hi)
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]
  have hz : ∑ i ∈ Finset.range n, (((diagLo C (minContent C + i) -
      diagLo C (minContent C + i + 1)) - (diagHi C (minContent C + i) -
      diagHi C (minContent C + i + 1))) * (diagHi C (minContent C + i) -
      diagLo C (minContent C + i + 1))) = 0 := by
    nlinarith [hid]
  have : ((C.filter (nwNorth C)).card : ℤ) = (C.filter (seNorth C)).card := by
    rw [h1, h2, ← sub_eq_zero, ← Finset.sum_sub_distrib, hdiff, hz]
  exact_mod_cast this

/-! ### Checked examples -/

section Examples

/-- The outer `(4, 3, 3, 1) / (2, 1)`. -/
def countOuter : Diagram := skewOf [4, 3, 3, 1] [2, 1]

/-- `ξ(D) = ξ(D*)` on a connected skew diagram: both counts are positive, and equal. -/
example : IsConnectedSkew countOuter ∧
    (countOuter.filter (nwNorth countOuter)).card = 3 ∧
    (countOuter.filter (seNorth countOuter)).card = 3 := by
  decide +kernel

end Examples

end CSign

end Corner

end Plan

end GluingCore
