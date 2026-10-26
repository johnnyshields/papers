-- TODO-COPIED (trimmed): skew-factor-gluing/lean/SkewGluing/MixedFold/Legal.lean with the lemma of MixedFold/Rows.lean
import SkewGluing.Local
import SkewGluing.MarkLocality

/-!
# A case-(d) mark from diagonal data

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph» (the legality
conditions I–IV) and «Diagonal geometry» (`lem:gluing-local`), in the converse direction: a mark is
legal as soon as the diagonals of the inner satisfy the conditions that `lem:gluing-local` extracts
from a legal mark.

`MixFoldDiag E q w p s t` records, for a connected skew diagram `E` with contents `[0, q + w - 1]`,
the southeast justification `h_{a+q} = h_a + p` on the marked diagonals, the tails
`ℓ_{a+q} - p - ℓ_a ∈ {-1, 0, 1}` according to the phases `t < s`, the private singleton
diagonals `w` and `q - 1`, and the caps `A_s = 1`, `A_{q+t} = 0` (`B_q = 0` when `t = 0`).  The mark
`mixFoldMark E q p` takes `W₋ = E ∩ (E - v)` for `v = (p, p + q)`, case (d).

Sorry-free.
-/

namespace SkewGluing

theorem mixFold_mem_of_connectedSkew {E : Diagram} (hE : IsConnectedSkew E) (x : ℤ × ℤ) :
    x ∈ E ↔ content x ∈ contents E ∧ diagLo E (content x) ≤ x.1 ∧ x.1 ≤ diagHi E (content x) := by
  have h := (isConnectedSkew_iff_diagonal.mp hE)
  obtain ⟨a, b⟩ := x
  have e : (a, b) = (a, a + (b - a)) := by ext <;> simp
  rw [e]
  have := h.mem_iff (k := b - a) (i := a)
  simp only [content]
  simpa using this


/-- The diagonal data of a case-(d) mark on `E`: period `q`, width `w`, row shift `p`, phases
`t < s`. -/
structure MixFoldDiag (E : Diagram) (q w : ℕ) (p s t : ℤ) : Prop where
  conn : IsConnectedSkew E
  min0 : minContent E = 0
  span_eq : (span E : ℤ) = q + w
  hw : 1 ≤ w
  hwq : w < q
  ht0 : 0 ≤ t
  hts : t < s
  hsw : s ≤ w
  se : ∀ a : ℤ, 0 ≤ a → a < w → diagHi E (a + q) = diagHi E a + p
  tails : ∀ a : ℤ, 0 ≤ a → a < w →
    diagLo E (a + q) = diagLo E a + p + (if a < t then -1 else if a < s then 0 else 1)
  sing_w : diagLo E w = diagHi E w
  sing_q : diagLo E (q - 1) = diagHi E (q - 1)
  capA : diagLo E (s - 1) - diagLo E s = 1
  capH0 : t = 0 → diagHi E (q - 1) = diagHi E q
  capH1 : 1 ≤ t → diagLo E (q + t - 1) = diagLo E (q + t)

/-- The case-(d) mark of `E` with displacement `(p, p + q)` and `W₋ = E ∩ (E - v)`. -/
def mixFoldMark (E : Diagram) (q : ℕ) (p : ℤ) : MarkedInner where
  E := E
  W := E.filter fun x => x + (p, p + (q : ℤ)) ∈ E
  v := (p, p + (q : ℤ))
  case := .d

namespace MixFoldDiag

variable {E : Diagram} {q w : ℕ} {p s t : ℤ}

theorem contents_iff (h : MixFoldDiag E q w p s t) (k : ℤ) :
    k ∈ contents E ↔ 0 ≤ k ∧ k ≤ (q : ℤ) + w - 1 := by
  have hs := isConnectedSkew_iff_diagonal.mp h.conn
  rw [hs.mem_contents_iff]
  have := span_eq_of_isConnectedSkew h.conn
  have h1 := h.span_eq
  have h2 := h.min0
  omega

theorem mem_iff (h : MixFoldDiag E q w p s t) (x : ℤ × ℤ) :
    x ∈ E ↔ 0 ≤ content x ∧ content x ≤ (q : ℤ) + w - 1 ∧ diagLo E (content x) ≤ x.1 ∧
      x.1 ≤ diagHi E (content x) := by
  rw [mixFold_mem_of_connectedSkew h.conn, h.contents_iff]
  tauto

theorem lo_le_hi (h : MixFoldDiag E q w p s t) {k : ℤ} (h0 : 0 ≤ k) (h1 : k ≤ (q : ℤ) + w - 1) :
    diagLo E k ≤ diagHi E k :=
  diagLo_le_diagHi ((h.contents_iff k).mpr ⟨h0, h1⟩)

theorem bits (h : MixFoldDiag E q w p s t) {k : ℤ} (h0 : 1 ≤ k) (h1 : k ≤ (q : ℤ) + w - 1) :
    (diagLo E (k - 1) - diagLo E k = 0 ∨ diagLo E (k - 1) - diagLo E k = 1) ∧
      (diagHi E (k - 1) - diagHi E k = 0 ∨ diagHi E (k - 1) - diagHi E k = 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp h.conn
  have := hs.2.2.2.1 k ((h.contents_iff k).mpr ⟨by omega, h1⟩)
    ((h.contents_iff (k - 1)).mpr ⟨by omega, by omega⟩)
  simp only [bitA, bitB, Finset.mem_insert, Finset.mem_singleton] at this
  exact this

theorem sing_first (h : MixFoldDiag E q w p s t) : diagLo E 0 = diagHi E 0 := by
  have hs := isConnectedSkew_iff_diagonal.mp h.conn
  exact hs.2.2.2.2 0 ((h.contents_iff 0).mpr ⟨le_refl _, by have := h.hwq; omega⟩)
    (Or.inl (fun hm => by rw [h.contents_iff] at hm; omega))

theorem sing_last (h : MixFoldDiag E q w p s t) :
    diagLo E ((q : ℤ) + w - 1) = diagHi E ((q : ℤ) + w - 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp h.conn
  exact hs.2.2.2.2 _ ((h.contents_iff _).mpr ⟨by have := h.hwq; have := h.hw; omega, le_refl _⟩)
    (Or.inr (fun hm => by rw [h.contents_iff] at hm; omega))

/-- The cells of `W₋`. -/
theorem mem_W (h : MixFoldDiag E q w p s t) (x : ℤ × ℤ) :
    x ∈ (mixFoldMark E q p).W ↔ 0 ≤ content x ∧ content x < w ∧
      diagLo E (content x) + (if content x < s then 0 else 1) ≤ x.1 ∧
        x.1 ≤ diagHi E (content x) := by
  unfold mixFoldMark
  simp only [Finset.mem_filter]
  have hc : content (x + (p, p + (q : ℤ))) = content x + q := by
    simp [content]; ring
  rw [h.mem_iff x, h.mem_iff (x + (p, p + (q : ℤ))), hc]
  simp only [Prod.fst_add]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩
    have hq := h.hwq
    have hse := h.se (content x) h1 (by omega)
    have htl := h.tails (content x) h1 (by omega)
    have hlh := h.lo_le_hi (k := content x) h1 (by omega)
    have hts := h.hts
    refine ⟨h1, by omega, ?_, h4⟩
    split_ifs at htl ⊢ <;> omega
  · rintro ⟨h1, h2, h3, h4⟩
    have hq := h.hwq
    have hse := h.se (content x) h1 h2
    have htl := h.tails (content x) h1 h2
    have hts := h.hts
    refine ⟨⟨h1, by omega, ?_, h4⟩, by omega, by omega, ?_, ?_⟩
    · split_ifs at h3 htl <;> omega
    · split_ifs at h3 htl <;> omega
    · omega

theorem mem_upper (h : MixFoldDiag E q w p s t) (x : ℤ × ℤ) :
    x ∈ (mixFoldMark E q p).upper ↔ (q : ℤ) ≤ content x ∧ content x < (q : ℤ) + w ∧
      diagLo E (content x) + (if content x - q < t then 1 else 0) ≤ x.1 ∧
        x.1 ≤ diagHi E (content x) := by
  unfold MarkedInner.upper
  rw [mem_translate, h.mem_W]
  have hv : (mixFoldMark E q p).v = (p, p + (q : ℤ)) := rfl
  rw [hv]
  have hc : content (x - (p, p + (q : ℤ))) = content x - q := by simp [content]; ring
  rw [hc]
  simp only [Prod.fst_sub]
  have hq := h.hwq
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hse := h.se (content x - q) h1 h2
    have htl := h.tails (content x - q) h1 h2
    have hts := h.hts
    have e : content x - q + q = content x := by ring
    rw [e] at hse htl
    refine ⟨by omega, by omega, ?_, by omega⟩
    split_ifs at htl h3 ⊢ <;> omega
  · rintro ⟨h1, h2, h3, h4⟩
    have hse := h.se (content x - q) (by omega) (by omega)
    have htl := h.tails (content x - q) (by omega) (by omega)
    have hts := h.hts
    have e : content x - q + q = content x := by ring
    rw [e] at hse htl
    refine ⟨by omega, by omega, ?_, by omega⟩
    split_ifs at htl h3 ⊢ <;> omega

theorem mem_middle (h : MixFoldDiag E q w p s t) (x : ℤ × ℤ) :
    x ∈ (mixFoldMark E q p).middle ↔ x ∈ E ∧
      (content x < w → s ≤ content x ∧ x.1 = diagLo E (content x)) ∧
      ((q : ℤ) ≤ content x → content x - q < t ∧ x.1 = diagLo E (content x)) := by
  unfold MarkedInner.middle
  have hEE : (mixFoldMark E q p).E = E := rfl
  rw [hEE, Finset.mem_sdiff, Finset.mem_union, h.mem_W, h.mem_upper, h.mem_iff x]
  have hq := h.hwq
  have hts := h.hts
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, hn⟩
    refine ⟨⟨h1, h2, h3, h4⟩, fun hc => ?_, fun hc => ?_⟩
    · by_contra hcon
      apply hn
      left
      refine ⟨h1, hc, ?_, h4⟩
      by_cases hcs : content x < s
      · simp only [hcs, ite_true]; omega
      · simp only [hcs, ite_false]
        have : x.1 ≠ diagLo E (content x) := fun he => hcon ⟨by omega, he⟩
        omega
    · by_contra hcon
      apply hn
      right
      refine ⟨hc, by omega, ?_, h4⟩
      by_cases hct : content x - q < t
      · simp only [hct, ite_true]
        have : x.1 ≠ diagLo E (content x) := fun he => hcon ⟨hct, he⟩
        omega
      · simp only [hct, ite_false]; omega
  · rintro ⟨⟨h1, h2, h3, h4⟩, hA, hB⟩
    refine ⟨⟨h1, h2, h3, h4⟩, ?_⟩
    rintro (⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩)
    · have := hA k2
      split_ifs at k3 <;> omega
    · have := hB k1
      split_ifs at k3 <;> omega

theorem maxContent_eq (h : MixFoldDiag E q w p s t) : maxContent E = (q : ℤ) + w - 1 := by
  have := span_eq_of_isConnectedSkew h.conn
  have := h.span_eq
  have := h.min0
  omega

theorem W_lo_le_hi (h : MixFoldDiag E q w p s t) {k : ℤ} (h0 : 0 ≤ k) (h1 : k < w) :
    diagLo E k + (if k < s then 0 else 1) ≤ diagHi E k := by
  have hq := h.hwq
  have hse := h.se k h0 h1
  have htl := h.tails k h0 h1
  have hlh := h.lo_le_hi (k := k + q) (by omega) (by omega)
  have hlh2 := h.lo_le_hi (k := k) h0 (by omega)
  have hts := h.hts
  have e : k + (q : ℤ) = k + q := rfl
  split_ifs at htl ⊢ <;> omega

theorem W_connected (h : MixFoldDiag E q w p s t) : IsConnectedSkew (mixFoldMark E q p).W := by
  have hq := h.hwq
  have hw1 := h.hw
  refine isConnectedSkew_of_rows _ 0 ((w : ℤ) - 1) (fun k => diagLo E k + (if k < s then 0 else 1))
    (fun k => diagHi E k) (by omega) (fun i k => ?_) (fun k h0 h1 => h.W_lo_le_hi h0 (by omega))
    (fun k h0 h1 => ?_) (fun k h0 h1 => ?_) ?_ ?_
  · rw [h.mem_W (i, i + k)]
    simp only [content_mk_add]
    constructor
    · rintro ⟨a, b, c, d⟩; exact ⟨a, by omega, c, d⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨a, by omega, c, d⟩
  · have hb := (h.bits (k := k) (by omega) (by omega)).1
    have hts := h.hts
    have hcap := h.capA
    by_cases hks : k < s
    · have : k - 1 < s := by omega
      simp only [hks, this, ite_true]; omega
    · by_cases hkeq : k = s
      · have hcap' : diagLo E (k - 1) - diagLo E k = 1 := by rw [hkeq]; exact hcap
        have h1 : k - 1 < s := by omega
        simp only [hks, h1, ite_true, ite_false]
        omega
      · have : ¬ (k - 1 < s) := by omega
        simp only [hks, this, ite_false]; omega
  · exact (h.bits (k := k) (by omega) (by omega)).2
  · have h0 := h.sing_first
    have hts := h.hts
    have hs0 : (0 : ℤ) < s := by have := h.ht0; omega
    simp only [hs0, ite_true]; omega
  · have hse := h.se ((w : ℤ) - 1) (by omega) (by omega)
    have htl := h.tails ((w : ℤ) - 1) (by omega) (by omega)
    have hl := h.sing_last
    have hts := h.hts
    have hsw := h.hsw
    have e : (w : ℤ) - 1 + q = (q : ℤ) + w - 1 := by ring
    rw [e] at hse htl
    split_ifs at htl ⊢ <;> omega

theorem sw_mem_W (h : MixFoldDiag E q w p s t) : sw E ∈ (mixFoldMark E q p).W := by
  have hEne : E.Nonempty := h.conn.2.1
  rw [h.mem_W]
  have hc : content (sw E) = 0 := by rw [content_sw hEne, h.min0]
  have hf : (sw E).1 = diagLo E 0 := by unfold sw; rw [h.min0]
  rw [hc, hf]
  have hs0 : (0 : ℤ) < s := by have := h.hts; have := h.ht0; omega
  have := h.sing_first
  simp only [hs0, ite_true]
  refine ⟨le_refl _, by have := h.hw; omega, by omega, by omega⟩

theorem ne_mem_upper (h : MixFoldDiag E q w p s t) : ne E ∈ (mixFoldMark E q p).upper := by
  have hEne : E.Nonempty := h.conn.2.1
  rw [h.mem_upper]
  have hc : content (ne E) = (q : ℤ) + w - 1 := by rw [content_ne hEne, h.maxContent_eq]
  have hf : (ne E).1 = diagLo E ((q : ℤ) + w - 1) := by unfold ne; rw [h.maxContent_eq]
  rw [hc, hf]
  have hts := h.hts
  have hsw := h.hsw
  have hnt : ¬ ((q : ℤ) + w - 1 - q < t) := by omega
  have := h.sing_last
  simp only [hnt, ite_false]
  refine ⟨by have := h.hw; omega, by omega, by omega, by omega⟩

theorem contents_W (h : MixFoldDiag E q w p s t) :
    contents (mixFoldMark E q p).W = Finset.Icc 0 ((w : ℤ) - 1) := by
  ext k
  rw [mem_contents_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi⟩
    have := (h.mem_W (i, i + k)).mp hi
    simp only [content] at this
    omega
  · rintro ⟨h0, h1⟩
    refine ⟨diagLo E k + (if k < s then 0 else 1), (h.mem_W _).mpr ?_⟩
    simp only [content]
    have := h.W_lo_le_hi h0 (by omega)
    refine ⟨by omega, by omega, ?_, ?_⟩
    all_goals simp
    all_goals omega

theorem width_eq (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).width = w := by
  unfold MarkedInner.width span
  rw [h.contents_W, Int.card_Icc]
  have := h.hw
  omega

theorem period_eq : (mixFoldMark E q p).period = q := by
  unfold MarkedInner.period content mixFoldMark
  simp

/-- The middle cell on the diagonal of content `c`: the first cell of `E` there. -/
def midCell (E : Diagram) (c : ℤ) : ℤ × ℤ := (diagLo E c, diagLo E c + c)

theorem midCell_content (E : Diagram) (c : ℤ) : content (midCell E c) = c := by
  simp [midCell, content]

theorem minContent_middle (h : MixFoldDiag E q w p s t) :
    minContent (mixFoldMark E q p).middle = s ∧ midCell E s ∈ (mixFoldMark E q p).middle := by
  have hts := h.hts
  have ht0 := h.ht0
  have hsw := h.hsw
  have hq := h.hwq
  have hmem : midCell E s ∈ (mixFoldMark E q p).middle := by
    rw [h.mem_middle, h.mem_iff, midCell_content]
    have := h.lo_le_hi (k := s) (by omega) (by omega)
    refine ⟨⟨by omega, by omega, le_refl _, ?_⟩, fun _ => ⟨le_refl _, rfl⟩, fun hc => ?_⟩
    · simpa [midCell] using this
    · omega
  refine ⟨?_, hmem⟩
  apply minContent_eq_of (by have := content_mem_contents hmem; rwa [midCell_content] at this)
  intro k hk
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
  rw [h.mem_middle] at hi
  simp only [content] at hi
  have := hi.2.1
  by_cases hkw : k < w
  · have := (hi.2.1 (by simpa using hkw)).1; simpa using this
  · omega

theorem maxContent_middle (h : MixFoldDiag E q w p s t) :
    maxContent (mixFoldMark E q p).middle = (q : ℤ) + t - 1 ∧
      midCell E ((q : ℤ) + t - 1) ∈ (mixFoldMark E q p).middle := by
  have hts := h.hts
  have hsw := h.hsw
  have hq := h.hwq
  have ht0 := h.ht0
  have hmem : midCell E ((q : ℤ) + t - 1) ∈ (mixFoldMark E q p).middle := by
    rw [h.mem_middle, h.mem_iff, midCell_content]
    have := h.lo_le_hi (k := (q : ℤ) + t - 1) (by omega) (by omega)
    refine ⟨⟨by omega, by omega, le_refl _, ?_⟩, fun hc => by omega, fun hc => ⟨by omega, rfl⟩⟩
    · simpa [midCell] using this
  refine ⟨?_, hmem⟩
  apply maxContent_eq_of (by have := content_mem_contents hmem; rwa [midCell_content] at this)
  intro k hk
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hk
  rw [h.mem_middle] at hi
  simp only [content] at hi
  by_cases hkq : (q : ℤ) ≤ k
  · have := (hi.2.2 (by simpa using hkq)).1; simp at this; omega
  · omega

theorem removals_W (h : MixFoldDiag E q w p s t) :
    IsConnectedSkew (E \ (mixFoldMark E q p).W) := by
  have hq := h.hwq
  have hw1 := h.hw
  have hts := h.hts
  have hsw := h.hsw
  have ht0 := h.ht0
  refine isConnectedSkew_of_rows _ s ((q : ℤ) + w - 1) (fun k => diagLo E k)
    (fun k => if k < w then diagLo E k else diagHi E k) (by omega) (fun i k => ?_)
    (fun k h0 h1 => ?_) (fun k h0 h1 => (h.bits (k := k) (by omega) h1).1) (fun k h0 h1 => ?_)
    ?_ ?_
  · rw [Finset.mem_sdiff, h.mem_iff (i, i + k), h.mem_W (i, i + k)]
    simp only [content_mk_add]
    constructor
    · rintro ⟨⟨a, b, c, d⟩, hn⟩
      by_cases hcw : k < w
      · have hn' : ¬ (diagLo E (k) + (if k < s then 0 else 1) ≤ i) :=
          fun hh => hn ⟨a, hcw, hh, d⟩
        refine ⟨?_, b, c, ?_⟩
        · by_contra hcon
          have : k < s := by omega
          simp only [this, ite_true] at hn'; omega
        · simp only [hcw, ite_true]
          by_cases hcs : k < s
          · simp only [hcs, ite_true] at hn'; omega
          · simp only [hcs, ite_false] at hn'; omega
      · refine ⟨by omega, b, c, ?_⟩
        simp only [hcw, ite_false]; exact d
    · rintro ⟨a, b, c, d⟩
      by_cases hcw : k < w
      · simp only [hcw, ite_true] at d
        refine ⟨⟨by omega, b, c, ?_⟩, ?_⟩
        · have := h.lo_le_hi (k := k) (by omega) b; omega
        · rintro ⟨e1, e2, e3, e4⟩
          by_cases hcs : k < s
          · omega
          · simp only [hcs, ite_false] at e3; omega
      · simp only [hcw, ite_false] at d
        refine ⟨⟨by omega, b, c, d⟩, ?_⟩
        rintro ⟨e1, e2, e3, e4⟩
        omega
  · split_ifs
    · exact le_refl _
    · exact h.lo_le_hi (by omega) h1
  · by_cases hk : k < w
    · have h' : k - 1 < w := by omega
      simp only [hk, h', ite_true]
      exact (h.bits (k := k) (by omega) h1).1
    · by_cases hk2 : k = w
      · have h' : k - 1 < w := by omega
        simp only [hk, h', ite_true, ite_false]
        have := h.sing_w
        rw [hk2]
        have e := (h.bits (k := (w : ℤ)) (by omega) (by omega)).1
        omega
      · have h' : ¬ (k - 1 < w) := by omega
        simp only [hk, h', ite_false]
        exact (h.bits (k := k) (by omega) h1).2
  · by_cases hs : s < w
    · simp only [hs, ite_true]
    · have : s = w := by omega
      simp only [hs, ite_false]; rw [this]; exact h.sing_w
  · have hn : ¬ ((q : ℤ) + w - 1 < w) := by omega
    simp only [hn, ite_false]; exact h.sing_last

theorem removals_upper (h : MixFoldDiag E q w p s t) :
    IsConnectedSkew (E \ (mixFoldMark E q p).upper) := by
  have hq := h.hwq
  have hw1 := h.hw
  have hts := h.hts
  have hsw := h.hsw
  have ht0 := h.ht0
  refine isConnectedSkew_of_rows _ 0 ((q : ℤ) + t - 1) (fun k => diagLo E k)
    (fun k => if k < q then diagHi E k else diagLo E k) (by omega) (fun i k => ?_)
    (fun k h0 h1 => ?_) (fun k h0 h1 => (h.bits (k := k) (by omega) (by omega)).1)
    (fun k h0 h1 => ?_) ?_ ?_
  · rw [Finset.mem_sdiff, h.mem_iff (i, i + k), h.mem_upper (i, i + k)]
    simp only [content_mk_add]
    constructor
    · rintro ⟨⟨a, b, c, d⟩, hn⟩
      by_cases hcq : k < q
      · refine ⟨a, by omega, c, ?_⟩
        simp only [hcq, ite_true]; exact d
      · have hn' : ¬ (diagLo E (k) + (if k - q < t then 1 else 0) ≤ i) :=
          fun hh => hn ⟨by omega, by omega, hh, d⟩
        by_cases hct : k - q < t
        · simp only [hct, ite_true] at hn'
          refine ⟨a, by omega, c, ?_⟩
          simp only [hcq, ite_false]; omega
        · simp only [hct, ite_false] at hn'; omega
    · rintro ⟨a, b, c, d⟩
      by_cases hcq : k < q
      · simp only [hcq, ite_true] at d
        refine ⟨⟨a, by omega, c, d⟩, ?_⟩
        rintro ⟨e1, e2, e3, e4⟩
        omega
      · simp only [hcq, ite_false] at d
        refine ⟨⟨a, by omega, c, ?_⟩, ?_⟩
        · have := h.lo_le_hi (k := k) a (by omega); omega
        · rintro ⟨e1, e2, e3, e4⟩
          by_cases hct : k - q < t
          · simp only [hct, ite_true] at e3; omega
          · omega
  · split_ifs
    · exact h.lo_le_hi h0 (by omega)
    · exact le_refl _
  · by_cases hk : k < q
    · have h' : k - 1 < q := by omega
      simp only [hk, h', ite_true]
      exact (h.bits (k := k) (by omega) (by omega)).2
    · by_cases hk2 : k = q
      · have h' : k - 1 < q := by omega
        simp only [hk, h', ite_true, ite_false]
        have := h.sing_q
        rw [hk2]
        have e := (h.bits (k := (q : ℤ)) (by omega) (by omega)).1
        omega
      · have h' : ¬ (k - 1 < q) := by omega
        simp only [hk, h', ite_false]
        exact (h.bits (k := k) (by omega) (by omega)).1
  · have : (0 : ℤ) < q := by omega
    simp only [this, ite_true]; exact h.sing_first
  · by_cases hq1 : (q : ℤ) + t - 1 < q
    · simp only [hq1, ite_true]
      have : (q : ℤ) + t - 1 = (q : ℤ) - 1 := by omega
      rw [this]; exact h.sing_q
    · simp only [hq1, ite_false]

theorem lowerV (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).LowerV := by
  have hts := h.hts
  have hsw := h.hsw
  have ht0 := h.ht0
  have hq := h.hwq
  obtain ⟨hmin, hmem⟩ := h.minContent_middle
  refine ⟨midCell E s, hmem, by rw [midCell_content, hmin], ?_⟩
  rw [h.mem_W]
  have hc : content ((midCell E s).1 + 1, (midCell E s).2) = s - 1 := by
    simp [midCell, content]
  rw [hc]
  have hcap := h.capA
  have hlh := h.lo_le_hi (k := s - 1) (by omega) (by omega)
  have hs1 : s - 1 < s := by omega
  simp only [hs1, ite_true, midCell]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem upperH (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).UpperH := by
  have hts := h.hts
  have hsw := h.hsw
  have ht0 := h.ht0
  have hq := h.hwq
  obtain ⟨hmax, hmem⟩ := h.maxContent_middle
  refine ⟨midCell E ((q : ℤ) + t - 1), hmem, by rw [midCell_content, hmax], ?_⟩
  rw [h.mem_upper]
  have hc : content ((midCell E ((q : ℤ) + t - 1)).1, (midCell E ((q : ℤ) + t - 1)).2 + 1) =
      (q : ℤ) + t := by
    simp [midCell, content]; ring
  rw [hc]
  have hlh := h.lo_le_hi (k := (q : ℤ) + t) (by omega) (by omega)
  have hnt : ¬ ((q : ℤ) + t - q < t) := by omega
  simp only [hnt, ite_false, midCell]
  by_cases ht1 : 1 ≤ t
  · have := h.capH1 ht1
    refine ⟨by omega, by omega, by omega, by omega⟩
  · have ht00 : t = 0 := by omega
    have e1 := h.capH0 ht00
    have e2 := h.sing_q
    have hlh2 := h.lo_le_hi (k := (q : ℤ)) (by omega) (by omega)
    subst ht00
    have e3 : (q : ℤ) + 0 - 1 = (q : ℤ) - 1 := by ring
    have e4 : (q : ℤ) + 0 = (q : ℤ) := by ring
    rw [e3, e4]
    refine ⟨by omega, by omega, by omega, by omega⟩

theorem nonemptyMark (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).IsNonemptyMark := by
  refine ⟨⟨sw E, h.sw_mem_W⟩, h.W_connected, fun x hx => (Finset.mem_filter.mp hx).1, ?_,
    h.sw_mem_W, h.ne_mem_upper, ?_⟩
  · intro x hx
    have hx' : x - (p, p + (q : ℤ)) ∈ (mixFoldMark E q p).W := mem_translate.mp hx
    have := (Finset.mem_filter.mp hx').2
    rw [sub_add_cancel] at this
    exact this
  · refine ⟨fun hc => by simp [mixFoldMark] at hc, fun hc => by simp [mixFoldMark] at hc,
      fun hc => by simp [mixFoldMark] at hc, fun _ => ⟨h.lowerV, h.upperH⟩⟩

theorem wellFormed (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).IsWellFormed :=
  ⟨h.conn, Or.inr h.nonemptyMark⟩

theorem narrow (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).IsNarrow := by
  unfold MarkedInner.IsNarrow
  rw [h.width_eq, period_eq]
  exact ⟨by positivity, by exact_mod_cast h.hwq⟩

theorem maximal (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).IsMaximal := by
  apply MarkedInner.IsMaximalAtDisplacement.isMaximal h.conn h.nonemptyMark
  intro W' hW' hlt hsk hc hsub
  apply hlt.2
  intro x hx
  have hxE : x ∈ E := Finset.mem_powerset.mp hW' hx
  have hxv : x + (p, p + (q : ℤ)) ∈ E := by
    apply hsub
    rw [mem_translate]
    have e : x + (p, p + (q : ℤ)) - (mixFoldMark E q p).v = x := by simp [mixFoldMark]
    rw [e]; exact hx
  exact Finset.mem_filter.mpr ⟨hxE, hxv⟩

theorem removals (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).RemovalsConnected :=
  ⟨h.removals_W, h.removals_upper⟩

/-- The hatted middle lies strictly between the private diagonals `w` and `q - 1`. -/
theorem thin (h : MixFoldDiag E q w p s t) {x : ℤ × ℤ} (hx : x ∈ (mixFoldMark E q p).middle)
    (hx' : x + eCell ∈ (mixFoldMark E q p).middle) :
    (w : ℤ) + 1 ≤ content x ∧ content x ≤ (q : ℤ) - 2 := by
  have hq := h.hwq
  have hc : content (x + eCell) = content x := MarkedInner.content_eCell_add x
  rw [h.mem_middle] at hx hx'
  rw [hc] at hx'
  obtain ⟨hxE, hxA, hxB⟩ := hx
  obtain ⟨hxE', hxA', hxB'⟩ := hx'
  have hxe : (x + eCell).1 = x.1 + 1 := by simp [eCell]
  rw [hxe] at hxA' hxB'
  have hcw : ¬ (content x < w) := fun hc' => by
    have := (hxA hc').2; have := (hxA' hc').2; omega
  have hcq : ¬ ((q : ℤ) ≤ content x) := fun hc' => by
    have := (hxB hc').2; have := (hxB' hc').2; omega
  rw [h.mem_iff] at hxE hxE'
  rw [hc] at hxE'
  have hwne : content x ≠ w := fun hc' => by
    have := h.sing_w
    rw [hc'] at hxE hxE'
    omega
  have hqne : content x ≠ (q : ℤ) - 1 := fun hc' => by
    have := h.sing_q
    rw [hc'] at hxE hxE'
    omega
  omega

theorem noHat (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).NoHatAdjacency := by
  rw [MarkedInner.noHatAdjacency_iff_window h.wellFormed h.narrow]
  intro k hk x hx y hy hadj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rw [Finset.mem_filter] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxm : x - k • (mixFoldMark E q p).v ∈ (mixFoldMark E q p).middle := mem_translate.mp hx1
  have hxm' : (x - k • (mixFoldMark E q p).v) + eCell ∈ (mixFoldMark E q p).middle := by
    have := mem_translate.mp hx2
    have e : x + eCell - k • (mixFoldMark E q p).v = (x - k • (mixFoldMark E q p).v) + eCell := by
      abel
    rwa [e] at this
  obtain ⟨t1, t2⟩ := h.thin hxm hxm'
  have hcx : content x = content (x - k • (mixFoldMark E q p).v) + k * q := by
    have : content x = content ((x - k • (mixFoldMark E q p).v) + k • (mixFoldMark E q p).v) := by
      congr 1; abel
    rw [this, content_add, MarkedInner.content_smul]
    have hv : content (mixFoldMark E q p).v = q := period_eq
    rw [hv]
  have hcy : 0 ≤ content y ∧ content y ≤ (w : ℤ) - 1 := by
    unfold MarkedInner.hatMarkWindow at hy
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hy
    rcases hy with ⟨-, hy2⟩ | ⟨hy1, -⟩
    · have := (h.mem_W _).mp hy2
      rw [MarkedInner.content_eCell_add] at this
      omega
    · have := (h.mem_W _).mp hy1
      omega
  have := content_adj hadj
  rcases hk with rfl | rfl
  · omega
  · omega

theorem phases (h : MixFoldDiag E q w p s t) : (mixFoldMark E q p).IsPhases s t := by
  have hts := h.hts
  have hsw := h.hsw
  have ht0 := h.ht0
  have hq := h.hwq
  have hw : (mixFoldMark E q p).widthZ = w := by
    unfold MarkedInner.widthZ; rw [h.width_eq]
  refine ⟨by omega, by omega, ht0, by omega, ?_, ?_⟩
  · intro a h0 h1
    rw [hw] at h1
    have hse := h.se a h0 (by omega)
    have htl := h.tails a h0 (by omega)
    unfold MarkedInner.TailLower MarkedInner.dLo MarkedInner.dHi MarkedInner.lo MarkedInner.hi
    have e1 : (mixFoldMark E q p).period = q := period_eq
    have e2 : (mixFoldMark E q p).rowShift = p := rfl
    have e3 : minContent (mixFoldMark E q p).E = 0 := h.min0
    simp only [e1, e2, e3, zero_add]
    have e4 : (mixFoldMark E q p).E = E := rfl
    rw [e4]
    split_ifs at htl <;> omega
  · intro a h0 h1
    rw [hw] at h1
    have hse := h.se a h0 (by omega)
    have htl := h.tails a h0 (by omega)
    unfold MarkedInner.TailUpper MarkedInner.dLo MarkedInner.dHi MarkedInner.lo MarkedInner.hi
    have e1 : (mixFoldMark E q p).period = q := period_eq
    have e2 : (mixFoldMark E q p).rowShift = p := rfl
    have e3 : minContent (mixFoldMark E q p).E = 0 := h.min0
    simp only [e1, e2, e3, zero_add]
    have e4 : (mixFoldMark E q p).E = E := rfl
    rw [e4]
    split_ifs at htl <;> omega

/-- **The mark of a diagonal datum is legal.** -/
theorem legal (h : MixFoldDiag E q w p s t) :
    (mixFoldMark E q p).IsLegalNonempty ∧ (mixFoldMark E q p).IsPhases s t :=
  ⟨⟨⟨h.wellFormed, h.maximal, h.narrow, h.removals, h.noHat⟩, ⟨sw E, h.sw_mem_W⟩⟩, h.phases⟩

end MixFoldDiag

end SkewGluing
