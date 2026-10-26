-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/Local/Statements.lean
import SkewGluing.Local.Injective

/-!
# Statements of `lem:gluing-local`

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-local`).

This file states assertions (1) and (2) of the lemma in set-level form and records the meaning of
the tail predicates used in the proofs: a lower (upper) marked residue `a` carries a middle tail
exactly when the middle has a cell on the content `c₀ + a` (`c₀ + q + a`).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner}

theorem IsLegalNonempty.tailLower_iff_middle (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) : ω.TailLower a ↔ ∃ r, ω.cell a r ∈ ω.middle := by
  have hq := h.width_lt_period
  constructor
  · intro ht
    obtain ⟨r, hr⟩ := h.exists_tail_cell h0 h1 ht
    exact ⟨r, (h.mem_middle_lt (by omega)).mpr (Finset.mem_sdiff.mp hr)⟩
  · rintro ⟨r, hr⟩
    exact h.tail_of_cell (r := r) h0 h1
      (Finset.mem_sdiff.mpr ⟨(h.mem_middle.mp hr).1, (h.mem_middle.mp hr).2.1⟩)

theorem IsLegalNonempty.tailUpper_iff_middle (h : ω.IsLegalNonempty) {a : ℤ} (h0 : 0 ≤ a)
    (h1 : a ≤ ω.widthZ - 1) :
    ω.TailUpper a ↔ ∃ r, ω.cell (a + ω.period) r ∈ ω.middle := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  constructor
  · intro ht
    have hl := h.lo_le_hi (a := a + ω.period) (by omega) (by omega)
    unfold TailUpper dLo dHi at ht
    by_cases hd : ω.lo (a + ω.period) - ω.rowShift - ω.lo a < 0
    · exact ⟨ω.lo (a + ω.period), by rw [h.mem_middle_upper h0 h1]; omega⟩
    · exact ⟨ω.hi (a + ω.period), by rw [h.mem_middle_upper h0 h1]; omega⟩
  · rintro ⟨r, hr⟩
    rw [h.mem_middle_upper h0 h1] at hr
    unfold TailUpper dLo dHi
    omega

/-- **`lem:gluing-local` (1).**  For a legal mark with a nonempty copy: the copies are the full
intersection `E ∩ (E - v)`; the middle has at most one cell on each marked diagonal (both copies);
and the private diagonals `w` and `q - 1` of `E` are singletons. -/
theorem IsLegal.gluing_local_one (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ω.W = ω.fullIntersection ∧
    (∀ x ∈ ω.middle, ∀ y ∈ ω.middle, content x = content y →
      (content x ≤ minContent ω.E + ω.widthZ - 1 ∨ minContent ω.E + ω.period ≤ content x) →
        x = y) ∧
    diagLo ω.E (minContent ω.E + ω.widthZ) = diagHi ω.E (minContent ω.E + ω.widthZ) ∧
    diagLo ω.E (minContent ω.E + (ω.period - 1)) = diagHi ω.E (minContent ω.E + (ω.period - 1)) :=
  have hl : ω.IsLegalNonempty := ⟨h, hW⟩
  ⟨h.W_eq_fullIntersection hW, fun _ hx _ hy hc hm => hl.middle_thin hx hy hc hm,
    hl.lo_w_eq_hi_w, hl.lo_pred_period_eq_hi⟩

/-- **`lem:gluing-local` (2).**  The middle occupies the contents `[c₀ + s, c₀ + q + t - 1]` with
`1 ≤ s ≤ w` and `0 ≤ t < w`: the lower tail lives on the marked residues `[s, w - 1]` and the
upper tail on `[0, t - 1]` (a residue `a` carries a lower, resp. upper, tail exactly when the
middle has a cell on the content `c₀ + a`, resp. `c₀ + q + a`).  For mixed marks `t < s`, so the
residue `s - 1` meets neither tail; in case (d) both copies are southeast-justified and in case (c)
northwest-justified. -/
theorem IsLegal.gluing_local_two (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    ∃ s t : ℤ, 1 ≤ s ∧ s ≤ ω.widthZ ∧ 0 ≤ t ∧ t < ω.widthZ ∧
      contents ω.middle = Finset.Icc (minContent ω.E + s) (minContent ω.E + ω.period + t - 1) ∧
      (∀ a, 0 ≤ a → a ≤ ω.widthZ - 1 →
        ((∃ r, ω.cell a r ∈ ω.middle) ↔ s ≤ a) ∧
        ((∃ r, ω.cell (a + ω.period) r ∈ ω.middle) ↔ a < t)) ∧
      (ω.case.IsMixed → t < s ∧ 0 ≤ s - 1 ∧ t ≤ s - 1 ∧ s - 1 ≤ ω.widthZ - 1) ∧
      (ω.case = .d → ω.SEJustified) ∧ (ω.case = .c → ω.NWJustified) := by
  have hl : ω.IsLegalNonempty := ⟨h, hW⟩
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  refine ⟨s, t, hs1, hs2, ht1, ht2, hl.contents_middle ⟨hs1, hs2, ht1, ht2, hS, hT⟩, ?_, ?_,
    fun hc => hl.seJustified hc, fun hc => hl.nwJustified hc⟩
  · intro a h0 h1
    exact ⟨(hl.tailLower_iff_middle h0 h1).symm.trans (hS a h0 h1),
      (hl.tailUpper_iff_middle h0 h1).symm.trans (hT a h0 h1)⟩
  · intro hmix
    have := hl.phases_lt hmix ⟨hs1, hs2, ht1, ht2, hS, hT⟩
    exact ⟨this, by omega, by omega, by omega⟩

end MarkedInner

end SkewGluing
