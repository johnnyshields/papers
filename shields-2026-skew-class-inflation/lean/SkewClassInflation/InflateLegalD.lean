/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalDiag
import SkewClassInflation.InflateLegalExtractD
import SkewClassInflation.InflateLegalPhases
import SkewClassInflation.InflateLegalA

/-!
# Inflation of a legal case-(d) mark

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`, case (d),
\(0<w<q-1\).  Under the two private pinches, the inflated mark of a legal case-(d) mark is again
legal, of the same period, width \(w+1\) and the same phases \((\tau,\sigma)\).  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

variable {ω : MarkedInner}

theorem diagShape_of_mixFold {E : Diagram} {q w : ℕ} {p s t : ℤ} (h : MixFoldDiag E q w p s t) :
    DiagShape 0 ((q : ℤ) + w - 1) (diagLo E) (diagHi E) := by
  have hq := h.hwq
  have hw := h.hw
  refine ⟨by omega, fun k h0 h1 => h.lo_le_hi h0 h1, fun k h0 h1 => (h.bits (by omega) h1).1,
    fun k h0 h1 => (h.bits (by omega) h1).2, h.sing_first, h.sing_last⟩

theorem mixFoldDiag_inflate {E E' : Diagram} {q w : ℕ} {p s t : ℤ}
    (h : MixFoldDiag E q w p s t) (hE' : DiagSet E' 0 ((q : ℤ) + w)
      (loI ((q : ℤ) + w - 1) (diagLo E)) (hiI (diagHi E)))
    (hw1 : (w : ℤ) + 1 < q) (X1 : diagLo E ((q : ℤ) + w - 1) = diagLo E w + p + 1)
    (X2 : diagHi E ((q : ℤ) - 1) = diagHi E q) (h1 : diagLo E ((w : ℤ) + 1) = diagLo E w)
    (h2 : diagHi E ((q : ℤ) - 2) = diagHi E ((q : ℤ) - 1)) :
    MixFoldDiag E' q (w + 1) p s t := by
  have hq := h.hwq
  have hw := h.hw
  have hts := h.hts
  have hsw := h.hsw
  have ht0 := h.ht0
  have sh := diagShape_of_mixFold h
  have sh' := diagShape_inflate sh
  rw [show (q : ℤ) + w - 1 + 1 = (q : ℤ) + w by ring] at sh'
  have hLo : ∀ k, 0 ≤ k → k ≤ (q : ℤ) + w → diagLo E' k = loI ((q : ℤ) + w - 1) (diagLo E) k :=
    fun k h0 h1 => hE'.diagLo_eq sh' h0 h1
  have hHi : ∀ k, 0 ≤ k → k ≤ (q : ℤ) + w → diagHi E' k = hiI (diagHi E) k :=
    fun k h0 h1 => hE'.diagHi_eq sh' h0 h1
  have hsp := hE'.span_eq sh'
  refine ⟨hE'.isConnectedSkew sh', hE'.minContent_eq sh', ?_, by omega, by omega, ht0, hts,
    by push_cast; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast; omega
  · intro a h0 ha
    push_cast at ha
    rw [hHi _ (by omega) (by omega), hHi _ (by omega) (by omega), hiI_of_pos (by omega)]
    by_cases ha0 : a = 0
    · subst ha0
      have := h.se 0 le_rfl (by omega)
      rw [hiI_zero]
      simp only [zero_add] at this ⊢
      omega
    · rw [hiI_of_pos (by omega)]
      have := h.se (a - 1) (by omega) (by omega)
      rw [show a - 1 + q = a + q - 1 by ring] at this
      exact this
  · intro a h0 ha
    push_cast at ha
    by_cases haw : a < w
    · have := h.tails a h0 haw
      rw [hLo _ (by omega) (by omega), hLo _ (by omega) (by omega), loI_of_le (by omega),
        loI_of_le (by omega)]
      rw [show a + (q : ℤ) = a + q from rfl] at this
      exact this
    · obtain rfl : a = w := by omega
      have e1 : (w : ℤ) + q = (q : ℤ) + w - 1 + 1 := by ring
      rw [e1, hLo _ (by omega) (by omega), hLo _ (by omega) (by omega), loI_succ,
        loI_of_le (by omega)]
      simp only [show ¬ ((w : ℤ) < t) by omega, show ¬ ((w : ℤ) < s) by omega, ite_false]
      omega
  · rw [hLo _ (by omega) (by omega), hHi _ (by omega) (by omega), loI_of_le (by omega),
      hiI_of_pos (by omega)]
    push_cast
    simp only [add_sub_cancel_right]
    rw [h1]
    exact h.sing_w
  · rw [hLo _ (by omega) (by omega), hHi _ (by omega) (by omega), loI_of_le (by omega),
      hiI_of_pos (by omega), show (q : ℤ) - 1 - 1 = q - 2 by ring, h2]
    exact h.sing_q
  · rw [hLo _ (by omega) (by omega), hLo _ (by omega) (by omega), loI_of_le (by omega),
      loI_of_le (by omega)]
    exact h.capA
  · intro ht
    rw [hHi _ (by omega) (by omega), hHi _ (by omega) (by omega), hiI_of_pos (by omega),
      hiI_of_pos (by omega), show (q : ℤ) - 1 - 1 = q - 2 by ring, h2]
  · intro ht
    rw [hLo _ (by omega) (by omega), hLo _ (by omega) (by omega), loI_of_le (by omega),
      loI_of_le (by omega)]
    exact h.capH1 ht

theorem diagSet_diag {S : Diagram} {k₀ k₁ : ℤ} {lo hi : ℤ → ℤ} (h : DiagSet S k₀ k₁ lo hi)
    (hs : DiagShape k₀ k₁ lo hi) : DiagSet S k₀ k₁ (diagLo S) (diagHi S) := by
  intro i k
  rw [h i k]
  by_cases hk : k₀ ≤ k ∧ k ≤ k₁
  · rw [h.diagLo_eq hs hk.1 hk.2, h.diagHi_eq hs hk.1 hk.2]
  · constructor
    · intro hh; exact absurd ⟨hh.1, hh.2.1⟩ hk
    · intro hh; exact absurd ⟨hh.1, hh.2.1⟩ hk

/-- The lower copy of the inflated case-(d) mark is the inflation of the lower copy. -/
theorem inflate_W_d {E E' : Diagram} {q w : ℕ} {p s t : ℤ}
    (h : MixFoldDiag E q w p s t) (h' : MixFoldDiag E' q (w + 1) p s t)
    (hE' : DiagSet E' 0 ((q : ℤ) + w)
      (loI ((q : ℤ) + w - 1) (diagLo E)) (hiI (diagHi E)))
    (X1 : diagLo E ((q : ℤ) + w - 1) = diagLo E w + p + 1) :
    inflateCells (mixFoldMark E q p).W = (mixFoldMark E' q p).W := by
  have hq := h.hwq
  have hw := h.hw
  have hts := h.hts
  have hsw := h.hsw
  have ht0 := h.ht0
  have sh := diagShape_of_mixFold h
  have sh' := diagShape_inflate sh
  rw [show (q : ℤ) + w - 1 + 1 = (q : ℤ) + w by ring] at sh'
  have hLo : ∀ k, 0 ≤ k → k ≤ (q : ℤ) + w → diagLo E' k = loI ((q : ℤ) + w - 1) (diagLo E) k :=
    fun k h0 h1 => hE'.diagLo_eq sh' h0 h1
  have hHi : ∀ k, 0 ≤ k → k ≤ (q : ℤ) + w → diagHi E' k = hiI (diagHi E) k :=
    fun k h0 h1 => hE'.diagHi_eq sh' h0 h1
  ext ⟨i, j⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by ring⟩
  rw [mem_inflateCells, show i + k - 1 = i + (k - 1) by ring, h.mem_W, h.mem_W, h'.mem_W]
  simp only [content, add_sub_cancel_left]
  push_cast
  by_cases hk0 : k < 0
  · constructor <;> intro hh <;> omega
  by_cases hk2 : (w : ℤ) < k
  · constructor <;> intro hh <;> omega
  have ne := sh.ne
  by_cases hk : k = 0
  · subst hk
    rw [hLo _ (by omega) (by omega), hHi _ (by omega) (by omega), loI_of_le (by omega), hiI_zero]
    simp only [show (0 : ℤ) < s by omega, ite_true]
    constructor
    · rintro (hh | hh)
      · omega
      · omega
    · intro hh
      left
      omega
  · rw [hLo _ (by omega) (by omega), hHi _ (by omega) (by omega), loI_of_le (by omega),
      hiI_of_pos (by omega)]
    have b1 := h.bits (k := k) (by omega) (by omega)
    have b2 := h.W_lo_le_hi (k := k - 1) (by omega) (by omega)
    have cA : k = s → diagLo E (k - 1) - diagLo E k = 1 := by
      rintro rfl; exact h.capA
    by_cases hkw : k = w
    · subst hkw
      have tl := h.tails ((w : ℤ) - 1) (by omega) (by omega)
      have e : ((w : ℤ) - 1) + q = (q : ℤ) + w - 1 := by ring
      rw [e] at tl
      constructor
      · rintro (hh | hh)
        · omega
        · split_ifs at hh tl ⊢ <;> omega
      · intro hh
        right
        split_ifs at hh tl ⊢ <;> omega
    · have b3 := h.W_lo_le_hi (k := k) (by omega) (by omega)
      constructor
      · rintro (hh | hh)
        · split_ifs at hh b3 b2 ⊢ <;> omega
        · split_ifs at hh b3 b2 ⊢ <;> omega
      · intro hh
        by_cases hi' : i ≤ diagHi E k
        · left
          refine ⟨by omega, by omega, ?_, hi'⟩
          split_ifs at hh ⊢ <;> omega
        · right
          split_ifs at hh b3 b2 ⊢ <;> omega

theorem caps_d (h : ω.IsLegalNonempty) (hc : ω.case = .d) :
    ω.lo (ω.period + ω.widthZ - 1) = ω.lo ω.widthZ + ω.rowShift + 1 ∧
      ω.hi (ω.period - 1) = ω.hi ω.period := by
  have hpa := h.attach.2.2.2 hc
  have cv := (h.lower_caps_V hpa.1).2.2
  have ch := (h.upper_caps_H hpa.2).2.1
  have hq := h.width_lt_period
  have hw := h.width_pos
  unfold dLo at cv
  refine ⟨?_, ch⟩
  rw [show ω.period + ω.widthZ - 1 = ω.widthZ - 1 + ω.period by ring]
  omega

/-- The inflated normalized legal case-(d) mark is the mark of the inflated diagonal data. -/
theorem inflateMarked_translate_eq_mark_d (h : ω.IsLegalNonempty) (hc : ω.case = .d)
    {s t : ℤ} (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (h1 : ω.lo (ω.widthZ + 1) = ω.lo ω.widthZ)
    (h2 : ω.hi (ω.period - 2) = ω.hi (ω.period - 1)) :
    MixFoldDiag (inflateCells (translate (0, -minContent ω.E) ω.E)) ω.period.toNat
        (ω.width + 1) ω.rowShift s t ∧
      inflateMarked (ω.translate (0, -minContent ω.E)) =
        mixFoldMark (inflateCells (translate (0, -minContent ω.E) ω.E)) ω.period.toNat
          ω.rowShift := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpt := period_toNat h
  have hwz : (ω.width : ℤ) = ω.widthZ := rfl
  have hmd := mixFoldDiag_of_legal h hc hp
  have hG := diagSet_E_of_legal h
  have hsh := diagShape_of_legal h
  have hGd := diagSet_diag hG hsh
  have hLo : ∀ a, 0 ≤ a → a ≤ ω.period + ω.widthZ - 1 →
      diagLo (translate (0, -minContent ω.E) ω.E) a = ω.lo a := fun a h0 h1 =>
    hG.diagLo_eq hsh h0 h1
  have hHi : ∀ a, 0 ≤ a → a ≤ ω.period + ω.widthZ - 1 →
      diagHi (translate (0, -minContent ω.E) ω.E) a = ω.hi a := fun a h0 h1 =>
    hG.diagHi_eq hsh h0 h1
  have hshd := diagShape_of_mixFold hmd
  rw [hpt, hwz] at hshd
  have hE' := diagSet_inflate hGd hshd
  rw [show ω.period + ω.widthZ - 1 + 1 = ω.period + ω.widthZ by ring] at hE'
  have hcaps := caps_d h hc
  have hE'q : DiagSet (inflateCells (translate (0, -minContent ω.E) ω.E)) 0
      ((ω.period.toNat : ℤ) + ω.width)
      (loI ((ω.period.toNat : ℤ) + ω.width - 1) (diagLo (translate (0, -minContent ω.E) ω.E)))
      (hiI (diagHi (translate (0, -minContent ω.E) ω.E))) := by
    rw [hpt, hwz]; exact hE'
  have X1 : diagLo (translate (0, -minContent ω.E) ω.E) ((ω.period.toNat : ℤ) + ω.width - 1) =
      diagLo (translate (0, -minContent ω.E) ω.E) ω.width + ω.rowShift + 1 := by
    rw [hpt, hwz, hLo _ (by omega) (by omega), hLo _ (by omega) (by omega)]
    exact hcaps.1
  have hmd' := mixFoldDiag_inflate hmd hE'q (by push_cast; omega) X1
    (by rw [hpt, hHi _ (by omega) (by omega), hHi _ (by omega) (by omega)]; exact hcaps.2)
    (by push_cast; rw [hwz, hLo _ (by omega) (by omega), hLo _ (by omega) (by omega)]; exact h1)
    (by rw [hpt, hHi _ (by omega) (by omega), hHi _ (by omega) (by omega)]; exact h2)
  refine ⟨hmd', ?_⟩
  have hWeq := inflate_W_d hmd hmd' hE'q X1
  refine MarkedInner.mk.injEq .. |>.mpr ⟨rfl, ?_, ?_, hc⟩
  · change inflateCells (translate (0, -minContent ω.E) ω.W) = (mixFoldMark _ _ _).W
    rw [← hWeq]
    congr 1
    ext x
    unfold mixFoldMark
    rw [mem_translate, h.1.W_eq_fullIntersection h.2]
    simp only [fullIntersection, Finset.mem_filter, mem_translate]
    have e : x + (ω.rowShift, ω.rowShift + ((ω.period.toNat : ℕ) : ℤ)) - (0, -minContent ω.E) =
        x - (0, -minContent ω.E) + ω.v := by
      rw [ω.v_eq, hpt]; ext <;> simp <;> ring
    rw [e]
  · change ω.v = (ω.rowShift, ω.rowShift + ((ω.period.toNat : ℕ) : ℤ))
    rw [hpt]; exact ω.v_eq

/-- **Inflation of a legal case-(d) mark.**  If the two private pinches hold and
\(w+1<q\), the inflated mark is a legal case-(d) mark of the same period and phases and of
width \(w+1\). -/
theorem inflate_isLegal_d (h : ω.IsLegalNonempty) (hc : ω.case = .d) {s t : ℤ}
    (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (h1 : ω.lo (ω.widthZ + 1) = ω.lo ω.widthZ)
    (h2 : ω.hi (ω.period - 2) = ω.hi (ω.period - 1)) :
    (inflateMarked ω).IsLegal ∧ (inflateMarked ω).IsPhases s t ∧
      (inflateMarked ω).widthZ = ω.widthZ + 1 ∧ (inflateMarked ω).period = ω.period ∧
      (inflateMarked ω).case = .d := by
  obtain ⟨hmd', heq⟩ := inflateMarked_translate_eq_mark_d h hc hp hw1 h1 h2
  rw [inflateMarked_translate] at heq
  obtain ⟨hleg, hph⟩ := hmd'.legal
  rw [← heq] at hleg hph
  have hleg' : (inflateMarked ω).IsLegal := (isLegal_translate_iff _).mp hleg.1
  have hne : (inflateMarked ω).IsLegalNonempty := ⟨hleg', inflateMarked_W_nonempty h.2⟩
  refine ⟨hleg', ?_, ?_, rfl, hc⟩
  · rw [← isPhases_translate_iff hne (0, -minContent ω.E)]
    exact hph
  · have := hmd'.width_eq
    rw [← heq] at this
    unfold MarkedInner.widthZ
    rw [← width_translate (0, -minContent ω.E) (inflateMarked ω), this]
    push_cast
    rfl

end SkewClassInflation
