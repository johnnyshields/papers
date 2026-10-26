/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/EdgeRibbon/Model.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Ribbons
import SkewMarkedFactor.Gluing.Local.Assemble

/-!
# The northwest border of a composite, as a periodic word with the outer's bits

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `eq:gluing-bits`): the border-word argument behind thesis
Thm. 5.4.1 and Lemmas 5.4.2 and 5.4.5 (`OlsonHarris2024HopfApplications`).

A `BorderModel` records, for a composite `F` of an ordinary mark of case (a) with a connected outer
diagram of first-row function `ℓ`, the first rows of `F` on the diagonal classes
`c₀ + (J q + a)` in terms of `ℓ` and of the first-row function `lo` of the inner diagram, together
with the facts about `lo` that come from legality (`t` is the phase of the upper middle tail).
Then the northwest border of `F` is the word of the key ribbons `lo (t + b)`, `0 ≤ b < q`,
joined by the bits of the outer diagram at the offset `t` (`bitA_cls_t_mid`).  A segment of size
`n q` of the border of `F` that starts after a north step (or at the least content) and ends
before an east step (or at the greatest content) starts at the offset `t` of a block, and the
outer segment is removable on the left from the outer diagram (`BorderModel.removable_iff`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace EdgeRibbon

open scoped Classical

/-! ### Arithmetic of diagonal classes -/

theorem cls_lt_of_lt {q J J' a a' : ℤ} (hq : 0 < q) (ha : a < q) (ha' : 0 ≤ a') (h : J < J') :
    J * q + a < J' * q + a' := by
  have : (J + 1) * q ≤ J' * q := mul_le_mul_of_nonneg_right (by omega) hq.le
  nlinarith

theorem cls_cases {q J J' a a' : ℤ} (hq : 0 < q) (ha0 : 0 ≤ a) (ha' : a' < q)
    (h : J * q + a ≤ J' * q + a') : J < J' ∨ (J = J' ∧ a ≤ a') := by
  rcases lt_trichotomy J J' with hlt | heq | hgt
  · exact Or.inl hlt
  · subst heq; right; exact ⟨rfl, by linarith⟩
  · exfalso
    have := cls_lt_of_lt hq ha' ha0 hgt
    omega

theorem cls_eq {q J J' a a' : ℤ} (hq : 0 < q) (ha0 : 0 ≤ a) (ha : a < q) (ha0' : 0 ≤ a')
    (ha' : a' < q) (h : J * q + a = J' * q + a') : J = J' ∧ a = a' := by
  rcases cls_cases hq ha0 ha' h.le with hlt | ⟨rfl, hle⟩
  · exfalso
    have := cls_lt_of_lt hq ha ha0' hlt
    omega
  · exact ⟨rfl, by linarith⟩

/-! ### The first rows of the composite -/

/-- The first row of the composite on the class `(J, a)`: in the class `a < t`, the cell comes from
the previous copy `J - 1` (on the diagonal `a + q` of the inner diagram) when it exists; otherwise
from the copy `J` (on the diagonal `a`), or, past the last copy, from the copy `M`. -/
def rowF (p : ℤ) (ℓ lo : ℤ → ℤ) (μ M t q J a : ℤ) : ℤ :=
  if a < t ∧ μ ≤ J - 1 ∧ J - 1 ≤ M then (J - 1) * p + ℓ (J - 1) + lo (a + q)
  else if μ ≤ J ∧ J ≤ M then J * p + ℓ J + lo a
  else M * p + ℓ M + lo (a + q)

/-- The data of the border of a composite `F` (see the module docstring).  `ℓ` is the first-row
function of the outer diagram, with contents `μ ≤ j ≤ M`; `lo` that of the inner diagram; `p` the
row shift; `q` the period and `w` the width; `t` the phase. -/
structure BorderModel (F : Diagram) (c₀ q w t μ M p : ℤ) (ℓ lo : ℤ → ℤ)
    (fLo fHi : ℤ → ℤ → ℤ) : Prop where
  cr : ClassRows F c₀ q w μ M fLo fHi
  row : ∀ J a, 0 ≤ a → a < q → ValidClass μ M w J a → fLo J a = rowF p ℓ lo μ M t q J a
  t0 : 0 ≤ t
  tw : t < w ∨ (w = 0 ∧ t = 0)
  lt : ∀ a, 0 ≤ a → a < t → lo (a + q) = p + lo a - 1
  ge : ∀ a, t ≤ a → a < w → lo (a + q) = p + lo a
  bit : ∀ a, 0 ≤ a → a + 1 ≤ q + w - 1 → lo a - lo (a + 1) = 0 ∨ lo a - lo (a + 1) = 1
  capU : lo (q - 1) = p + lo 0
  capL : 0 < w → lo (w - 1) = lo w
  bitC : ∀ J, μ + 1 ≤ J → J ≤ M → ℓ (J - 1) - ℓ J = 0 ∨ ℓ (J - 1) - ℓ J = 1

namespace BorderModel

variable {F : Diagram} {c₀ q w t μ M p : ℤ} {ℓ lo : ℤ → ℤ} {fLo fHi : ℤ → ℤ → ℤ}

theorem t_lt_q (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) : t < q := by
  have := h.cr.hq
  have := h.cr.hwq
  have := h.t0
  rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega

theorem contents_iff (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {k : ℤ} :
    k ∈ contents F ↔ c₀ + μ * q ≤ k ∧ k ≤ c₀ + M * q + q + w - 1 := by
  obtain ⟨J, a, ha0, haq, rfl⟩ := h.cr.decomp k
  rw [h.cr.mem_contents ha0 haq, h.cr.valid_iff ha0 haq]
  omega

theorem minContent_eq (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) :
    minContent F = c₀ + μ * q := by
  have hq := h.cr.hq
  have hmM := h.cr.hmM
  have hw := h.cr.hw
  have hwq := h.cr.hwq
  have := mul_le_mul_of_nonneg_right hmM hq.le
  refine minContent_eq_of (h.contents_iff.mpr ⟨le_rfl, by nlinarith⟩) fun k hk => ?_
  exact (h.contents_iff.mp hk).1

theorem maxContent_eq (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) :
    maxContent F = c₀ + M * q + q + w - 1 := by
  have hq := h.cr.hq
  have hmM := h.cr.hmM
  have hw := h.cr.hw
  have hwq := h.cr.hwq
  have := mul_le_mul_of_nonneg_right hmM hq.le
  refine maxContent_eq_of (h.contents_iff.mpr ⟨by nlinarith, le_rfl⟩) fun k hk => ?_
  exact (h.contents_iff.mp hk).2

/-- The first row on a valid class. -/
theorem diagLo_cls (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < q) (hv : ValidClass μ M w J a) :
    diagLo F (c₀ + (J * q + a)) = rowF p ℓ lo μ M t q J a := by
  rw [h.cr.diagLo_eq ha0 haq hv, h.row J a ha0 haq hv]

theorem bitA_cls_pos (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {J a : ℤ} (ha1 : 1 ≤ a)
    (haq : a < q) (hv : ValidClass μ M w J a) :
    bitA F (c₀ + (J * q + a)) = rowF p ℓ lo μ M t q J (a - 1) - rowF p ℓ lo μ M t q J a := by
  have hv' : ValidClass μ M w J (a - 1) := by unfold ValidClass at hv ⊢; omega
  unfold bitA
  have e : c₀ + (J * q + a) - 1 = c₀ + (J * q + (a - 1)) := by ring
  rw [e, h.diagLo_cls (by omega) (by omega) hv', h.diagLo_cls (by omega) haq hv]

theorem bitA_cls_zero (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {J : ℤ}
    (hv : ValidClass μ M w J 0) (hv' : ValidClass μ M w (J - 1) (q - 1)) :
    bitA F (c₀ + (J * q + 0)) =
      rowF p ℓ lo μ M t q (J - 1) (q - 1) - rowF p ℓ lo μ M t q J 0 := by
  have hq := h.cr.hq
  unfold bitA
  have e : c₀ + (J * q + 0) - 1 = c₀ + ((J - 1) * q + (q - 1)) := by ring
  rw [e, h.diagLo_cls (by omega) (by omega) hv', h.diagLo_cls (le_refl _) hq hv]

/-! ### Facts about the inner first-row function -/

theorem E1 (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) : lo (t + q - 1) = p + lo t := by
  have hq := h.cr.hq
  have ht0 := h.t0
  rcases h.tw with htw | ⟨hw0, ht⟩
  · by_cases ht1 : t = 0
    · subst ht1
      have := h.capU
      simpa using this
    · have a1 := h.lt (t - 1) (by omega) (by omega)
      have a2 := h.ge t le_rfl htw
      have a3 := h.bit (t - 1) (by omega) (by omega)
      have a4 := h.bit (t + q - 1) (by omega) (by omega)
      have e1 : t - 1 + q = t + q - 1 := by ring
      have e2 : t - 1 + 1 = t := by ring
      have e3 : t + q - 1 + 1 = t + q := by ring
      rw [e1] at a1
      rw [e2] at a3
      rw [e3] at a4
      omega
  · subst ht
    have := h.capU
    simpa using this

theorem E3 (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) (ht1 : 1 ≤ t) :
    lo (t - 1) - lo t = 1 := by
  have hq := h.cr.hq
  have htw : t < w := by rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega
  have a1 := h.lt (t - 1) (by omega) (by omega)
  have a2 := h.ge t le_rfl htw
  have a3 := h.bit (t - 1) (by omega) (by omega)
  have a4 := h.bit (t + q - 1) (by omega) (by omega)
  have e1 : t - 1 + q = t + q - 1 := by ring
  have e2 : t - 1 + 1 = t := by ring
  have e3 : t + q - 1 + 1 = t + q := by ring
  rw [e1] at a1
  rw [e2] at a3
  rw [e3] at a4
  omega

theorem E4 (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) (htw : t < w) :
    lo (t + q - 1) - lo (t + q) = 0 := by
  have a2 := h.ge t le_rfl htw
  have := h.E1
  omega

theorem E5 (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) (ht1 : 1 ≤ t) :
    lo (q - 1) - lo q = 1 := by
  have htw : t < w := by rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega
  have a1 := h.lt 0 le_rfl (by omega)
  have := h.capU
  simp only [zero_add] at a1
  omega

/-! ### The bits of the composite -/

/-- The bit of the border of the composite at a class `a ≠ t`: independent of the block. -/
def Qval (lo : ℤ → ℤ) (t a : ℤ) (q : ℤ) : ℤ :=
  if a < t then lo (a - 1 + q) - lo (a + q) else lo (a - 1) - lo a

theorem bitA_cls_ne_t (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < q) (hv : ValidClass μ M w J a) (hat : a ≠ t) (hmin : ¬ (J = μ ∧ a = 0)) :
    bitA F (c₀ + (J * q + a)) = Qval lo t a q := by
  have hq := h.cr.hq
  have hmM := h.cr.hmM
  have htq := h.t_lt_q
  have ht0 := h.t0
  have hp1 : (J - 1) * p = J * p - p := by ring
  by_cases ha1 : 1 ≤ a
  · rw [h.bitA_cls_pos ha1 haq hv]
    unfold rowF Qval
    unfold ValidClass at hv
    rcases lt_or_gt_of_ne hat with hlt | hgt
    · have l1 := h.lt (a - 1) (by omega) (by omega)
      have l2 := h.lt a (by omega) hlt
      have hw : t < w := by rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega
      split_ifs <;> omega
    · by_cases haw : a < w
      · have g1 := h.ge (a - 1) (by omega) (by omega)
        have g2 := h.ge a (by omega) haw
        split_ifs <;> omega
      · split_ifs <;> omega
  · have ha' : a = 0 := by omega
    subst ha'
    have ht1 : 1 ≤ t := by omega
    have hJ : μ + 1 ≤ J := by unfold ValidClass at hv; omega
    have hv' : ValidClass μ M w (J - 1) (q - 1) := by unfold ValidClass at hv ⊢; omega
    rw [h.bitA_cls_zero hv hv']
    unfold rowF Qval
    unfold ValidClass at hv
    have e1 : (0 : ℤ) - 1 + q = q - 1 := by ring
    have e2 : (0 : ℤ) + q = q := by ring
    have := h.E5 ht1
    simp only [e1, e2]
    split_ifs <;> omega

/-- At the offset `t` the bit of the border of the composite is the bit of the outer diagram. -/
theorem bitA_cls_t_mid (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {J : ℤ} (hJ1 : μ + 1 ≤ J)
    (hJ2 : J ≤ M) : bitA F (c₀ + (J * q + t)) = ℓ (J - 1) - ℓ J := by
  have hq := h.cr.hq
  have htq := h.t_lt_q
  have ht0 := h.t0
  have hp1 : (J - 1) * p = J * p - p := by ring
  have hv : ValidClass μ M w J t := Or.inl ⟨by omega, hJ2⟩
  by_cases ht1 : 1 ≤ t
  · rw [h.bitA_cls_pos ht1 htq hv]
    unfold rowF
    have := h.E1
    have e1 : t - 1 + q = t + q - 1 := by ring
    rw [e1]
    split_ifs <;> omega
  · have ht' : t = 0 := by omega
    subst ht'
    have hv' : ValidClass μ M w (J - 1) (q - 1) := Or.inl ⟨by omega, by omega⟩
    rw [h.bitA_cls_zero hv hv']
    unfold rowF
    have := h.capU
    split_ifs <;> omega

/-- At the least block, the bit at the offset `t ≥ 1` is a north step. -/
theorem bitA_cls_t_first (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) (ht1 : 1 ≤ t) :
    bitA F (c₀ + (μ * q + t)) = 1 := by
  have hq := h.cr.hq
  have hmM := h.cr.hmM
  have htq := h.t_lt_q
  have hv : ValidClass μ M w μ t := Or.inl ⟨le_rfl, hmM⟩
  rw [h.bitA_cls_pos ht1 htq hv]
  unfold rowF
  have := h.E3 ht1
  split_ifs <;> omega

/-- Past the last block the bit at the offset `t` is an east step. -/
theorem bitA_cls_t_last (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) (htw : t < w) :
    bitA F (c₀ + ((M + 1) * q + t)) = 0 := by
  have hq := h.cr.hq
  have hmM := h.cr.hmM
  have htq := h.t_lt_q
  have ht0 := h.t0
  have hv : ValidClass μ M w (M + 1) t := Or.inr ⟨rfl, htw⟩
  by_cases ht1 : 1 ≤ t
  · rw [h.bitA_cls_pos ht1 htq hv]
    unfold rowF
    have := h.E4 htw
    have e1 : t - 1 + q = t + q - 1 := by ring
    rw [e1]
    simp only [add_sub_cancel_right]
    split_ifs <;> omega
  · have ht' : t = 0 := by omega
    subst ht'
    have hv' : ValidClass μ M w (M + 1 - 1) (q - 1) := Or.inl ⟨by omega, by omega⟩
    rw [h.bitA_cls_zero hv hv']
    unfold rowF
    have := h.capU
    have g := h.ge 0 le_rfl htw
    simp only [add_sub_cancel_right]
    split_ifs <;> omega

/-! ### Removable segments of the border of the composite -/

theorem valid_of_bounds (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < q) (h1 : μ * q ≤ J * q + a) (h2 : J * q + a ≤ M * q + q + w - 1) :
    ValidClass μ M w J a :=
  (h.cr.valid_iff ha0 haq).mpr ⟨h1, h2⟩

/-- **Removable segments of the border of the composite** (thesis Lemma 5.4.2 for a ribbon of size
`n q`): a segment of the border of `F` on the `n q` contents from `k₀` that starts after a north
step (or at the least content) and ends before an east step (or at the greatest content) starts at
the offset `t` of a block, and the corresponding outer segment is removable on the left from the
outer diagram. -/
theorem removable_iff (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {n : ℤ} (hn : 0 < n)
    {k₀ : ℤ} :
    (minContent F ≤ k₀ ∧ k₀ + n * q - 1 ≤ maxContent F ∧
      (k₀ = minContent F ∨ bitA F k₀ = 1) ∧
      (k₀ + n * q - 1 = maxContent F ∨ bitA F (k₀ + n * q) = 0)) ↔
    ∃ j₀, μ ≤ j₀ ∧ j₀ + n - 1 ≤ M ∧ (j₀ = μ ∨ ℓ (j₀ - 1) - ℓ j₀ = 1) ∧
      (j₀ + n - 1 = M ∨ ℓ (j₀ + n - 1) - ℓ (j₀ + n) = 0) ∧ k₀ = c₀ + t + j₀ * q := by
  have hq := h.cr.hq
  have hw0 := h.cr.hw
  have hwq := h.cr.hwq
  have hmM := h.cr.hmM
  have htq := h.t_lt_q
  have ht0 := h.t0
  have hnq : q ≤ n * q := by nlinarith
  rw [h.minContent_eq, h.maxContent_eq]
  constructor
  · rintro ⟨hk1, hk2, hs, he⟩
    obtain ⟨J₀, a₀, ha0, haq, rfl⟩ := h.cr.decomp k₀
    have e1 : c₀ + (J₀ * q + a₀) + n * q = c₀ + ((J₀ + n) * q + a₀) := by ring
    have e2 : (J₀ + n) * q = J₀ * q + n * q := by ring
    have e3 : (M + 1) * q = M * q + q := by ring
    have hv0 : ValidClass μ M w J₀ a₀ :=
      h.valid_of_bounds ha0 haq (by omega) (by omega)
    have hJ₀μ : μ ≤ J₀ := by unfold ValidClass at hv0; omega
    have hend : J₀ + n < M + 1 ∨ (J₀ + n = M + 1 ∧ a₀ ≤ w) :=
      cls_cases hq ha0 hwq (by rw [e2, e3]; omega)
    -- the end of the segment: either at the greatest content, or a valid class follows
    have hend1 : c₀ + (J₀ * q + a₀) + n * q - 1 = c₀ + M * q + q + w - 1 →
        J₀ + n = M + 1 ∧ a₀ = w := fun he1 =>
      cls_eq hq ha0 haq hw0 hwq (by rw [e2, e3]; omega)
    have hend2 : c₀ + (J₀ * q + a₀) + n * q - 1 ≠ c₀ + M * q + q + w - 1 →
        ValidClass μ M w (J₀ + n) a₀ := fun he1 =>
      h.valid_of_bounds ha0 haq (by omega) (by omega)
    have hstart1 : c₀ + (J₀ * q + a₀) = c₀ + μ * q → J₀ = μ ∧ a₀ = 0 := fun hs1 =>
      cls_eq hq ha0 haq le_rfl hq (by omega)
    by_cases hat : a₀ = t
    · subst hat
      have hJ₀M : J₀ + n - 1 ≤ M := by omega
      refine ⟨J₀, hJ₀μ, hJ₀M, ?_, ?_, by ring⟩
      · rcases hs with hs | hs
        · exact Or.inl (hstart1 hs).1
        · by_cases hJ : J₀ = μ
          · exact Or.inl hJ
          · right
            have := h.bitA_cls_t_mid (J := J₀) (by omega) (by omega)
            omega
      · by_cases hJ : J₀ + n - 1 = M
        · exact Or.inl hJ
        · right
          have hne : c₀ + (J₀ * q + a₀) + n * q - 1 ≠ c₀ + M * q + q + w - 1 := by
            intro he1
            have := hend1 he1
            omega
          have hb := he.resolve_left hne
          rw [e1] at hb
          have := h.bitA_cls_t_mid (J := J₀ + n) (by omega) (by omega)
          rw [this] at hb
          have e4 : J₀ + n - 1 = J₀ + n - 1 := rfl
          omega
    · exfalso
      by_cases hmin : J₀ = μ ∧ a₀ = 0
      · obtain ⟨hJ, ha⟩ := hmin
        subst hJ ha
        have ht1 : 1 ≤ t := by omega
        rcases he with he | he
        · have := hend1 he
          have hw' : w = 0 := by omega
          rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega
        · have hne : c₀ + (J₀ * q + 0) + n * q - 1 ≠ c₀ + M * q + q + w - 1 := by
            intro he1
            have := hend1 he1
            have hw' : w = 0 := by omega
            rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega
          have hv := hend2 hne
          rw [e1] at he
          have hb := h.bitA_cls_ne_t (J := J₀ + n) (a := 0) le_rfl hq hv hat
            (by intro hh; omega)
          rw [hb] at he
          have hE5 := h.E5 ht1
          have e5 : (0 : ℤ) - 1 + q = q - 1 := by ring
          have e6 : (0 : ℤ) + q = q := by ring
          have hc : (0 : ℤ) < t := by omega
          unfold Qval at he
          simp only [hc, ite_true, e5, e6] at he
          omega
      · have hs' : bitA F (c₀ + (J₀ * q + a₀)) = 1 := by
          rcases hs with hs | hs
          · exact absurd (hstart1 hs) hmin
          · exact hs
        rw [h.bitA_cls_ne_t ha0 haq hv0 hat hmin] at hs'
        rcases he with he | he
        · have := hend1 he
          obtain ⟨-, hw'⟩ := this
          subst hw'
          have hwt : t < a₀ := by
            rcases h.tw with h1 | ⟨h1, h2⟩
            · omega
            · omega
          have hcap := h.capL (by omega)
          unfold Qval at hs'
          split_ifs at hs' <;> omega
        · have hne : c₀ + (J₀ * q + a₀) + n * q - 1 ≠ c₀ + M * q + q + w - 1 := by
            intro he1
            have := hend1 he1
            rcases lt_or_gt_of_ne hat with hl | hg
            · have hcap : a₀ = w := this.2
              rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega
            · have hcap := h.capL (by have := this.2; omega)
              have h2 : a₀ = w := this.2
              subst h2
              unfold Qval at hs'
              split_ifs at hs' <;> omega
          have hv := hend2 hne
          rw [e1] at he
          have hb := h.bitA_cls_ne_t (J := J₀ + n) ha0 haq hv hat
            (by intro hh; omega)
          rw [hb] at he
          unfold Qval at he hs'
          split_ifs at he hs' <;> omega
  · rintro ⟨j₀, hj1, hj2, hs, he, rfl⟩
    have e2 : (j₀ + n) * q = j₀ * q + n * q := by ring
    have e3 : (M + 1) * q = M * q + q := by ring
    have hmq : μ * q ≤ j₀ * q := mul_le_mul_of_nonneg_right hj1 hq.le
    have hjq : (j₀ + n) * q ≤ (M + 1) * q := mul_le_mul_of_nonneg_right (by omega) hq.le
    have htw' : t ≤ w := by rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega
    refine ⟨by omega, by omega, ?_, ?_⟩
    · by_cases hJ : j₀ = μ
      · subst hJ
        by_cases ht1 : 1 ≤ t
        · right
          have := h.bitA_cls_t_first ht1
          have e : c₀ + t + j₀ * q = c₀ + (j₀ * q + t) := by ring
          rw [e]; exact this
        · left
          have : t = 0 := by omega
          subst this
          ring
      · right
        have hb := h.bitA_cls_t_mid (J := j₀) (by omega) (by omega)
        have e : c₀ + t + j₀ * q = c₀ + (j₀ * q + t) := by ring
        rw [e, hb]
        exact hs.resolve_left hJ
    · by_cases hJ : j₀ + n - 1 = M
      · have hM : j₀ + n = M + 1 := by omega
        rcases h.tw with htw | ⟨hw', ht'⟩
        · right
          have hb := h.bitA_cls_t_last htw
          have e : c₀ + t + j₀ * q + n * q = c₀ + ((M + 1) * q + t) := by
            rw [← hM, e2]; ring
          rw [e]; exact hb
        · left
          subst hw' ht'
          rw [e2] at hjq
          have : (j₀ + n) * q = (M + 1) * q := by rw [hM]
          rw [e2, e3] at this
          omega
      · right
        have hb := h.bitA_cls_t_mid (J := j₀ + n) (by omega) (by omega)
        have e : c₀ + t + j₀ * q + n * q = c₀ + ((j₀ + n) * q + t) := by ring
        rw [e, hb]
        have := he.resolve_left hJ
        have e4 : j₀ + n - 1 = j₀ + n - 1 := rfl
        exact this

/-! ### The key ribbons inside the border -/

/-- **The border of the composite is the word of the key ribbons**: on the contents
`c₀ + t + j q + i`, `μ ≤ j ≤ M` and `0 ≤ i < q`, the first row of `F` is the first row `j p + ℓ j`
of the copy `j` plus the first row of the inner diagram on the diagonal `t + i`. -/
theorem diagLo_core (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {j i : ℤ} (hj1 : μ ≤ j)
    (hj2 : j ≤ M) (hi0 : 0 ≤ i) (hiq : i < q) :
    diagLo F (c₀ + t + j * q + i) = j * p + ℓ j + lo (t + i) := by
  have hq := h.cr.hq
  have ht0 := h.t0
  have htq := h.t_lt_q
  by_cases hti : t + i < q
  · have e : c₀ + t + j * q + i = c₀ + (j * q + (t + i)) := by ring
    rw [e, h.diagLo_cls (by omega) hti (Or.inl ⟨hj1, hj2⟩)]
    unfold rowF
    split_ifs <;> omega
  · have e : c₀ + t + j * q + i = c₀ + ((j + 1) * q + (t + i - q)) := by ring
    have ht1 : 1 ≤ t := by omega
    have htw : t < w := by rcases h.tw with h1 | ⟨h1, h2⟩ <;> omega
    have hv : ValidClass μ M w (j + 1) (t + i - q) := by
      unfold ValidClass
      by_cases hjM : j + 1 ≤ M
      · exact Or.inl ⟨by omega, hjM⟩
      · exact Or.inr ⟨by omega, by omega⟩
    rw [e, h.diagLo_cls (by omega) (by omega) hv]
    unfold rowF
    simp only [add_sub_cancel_right, sub_add_cancel]
    split_ifs <;> omega

/-- The height of a ribbon of size `n q` of the border of the composite starting at the offset
`t` of the block `j₀`. -/
theorem diagLo_start_end (h : BorderModel F c₀ q w t μ M p ℓ lo fLo fHi) {j₀ n : ℤ}
    (hj1 : μ ≤ j₀) (hn : 0 < n) (hj2 : j₀ + n - 1 ≤ M) :
    diagLo F (c₀ + t + j₀ * q) - diagLo F (c₀ + t + j₀ * q + n * q - 1) =
      (ℓ j₀ - ℓ (j₀ + n - 1)) - n * p := by
  have hq := h.cr.hq
  have e1 : c₀ + t + j₀ * q = c₀ + t + j₀ * q + 0 := by ring
  have a1 := h.diagLo_core (j := j₀) (i := 0) hj1 (by omega) le_rfl hq
  have a2 := h.diagLo_core (j := j₀ + n - 1) (i := q - 1) (by omega) hj2 (by omega) (by omega)
  have e2 : c₀ + t + (j₀ + n - 1) * q + (q - 1) = c₀ + t + j₀ * q + n * q - 1 := by ring
  rw [e2] at a2
  rw [add_zero] at a1
  have hE1 := h.E1
  have e3 : t + (q - 1) = t + q - 1 := by ring
  rw [e3] at a2
  have e4 : (j₀ + n - 1) * p = j₀ * p + n * p - p := by ring
  have e5 : t + 0 = t := by ring
  rw [e5] at a1
  rw [a1, a2, e4]
  omega

end BorderModel

end EdgeRibbon

end Plan

end SkewMarkedFactor.Gluing
