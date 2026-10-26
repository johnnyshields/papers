/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.MixedBoundary
import SkewMarkedFactor.Gluing.RowInner
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Ribbons

/-!
# The northwest border of a case-(d) row power

The case-(d) analysis in the proof of «Mixed weighted covariance» (`rt:mixed-covariance`) of
`shields-2026-skew-marked-factor.tex`: the northwest border word of
`F_m = Row_m ∘_η E` is periodic with period `p` apart from two defects, and among the
northwest-removable ribbons of size `k p` at most two survive, at the contents
`t` and `(m - k) p + s` measured from the least content.
Contents are measured from `minContent F = minContent E`.
-/

namespace SkewMarkedFactor
open Gluing Gluing.MarkedInner Gluing.Plan

/-- The northwest bit of `F` at the content `c₀ + u`: `ℓ_{c₀+u-1} - ℓ_{c₀+u}`. -/
abbrev nwBit (F : Diagram) (c : ℤ) : ℤ := diagLo F (c - 1) - diagLo F c

section RowPower

variable {η : MarkedInner} {m : ℕ}

theorem rowCells_diagHi {m k : ℤ} (hk : 0 ≤ k) (hk' : k < m) :
    diagHi (rowCells 0 m) k = 0 := by
  apply diagHi_eq_of (l := 0)
  · rw [zero_add]; exact mem_rowCells.mpr ⟨rfl, hk, hk'⟩
  · intro i hi
    have := (mem_rowCells.mp hi).1
    omega

/-- The diagonal `ℓ` of the case-(d) row power on the class `(J, a)`: the periodic part
`J v₁ + ℓ_E(a)`, lowered by one on the residues `a < t` once `J ≥ 1`, and raised by one on the
residues `a ≥ s` of the last band. -/
theorem diagLo_rowPower (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < η.period) (hJ : (0 ≤ J ∧ J ≤ (m : ℤ) - 1) ∨ (J = m ∧ a < η.widthZ)) :
    diagLo (η.compose (rowCells 0 m)) (minContent η.E + (J * η.period + a)) =
      J * η.rowShift + η.lo a - (if 1 ≤ J ∧ a < t then 1 else 0) +
        (if J = m ∧ s ≤ a then 1 else 0) := by
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hmin := minContent_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hmax := maxContent_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hcr := mix_classRows h hD hd hph hlt
  rw [hmin, hmax] at hcr
  have hv : ValidClass 0 ((m : ℤ) - 1) η.widthZ J a := by
    unfold ValidClass; omega
  have hq := h.width_lt_period
  have hw := h.width_pos
  rw [hcr.diagLo_eq ha0 haq hv]
  have hph' := hph
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := hph'
  have hlo : ∀ J', 0 ≤ J' → J' ≤ (m : ℤ) - 1 → η.oRowLo (rowCells 0 m) J' = J' * η.rowShift := by
    intro J' h1 h2
    simp only [oRowLo, hd]
    rw [rowCells_diagHi h1 (by omega), diagLo_rowCells h1 (by omega)]
    ring
  have fa' := fun hw' : a < η.widthZ => d_E_facts h hd hph ha0 (a := a) (by omega)
  by_cases hJ0 : J = 0
  · subst hJ0
    rw [mixLo_P1 (by omega) (by omega), hlo 0 le_rfl (by omega)]
    split_ifs <;> omega
  by_cases hJm : J = m
  · have haw : a < η.widthZ := by omega
    subst hJm
    rw [mixLo_P2 (by omega), hlo (m - 1) (by omega) le_rfl]
    have fa := fa' haw
    simp only [dLo] at fa
    have e : ((m : ℤ) - 1) * η.rowShift = (m : ℤ) * η.rowShift - η.rowShift := by ring
    rw [e]
    split_ifs <;> omega
  have hJ1 : 1 ≤ J ∧ J ≤ (m : ℤ) - 1 := by omega
  by_cases haw : a < η.widthZ
  · rw [mixLo_all0 (by omega) ⟨haw, by omega, by omega⟩ (by
      rw [rowCells_diagHi (by omega) (by omega), rowCells_diagHi (by omega) (by omega)]
      omega), hlo J (by omega) (by omega), hlo (J - 1) (by omega) (by omega)]
    have fa := fa' haw
    simp only [dLo] at fa
    have e : (J - 1) * η.rowShift = J * η.rowShift - η.rowShift := by ring
    rw [e]
    split_ifs <;> omega
  · rw [mixLo_P1 (by omega) (by omega), hlo J (by omega) (by omega)]
    split_ifs <;> omega


/-- The northwest bit of the case-(d) row power at a content with residue `a ≥ 1`. -/
theorem nwBit_rowPower_pos (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {J a : ℤ} (ha1 : 1 ≤ a)
    (haq : a < η.period) (hJ : (0 ≤ J ∧ J ≤ (m : ℤ) - 1) ∨ (J = m ∧ a < η.widthZ)) :
    nwBit (η.compose (rowCells 0 m)) (minContent η.E + (J * η.period + a)) =
      (η.lo (a - 1) - η.lo a) - (if 1 ≤ J ∧ a = t then 1 else 0) -
        (if J = m ∧ a = s then 1 else 0) := by
  have e : minContent η.E + (J * η.period + a) - 1 = minContent η.E + (J * η.period + (a - 1)) := by
    ring
  unfold nwBit
  rw [e, diagLo_rowPower h hd hph hlt hm (by omega) (by omega) (by omega),
    diagLo_rowPower h hd hph hlt hm (by omega) haq hJ]
  split_ifs <;> omega

/-- The northwest bit at the first residue of a band: it is `1` exactly when `t > 0`. -/
theorem nwBit_rowPower_zero (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {J : ℤ} (hJ1 : 1 ≤ J)
    (hJm : J ≤ (m : ℤ)) :
    nwBit (η.compose (rowCells 0 m)) (minContent η.E + J * η.period) =
      if 0 < t then 1 else 0 := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hph' := hph
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := hph'
  have e : minContent η.E + J * η.period - 1 =
      minContent η.E + ((J - 1) * η.period + (η.period - 1)) := by ring
  have e0 : minContent η.E + J * η.period = minContent η.E + (J * η.period + 0) := by ring
  have hc := d_caps h hd
  have hL := hc.2.1
  have hL2 := hc.2.2.2
  simp only [dLo, dHi] at hL hL2
  unfold nwBit
  rw [e, e0, diagLo_rowPower h hd hph hlt hm (by omega) (by omega) (by omega),
    diagLo_rowPower h hd hph hlt hm (by omega) (by omega) (by omega)]
  have hj : (J - 1) * η.rowShift = J * η.rowShift - η.rowShift := by ring
  simp only [zero_add] at hL2
  rw [hj]
  split_ifs <;> omega


private theorem divmod_unique {p J a J' a' : ℤ} (hp : 0 < p) (h1 : 0 ≤ a) (h2 : a < p)
    (h3 : 0 ≤ a') (h4 : a' < p) (h : J * p + a = J' * p + a') : J = J' ∧ a = a' := by
  have hJ : J = J' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · nlinarith
    · nlinarith
  subst hJ
  exact ⟨rfl, by omega⟩

/-- Duplicate-or-horizon: a northwest-removable border segment of `k p` contents in the case-(d)
row power starts at content `t` or at content `(m - k) p + s`, measured from the least content. -/
theorem rowPower_nw_start (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {k : ℕ} (hk : 1 ≤ k) {c0 : ℤ}
    (h0 : minContent η.E ≤ c0)
    (hfin : c0 + (k : ℤ) * η.period - 1 ≤ maxContent (η.compose (rowCells 0 m)))
    (hS : c0 = minContent (η.compose (rowCells 0 m)) ∨
      bitA (η.compose (rowCells 0 m)) c0 = 1)
    (hE : c0 + (k : ℤ) * η.period - 1 = maxContent (η.compose (rowCells 0 m)) ∨
      bitA (η.compose (rowCells 0 m)) (c0 + (k : ℤ) * η.period) = 0) :
    c0 = minContent η.E + t ∨ c0 = minContent η.E + (((m : ℤ) - k) * η.period + s) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpp : 0 < η.period := by omega
  have hl := h.1
  have hph' := hph
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := hph'
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hmin' := minContent_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hmax' := maxContent_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hFmin := hl.minContent_compose hD
  rw [hmin', zero_mul, add_zero] at hFmin
  have hspan := span_compose hD hl
  have hFsp := span_eq_of_isConnectedSkew (hl.isConnectedSkew_compose hD)
  have hsp : (span (rowCells 0 (m : ℤ)) : ℤ) = m := by
    rw [span_rowCells]; omega
  rw [hsp] at hspan
  have hFmax : maxContent (η.compose (rowCells 0 m)) =
      minContent η.E + (m * η.period + η.widthZ - 1) := by
    have : (η.width : ℤ) = η.widthZ := rfl
    omega
  rw [hFmin] at hS
  rw [hFmax] at hE hfin
  obtain ⟨J0, a, ha0, haq, he⟩ : ∃ J a, 0 ≤ a ∧ a < η.period ∧
      c0 = minContent η.E + (J * η.period + a) :=
    ⟨(c0 - minContent η.E) / η.period, (c0 - minContent η.E) % η.period,
      Int.emod_nonneg _ hpp.ne', Int.emod_lt_of_pos _ hpp, by
        have := Int.mul_ediv_add_emod (c0 - minContent η.E) η.period
        have e : (c0 - minContent η.E) / η.period * η.period =
          η.period * ((c0 - minContent η.E) / η.period) := by ring
        omega⟩
  have hJ0 : 0 ≤ J0 := by nlinarith
  have hJk : J0 + k ≤ m := by
    by_contra hcon
    have : ((m : ℤ) + 1) * η.period ≤ (J0 + k) * η.period := by
      apply mul_le_mul_of_nonneg_right _ hpp.le; omega
    nlinarith
  have hJkw : J0 + k = m → a ≤ η.widthZ := by
    intro hh
    have : (J0 + k) * η.period = m * η.period := by rw [hh]
    nlinarith
  have hend : c0 + (k : ℤ) * η.period = minContent η.E + ((J0 + k) * η.period + a) := by
    rw [he]; ring
  by_cases ha : a = 0
  · subst ha
    have hbit0 : ∀ J : ℤ, 1 ≤ J → J ≤ m → bitA (η.compose (rowCells 0 m))
        (minContent η.E + (J * η.period + 0)) = if 0 < t then 1 else 0 := by
      intro J h1 h2
      have := nwBit_rowPower_zero h hd hph hlt hm h1 h2
      rw [add_zero]; exact this
    by_cases hJ : J0 = 0
    · subst hJ
      left
      rw [he]
      have hkp : (k : ℤ) * η.period ≤ m * η.period := by
        apply mul_le_mul_of_nonneg_right _ hpp.le; omega
      rcases hE with hE | hE
      · exfalso; rw [he] at hE; nlinarith
      · rw [hend] at hE
        have := hbit0 (0 + k) (by omega) hJk
        rw [this] at hE
        split_ifs at hE <;> omega
    · exfalso
      have hJ1 : 1 ≤ J0 := by omega
      have hpos : 0 < J0 * η.period := by positivity
      have hkp : ((J0 + k : ℤ)) * η.period ≤ m * η.period := by
        apply mul_le_mul_of_nonneg_right _ hpp.le; omega
      rcases hS with hS | hS
      · rw [he] at hS; omega
      · rw [he] at hS
        have h1 := hbit0 J0 hJ1 (by omega)
        rw [h1] at hS
        rcases hE with hE | hE
        · rw [he] at hE; nlinarith
        · rw [hend] at hE
          have := hbit0 (J0 + k) (by omega) hJk
          rw [this] at hE
          split_ifs at hS hE <;> omega
  · have ha1 : 1 ≤ a := by omega
    have hJm : J0 ≠ m := by omega
    have hJ0p : 0 ≤ J0 * η.period := mul_nonneg hJ0 hpp.le
    have hst := nwBit_rowPower_pos h hd hph hlt hm ha1 haq (J := J0)
      (Or.inl ⟨hJ0, by omega⟩)
    have hS' : nwBit (η.compose (rowCells 0 m)) (minContent η.E + (J0 * η.period + a)) = 1 := by
      rcases hS with hS | hS
      · exfalso; rw [he] at hS; omega
      · rw [he] at hS; exact hS
    rw [hS'] at hst
    by_cases hH : J0 + k = m ∧ a = η.widthZ
    · -- horizon: the segment ends at the last content
      obtain ⟨hH1, hH2⟩ := hH
      have hc := d_caps h hd
      have hL := hc.1.2.2
      have hfa := d_E_facts h hd hph (a := η.widthZ - 1) (by omega) le_rfl
      subst hH2
      have hind : ¬ (1 ≤ J0 ∧ η.widthZ = t) := by omega
      have hind2 : ¬ (J0 = m ∧ η.widthZ = s) := by omega
      simp only [hind, hind2, ite_false] at hst
      have hs : s = η.widthZ := by
        simp only [dLo] at hfa hL
        have := hfa.2.2.2.2.2.1
        by_contra hne
        have h2 : s ≤ η.widthZ - 1 := by omega
        have := this h2
        have e : η.widthZ - 1 + η.period = η.widthZ - 1 + η.period := rfl
        omega
      right
      rw [he, show J0 = (m : ℤ) - k by omega, ← hs]
    · have hvalid : (0 ≤ J0 + k ∧ J0 + k ≤ (m : ℤ) - 1) ∨ (J0 + k = m ∧ a < η.widthZ) := by
        by_cases hh : J0 + k = m
        · right; exact ⟨hh, by have := hJkw hh; omega⟩
        · left; omega
      have hbE := nwBit_rowPower_pos h hd hph hlt hm ha1 haq (J := J0 + k) hvalid
      have hE' : nwBit (η.compose (rowCells 0 m))
          (minContent η.E + ((J0 + k) * η.period + a)) = 0 := by
        rcases hE with hE | hE
        · exfalso
          rw [he] at hE
          have e1 : (J0 + k) * η.period + a = m * η.period + η.widthZ := by
            have : (k : ℤ) * η.period + (J0 * η.period + a) =
              (J0 + k) * η.period + a := by ring
            omega
          obtain ⟨e2, e3⟩ := divmod_unique hpp (by omega) haq (by omega) hq e1
          exact hH ⟨e2, e3⟩
        · rw [hend] at hE; exact hE
      rw [hE'] at hbE
      have key : (J0 = 0 ∧ a = t) ∨ (J0 + k = m ∧ a = s) := by
        split_ifs at hst hbE <;> omega
      rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · left; rw [he, k1, k2]; ring
      · right; rw [he, show J0 = (m : ℤ) - k by omega, k2]


theorem minContent_segment (X : Diagram) (c0 : ℤ) {n : ℕ} (hn : 0 < n) :
    minContent (segment X c0 n) = c0 := by
  apply minContent_eq_of
  · rw [contents_segment]; exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  · intro k hk
    rw [contents_segment, Finset.mem_Ico] at hk
    exact hk.1

/-- The least and greatest contents of the case-(d) row power. -/
theorem rowPower_content_range (h : η.IsLegalNonempty) (hm : 1 ≤ m) :
    minContent (η.compose (rowCells 0 m)) = minContent η.E ∧
      maxContent (η.compose (rowCells 0 m)) =
        minContent η.E + (m * η.period + η.widthZ - 1) := by
  have hl := h.1
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hmin' := minContent_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hFmin := hl.minContent_compose hD
  rw [hmin', zero_mul, add_zero] at hFmin
  have hspan := span_compose hD hl
  have hFsp := span_eq_of_isConnectedSkew (hl.isConnectedSkew_compose hD)
  have hsp : (span (rowCells 0 (m : ℤ)) : ℤ) = m := by
    rw [span_rowCells]; omega
  rw [hsp] at hspan
  refine ⟨hFmin, ?_⟩
  have : (η.width : ℤ) = η.widthZ := rfl
  omega

/-- **The northwest-removable ribbons of `k p` cells of the case-(d) row power.**  Among them
at most two occur, the border segments starting at the contents `t` and `(m - k) p + s`
above the least content. -/
theorem rowPower_leftRibbons_subset (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {k : ℕ} (hk : 1 ≤ k) :
    leftRibbons (η.compose (rowCells 0 m)) (k * η.period.toNat) ⊆
      {Plan.segment (η.compose (rowCells 0 m)) (minContent η.E + t) (k * η.period.toNat),
       Plan.segment (η.compose (rowCells 0 m)) (minContent η.E + (((m : ℤ) - k) * η.period + s))
         (k * η.period.toNat)} := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hpp : 0 < η.period := by omega
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hF := h.1.isConnectedSkew_compose hD
  obtain ⟨hmn, hmx⟩ := rowPower_content_range h hm
  have hkpos : 0 < k * η.period.toNat := Nat.mul_pos hk (by omega)
  have hcast : ((k * η.period.toNat : ℕ) : ℤ) = (k : ℤ) * η.period := by
    push_cast; rw [Int.toNat_of_nonneg hpp.le]
  intro Y hY
  rw [mem_leftRibbons_iff_segment hF hkpos] at hY
  obtain ⟨c0, h1, h2, h3, h4, hYe⟩ := hY
  rw [hcast] at h2 h4
  rw [hmn] at h1 h3
  have h2' : c0 + (k : ℤ) * η.period - 1 ≤ maxContent (η.compose (rowCells 0 m)) := by
    rw [hmx]; rw [hmx] at h2; exact h2
  have h3' : c0 = minContent (η.compose (rowCells 0 m)) ∨
      bitA (η.compose (rowCells 0 m)) c0 = 1 := by rw [hmn]; exact h3
  have h4' : c0 + (k : ℤ) * η.period - 1 = maxContent (η.compose (rowCells 0 m)) ∨
      bitA (η.compose (rowCells 0 m)) (c0 + (k : ℤ) * η.period) = 0 := by
    rw [hmx]; rw [hmx] at h4; exact h4
  have := rowPower_nw_start h hd hph hlt hm hk h1 h2' h3' h4'
  rw [hYe, Finset.mem_insert, Finset.mem_singleton]
  rcases this with e | e
  · exact Or.inl (by rw [e])
  · exact Or.inr (by rw [e])


/-- **The northwest border word of the case-(d) row power is periodic apart from two defects.**
At a residue `a ≥ 1`, passing from the band `J` to the band `J + 1` changes the northwest bit
only by the defect `-1` at `(J, a) = (0, t)` (the start) and at `(J + 1, a) = (m, s)` (the
end); at the residue `0` the bit is the constant `[0 < t]` on every band `1 ≤ J ≤ m`. -/
theorem rowPower_nw_word (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) :
    (∀ J a : ℤ, 0 ≤ J → 1 ≤ a → a < η.period →
      ((J + 1 ≤ (m : ℤ) - 1) ∨ (J + 1 = m ∧ a < η.widthZ)) →
      nwBit (η.compose (rowCells 0 m)) (minContent η.E + ((J + 1) * η.period + a)) =
        nwBit (η.compose (rowCells 0 m)) (minContent η.E + (J * η.period + a)) -
          (if J = 0 ∧ a = t then 1 else 0) - (if J + 1 = m ∧ a = s then 1 else 0)) ∧
    (∀ J : ℤ, 1 ≤ J → J ≤ (m : ℤ) →
      nwBit (η.compose (rowCells 0 m)) (minContent η.E + J * η.period) =
        if 0 < t then 1 else 0) := by
  refine ⟨fun J a hJ ha1 haq hv => ?_, fun J h1 h2 => nwBit_rowPower_zero h hd hph hlt hm h1 h2⟩
  have hw := h.width_pos
  have hv' : (0 ≤ J + 1 ∧ J + 1 ≤ (m : ℤ) - 1) ∨ (J + 1 = m ∧ a < η.widthZ) := by
    rcases hv with hv | hv
    · exact Or.inl ⟨by omega, hv⟩
    · exact Or.inr hv
  rw [nwBit_rowPower_pos h hd hph hlt hm ha1 haq (J := J + 1) hv',
    nwBit_rowPower_pos h hd hph hlt hm ha1 haq (J := J) (Or.inl ⟨hJ, by omega⟩)]
  have hJm : J ≠ m := by omega
  split_ifs <;> omega

/-- **The unweighted sum over the northwest-removable ribbons vanishes.** -/
theorem rowPower_ribbonSum_zero (h : η.IsLegalNonempty) (hd : η.case = .d) (hm : 1 ≤ m)
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ Y ∈ leftRibbons (η.compose (rowCells 0 m)) (k * η.period.toNat),
      (ribbonSign Y : Lambda) * cellSchur (η.compose (rowCells 0 m) \ Y) = 0 := by
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hpp : 0 < η.period.toNat := by have := h.1.period_pos; omega
  have hF := (h.1.isConnectedSkew_compose hD).1
  have hz := mixed_period_derivative_zero (η := η) (Or.inl h.1) (Or.inr hd) hD hk
  rw [MN.pDeriv_cellSchur_left_of_isSkew hF (Nat.mul_pos hk hpp)] at hz
  exact hz

/-- **Classification consumed by the weighted Murnaghan–Nakayama step.**  For every weight `g`
of the least content, the `g`-weighted northwest ribbon sum of the case-(d) row power is the
difference `g(y_s) - g(y_t)` of the two surviving weights, `y_t = c + t` and
`y_s = c + (m - k) p + s` with `c` the least content, times the signed cofactor of the ribbon at
`y_s` (zero unless both ribbons are removable). -/
theorem rowPower_weighted_ribbonSum (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (g : ℤ → Lambda) :
    ∑ Y ∈ leftRibbons (η.compose (rowCells 0 m)) (k * η.period.toNat),
      (ribbonSign Y : Lambda) * g (minContent Y) * cellSchur (η.compose (rowCells 0 m) \ Y) =
    (g (minContent η.E + (((m : ℤ) - k) * η.period + s)) - g (minContent η.E + t)) *
      (if Plan.segment (η.compose (rowCells 0 m))
            (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat) ∈
          leftRibbons (η.compose (rowCells 0 m)) (k * η.period.toNat) then
        (ribbonSign (Plan.segment (η.compose (rowCells 0 m))
            (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat)) : Lambda) *
          cellSchur (η.compose (rowCells 0 m) \ Plan.segment (η.compose (rowCells 0 m))
            (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat))
       else 0) := by
  classical
  set F := η.compose (rowCells 0 m) with hFdef
  set n := k * η.period.toNat with hn
  set Yt := Plan.segment F (minContent η.E + t) n with hYt
  set Ys := Plan.segment F (minContent η.E + (((m : ℤ) - k) * η.period + s)) n with hYs
  have hw := h.width_pos
  have hq := h.width_lt_period
  have hpp : 0 < n := Nat.mul_pos hk (by have := h.1.period_pos; omega)
  have hsub := rowPower_leftRibbons_subset h hd hph hlt hm hk
  have hz := rowPower_ribbonSum_zero h hd hm hk
  have hht := h.1.period_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hmk : 0 ≤ ((m : ℤ) - k) * η.period := mul_nonneg (by omega) hht.le
  have hcmp : minContent η.E + t ≠ minContent η.E + (((m : ℤ) - k) * η.period + s) := by omega
  have hne : Yt ≠ Ys := by
    intro hEq
    have := congrArg minContent hEq
    rw [hYt, hYs, minContent_segment _ _ hpp, minContent_segment _ _ hpp] at this
    exact hcmp this
  have hmt : minContent Yt = minContent η.E + t := minContent_segment _ _ hpp
  have hms : minContent Ys = minContent η.E + (((m : ℤ) - k) * η.period + s) :=
    minContent_segment _ _ hpp
  have sum2 : ∀ f : Diagram → Lambda, ∑ Y ∈ leftRibbons F n, f Y =
      (if Yt ∈ leftRibbons F n then f Yt else 0) +
        (if Ys ∈ leftRibbons F n then f Ys else 0) := by
    intro f
    have hL : leftRibbons F n = ({Yt, Ys} : Finset Diagram).filter (· ∈ leftRibbons F n) := by
      ext Y
      simp only [Finset.mem_filter]
      exact ⟨fun hY => ⟨hsub hY, hY⟩, fun hY => hY.2⟩
    conv_lhs => rw [hL]
    rw [Finset.sum_filter, Finset.sum_pair hne]
  rw [sum2] at hz ⊢
  rw [hmt, hms]
  by_cases a1 : Yt ∈ leftRibbons F n <;> by_cases a2 : Ys ∈ leftRibbons F n <;>
    simp only [a1, a2, ite_true, ite_false] at hz ⊢
  · linear_combination g (minContent η.E + t) * hz
  · linear_combination g (minContent η.E + t) * hz
  · linear_combination g (minContent η.E + t) * hz
  · simp

end RowPower

end SkewMarkedFactor
