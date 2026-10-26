/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Local/Profile.lean
import SkewMarkedFactor.Gluing.Local.Statements

/-!
# The profile of a composite

Formalizes `shields-2026-skew-gluing.tex`, «Diagonal geometry» (`eq:gluing-profile`,
`eq:gluing-mixed-profile`, and the southeast endpoint `se_E(a) + j v`).

For an outer diagram `D` with contents `[m, M]` the heights are `M_j = h_j - ℓ_j + 1` with
`M = 0` outside `[m, M]`, and `S_j = h_{j-1} - ℓ_j + 1` for `m < j ≤ M` with `S = 1` at the two ends
(`eq:gluing-profile`).  In case (d) the height of the composite on the diagonal `c₀ + (j q + a)` is
given by the four lines of `eq:gluing-mixed-profile`.

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

/-- The height `M_J` of the diagonal `J` of an outer diagram, `0` off the contents
(`eq:gluing-profile`; the paper indexes `j = J - minContent`, `M_{-1} = M_r = 0`). -/
def profM (D : Diagram) (J : ℤ) : ℤ :=
  if minContent D ≤ J ∧ J ≤ maxContent D then diagHi D J - diagLo D J + 1 else 0

/-- The quantity `S_J = h_{J-1} - ℓ_J + 1` for `minContent D < J ≤ maxContent D`, and `S = 1` at
the two ends `J = minContent D`, `J = maxContent D + 1` (`eq:gluing-profile`). -/
def profS (D : Diagram) (J : ℤ) : ℤ :=
  if minContent D + 1 ≤ J ∧ J ≤ maxContent D then diagHi D (J - 1) - diagLo D J + 1 else 1

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem sigmaD_eq (J : ℤ) : sigmaD D J = profS D J - 1 := by
  unfold sigmaD profS; split_ifs <;> omega

theorem mix_height_marked (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hc : ω.case = .d)
    {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {J a : ℤ} (ha0 : 0 ≤ a)
    (haw : a < ω.widthZ) (hv : minContent D ≤ J ∧ J ≤ maxContent D + 1) :
    height (ω.compose D) (minContent ω.E + (J * ω.period + a)) =
      height ω.W (minContent ω.E + a) +
        (if a < t then profM D (J - 1) else if a < s then profS D J - 1 else profM D J) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hcr := mix_classRows h hD hc hph hlt
  have hv' : ValidClass (minContent D) (maxContent D) ω.widthZ J a := by
    unfold ValidClass; omega
  have hLo := hcr.diagLo_eq ha0 (by omega) hv'
  have hHi := hcr.diagHi_eq ha0 (by omega) hv'
  have he := D_ends hD
  have fa := d_E_facts h hc hph ha0 (by omega : a ≤ ω.widthZ - 1)
  have hWh := h.diagHi_W ha0 (by omega : a ≤ ω.widthZ - 1)
  have hWl := h.diagLo_W ha0 (by omega : a ≤ ω.widthZ - 1)
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  have hdd : ω.dLo a = -1 ∨ ω.dLo a = 0 ∨ ω.dLo a = 1 := by omega
  unfold height
  rw [hLo, hHi, hWh, hWl]
  simp only [dLo, dHi] at fa hdd
  unfold mixHi profM profS
  by_cases hJm : J = minContent D
  · subst hJm
    rw [mixLo_P1 (by omega) (by omega)]
    simp only [oRowLo, hc]
    split_ifs <;> omega
  by_cases hJM : J = maxContent D + 1
  · subst hJM
    rw [mixLo_P2 (by omega)]
    have hp2 : (maxContent D + 1) * ω.rowShift = maxContent D * ω.rowShift + ω.rowShift := by
      ring
    simp only [oRowLo, hc, add_sub_cancel_right]
    split_ifs <;> omega
  have hJ' : minContent D + 1 ≤ J ∧ J ≤ maxContent D := by omega
  have hb := D_bits hD hJ'.1 hJ'.2
  have hdl := diagLo_le_diagHi (isConnectedSkew_iff_diagonal.mp hD |>.mem_contents_iff.mpr
    ⟨by omega, hJ'.2⟩ : J ∈ contents D)
  have hdl' := diagLo_le_diagHi (isConnectedSkew_iff_diagonal.mp hD |>.mem_contents_iff.mpr
    ⟨by omega, by omega⟩ : J - 1 ∈ contents D)
  by_cases hB : diagHi D (J - 1) - diagHi D J = 1
  · rw [mixLo_all1 (by omega) (by omega) hB]
    simp only [oRowLo, hc, hp]
    split_ifs <;> omega
  · rw [mixLo_all0 (by omega) (by omega) hB]
    simp only [oRowLo, hc, hp]
    split_ifs <;> omega

/-- **`eq:gluing-mixed-profile`, case (d), with the southeast endpoint.**  For a legal case-(d)
mark and a connected outer, the composite has southeast endpoint `se_E(a) + J v` on every
diagonal class, and its height on the diagonal `c₀ + (J q + a)` is
* `ν_a + M_J - 1` on a private residue `w ≤ a < q`, `m ≤ J ≤ M`,
* `Ω_a + M_{J-1}` for `a < t`, `Ω_a + S_J - 1` for `t ≤ a < s`, `Ω_a + M_J` for `s ≤ a < w`,
  for `m ≤ J ≤ M + 1`,
where `ν_a` is the height of `E` on the diagonal `a` and `Ω_a` that of `W₋`. -/
theorem IsLegalNonempty.mixed_profile (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D)
    (hc : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {J a : ℤ} (ha0 : 0 ≤ a)
    (haq : a < ω.period)
    (hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a) :
    diagHi (ω.compose D) (minContent ω.E + (J * ω.period + a)) =
      diagHi ω.E (minContent ω.E + a) + J * ω.rowShift ∧
    (ω.widthZ ≤ a → height (ω.compose D) (minContent ω.E + (J * ω.period + a)) =
      height ω.E (minContent ω.E + a) + profM D J - 1) ∧
    (a < t → height (ω.compose D) (minContent ω.E + (J * ω.period + a)) =
      height ω.W (minContent ω.E + a) + profM D (J - 1)) ∧
    (t ≤ a → a < s → height (ω.compose D) (minContent ω.E + (J * ω.period + a)) =
      height ω.W (minContent ω.E + a) + profS D J - 1) ∧
    (s ≤ a → a < ω.widthZ → height (ω.compose D) (minContent ω.E + (J * ω.period + a)) =
      height ω.W (minContent ω.E + a) + profM D J) := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  have hcr := mix_classRows h hD hc hph hlt
  have hLo := hcr.diagLo_eq ha0 haq hv
  have hHi := hcr.diagHi_eq ha0 haq hv
  have hJr : minContent D ≤ J ∧ J ≤ maxContent D + 1 := by unfold ValidClass at hv; omega
  have hph' := hph
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph'
  refine ⟨by rw [hHi]; unfold mixHi hi; ring, ?_, ?_, ?_, ?_⟩
  · intro haw
    have hJ : minContent D ≤ J ∧ J ≤ maxContent D := by unfold ValidClass at hv; omega
    unfold height
    rw [hLo, hHi]
    rw [mixLo_P1 hJ (by omega)]
    unfold mixHi profM
    simp only [oRowLo, hc, hJ, and_self, ite_true]
    unfold hi lo
    omega
  · intro hat
    have := mix_height_marked h hD hc hph hlt ha0 (by omega) hJr
    rw [this]; simp [hat]
  · intro hta has
    have := mix_height_marked h hD hc hph hlt ha0 (by omega) hJr
    rw [this]
    have : ¬ a < t := by omega
    simp [this, has]; omega
  · intro hsa haw
    have := mix_height_marked h hD hc hph hlt ha0 haw hJr
    rw [this]
    have h1 : ¬ a < t := by omega
    have h2 : ¬ a < s := by omega
    simp [h1, h2]

end MarkedInner

end SkewMarkedFactor.Gluing
