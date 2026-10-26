/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Mark1.lean`. -/
import GluingCore.Aligned.CaseD.Mark0

/-!
# Aligned marks, case (d): the middle of the lower mark

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`).

`alD_mark V a θ cs` is the candidate lower mark: `E = V`, `W₋ = Z = V ∩ (V - z)`, `v = z`, case
`c`.  This file describes its upper copy and its middle on the diagonals of `V`, and proves that
the middle has at most one cell on every diagonal outside `[b + 1, a - 2]`, which is the
content-distance input of condition IV.

Sorry-free.
-/

namespace GluingCore

/-- The candidate lower mark on `V`. -/
def alD_mark (V : Diagram) (a θ : ℤ) (cs : AttachCase) : MarkedInner where
  E := V
  W := alD_Z V a θ
  v := alD_z a θ
  case := cs

section Mid

variable {V : Diagram} {a θ : ℤ} {cs : AttachCase}

theorem alD_mark_E : (alD_mark V a θ cs).E = V := rfl
theorem alD_mark_W : (alD_mark V a θ cs).W = alD_Z V a θ := rfl
theorem alD_mark_v : (alD_mark V a θ cs).v = alD_z a θ := rfl

theorem alD_mem_upper (hV : IsConnectedSkew V) (ha : 0 ≤ a) (r j : ℤ) :
    (r, r + (minContent V + j)) ∈ (alD_mark V a θ cs).upper ↔
      a ≤ j ∧ j < (span V : ℤ) ∧ alD_zl V a θ (j - a) ≤ r - θ ∧
        r - θ ≤ alD_zh V a θ (j - a) := by
  unfold MarkedInner.upper
  rw [mem_translate, alD_mark_v, alD_cell_sub_z, alD_mark_W, alD_mem_Z hV ha]
  have e : j - a + a = j := by ring
  rw [e]
  omega

theorem alD_mem_middle (hV : IsConnectedSkew V) (ha : 0 ≤ a) (r j : ℤ) :
    (r, r + (minContent V + j)) ∈ (alD_mark V a θ cs).middle ↔
      (0 ≤ j ∧ j < (span V : ℤ) ∧ alD_L V j ≤ r ∧ r ≤ alD_H V j) ∧
      ¬ (0 ≤ j ∧ j + a < (span V : ℤ) ∧ alD_zl V a θ j ≤ r ∧ r ≤ alD_zh V a θ j) ∧
      ¬ (a ≤ j ∧ j < (span V : ℤ) ∧ alD_zl V a θ (j - a) ≤ r - θ ∧
        r - θ ≤ alD_zh V a θ (j - a)) := by
  unfold MarkedInner.middle
  rw [Finset.mem_sdiff, Finset.mem_union, not_or, alD_mark_E, alD_mark_W, alD_mem_V hV,
    alD_mem_Z hV ha, alD_mem_upper hV ha]

/-- The middle has at most one cell on each diagonal outside `[b + 1, a - 2]`. -/
theorem alD_middle_thin (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {r₁ r₂ j : ℤ}
    (h₁ : (r₁, r₁ + (minContent V + j)) ∈ (alD_mark V a θ cs).middle)
    (h₂ : (r₂, r₂ + (minContent V + j)) ∈ (alD_mark V a θ cs).middle) (hne : r₁ ≠ r₂) :
    (span V : ℤ) - a + 1 ≤ j ∧ j ≤ a - 2 := by
  have hb := hD.hb
  have hba := hD.hba
  have ha := hD.ha
  rw [alD_mem_middle hV ha.le] at h₁ h₂
  have l0 := alD_L_le_H hV (j := j) (by omega) (by omega)
  by_cases hj1 : j < (span V : ℤ) - a
  · have z := alD_zrows hV hD (j := j) (by omega) hj1
    have e1 := hD.e_bd j (by omega) hj1
    have l2 := alD_L_le_H hV (j := j + a) (by omega) (by omega)
    unfold alD_e at e1 z
    omega
  by_cases hj2 : a ≤ j
  · have z := alD_zrows hV hD (j := j - a) (by omega) (by omega)
    have e1 := hD.e_bd (j - a) (by omega) (by omega)
    have l2 := alD_L_le_H hV (j := j - a) (by omega) (by omega)
    have e : j - a + a = j := by ring
    unfold alD_e at e1 z
    rw [e] at e1 z
    have hz := z.2.2.2.2.2
    have l3 := alD_L_le_H hV (j := j) (by omega) (by omega)
    obtain ⟨⟨_, _, a1, a2⟩, b1, b2⟩ := h₁
    obtain ⟨⟨_, _, a3, a4⟩, b3, b4⟩ := h₂
    omega
  · have s1 := hD.singleton_b
    have s2 := hD.singleton_a
    by_contra hcon
    have : j = (span V : ℤ) - a ∨ j = a - 1 := by omega
    rcases this with h | h <;> subst h <;> omega

end Mid

end GluingCore
