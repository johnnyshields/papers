-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/CornerCase/WordWindows.lean
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Basic
import GluingCore.Tactics

/-!
# Windows of the southeast word of a corner composite

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-holes`, `eq:gluing-caps`, `eq:gluing-interface`) as used in thesis Lemma 5.5.7
(`OlsonHarris2024HopfApplications`).

A ribbon of size `m q` removable on the right from a diagram of span `N = r q + w` is read off its
southeast word `B` as a window start `k` with `k = 0` or `B_k = 0`, and window end `k + m q = N`
or `B_{k+mq} = 1`.  If `B` has period `q` except at the residues `s`, `t`
(`0 ≤ t < s ≤ w < q`), reads
`B_{jq+s} = Bx_j` and `B_{jq+t} = 1 - Ax_j` there (the bits of the outer, extended by
`Bx_0 = 0`, `Bx_r = 1`, `Ax_0 = 1`, `Ax_r = 0`), and satisfies the two extra conditions `B_q = 0`
(when `t ≥ 1`) and `B_w = 1` (when `s < w`), then the windows are exactly those at the residues
`s` and `t` whose ends read the outer in the same way (`window_classification`).

This is pure integer arithmetic.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace Corner

/-- A word with period `q` away from the residues `s`, `t` is constant along the arithmetic
progression of a position of another residue. -/
theorem word_chain {q N s t : ℤ} {B : ℤ → ℤ} (hq : 0 < q)
    (hPer : ∀ x, 1 ≤ x → x + q ≤ N - 1 → x % q ≠ s → x % q ≠ t → B x = B (x + q))
    {x : ℤ} (hx : 1 ≤ x) (hs : x % q ≠ s) (ht : x % q ≠ t) :
    ∀ i : ℕ, x + i * q ≤ N - 1 → B (x + i * q) = B x := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro h
    have h1 : x + i * q ≤ N - 1 := by push_cast at h; nlinarith
    have e : x + ((i + 1 : ℕ) : ℤ) * q = (x + i * q) + q := by push_cast; ring
    have hmod : (x + i * q) % q = x % q := by
      rw [Int.add_mul_emod_self_right]
    rw [e, ← hPer _ (by nlinarith [Int.natCast_nonneg i]) (by rw [e] at h; exact h)
      (by rw [hmod]; exact hs) (by rw [hmod]; exact ht)]
    exact ih h1

/-- **Classification of the windows of the southeast word.**  See the module docstring. -/
theorem window_classification {q w s t r m : ℤ} {B Bx Ax : ℤ → ℤ} (hq : 0 < q) (hw : 0 < w)
    (hwq : w < q) (ht : 0 ≤ t) (hts : t < s) (hs : s ≤ w) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hBxr : Bx r = 1) (hAx0 : Ax 0 = 1) (hAxr : Ax r = 0)
    (hPs : ∀ j, 0 ≤ j → j * q + s ≤ r * q + w - 1 → B (j * q + s) = Bx j)
    (hPt : ∀ j, 0 ≤ j → j * q + t ≤ r * q + w - 1 → 1 ≤ j * q + t →
      B (j * q + t) = 1 - Ax j)
    (hPer : ∀ x, 1 ≤ x → x + q ≤ r * q + w - 1 → x % q ≠ s → x % q ≠ t → B x = B (x + q))
    (hFq : 1 ≤ t → B q = 0) (hFw : s < w → B w = 1) {k : ℤ} :
    (0 ≤ k ∧ k + m * q ≤ r * q + w ∧ (k = 0 ∨ B k = 0) ∧
        (k + m * q = r * q + w ∨ B (k + m * q) = 1)) ↔
      (∃ j, k = j * q + s ∧ 0 ≤ j ∧ j + m ≤ r ∧ Bx j = 0 ∧ Bx (j + m) = 1) ∨
      (∃ j, k = j * q + t ∧ 0 ≤ j ∧ j + m ≤ r ∧ Ax j = 1 ∧ Ax (j + m) = 0) := by
  have hmono : ∀ u v : ℤ, u ≤ v → u * q ≤ v * q := fun u v h => by nlinarith
  have hstr : ∀ u v : ℤ, u + 1 ≤ v → u * q + q ≤ v * q := fun u v h => by nlinarith
  have hnn : ∀ u : ℤ, 0 ≤ u → 0 ≤ u * q := fun u h => by nlinarith
  have hadd : ∀ u v : ℤ, (u + v) * q = u * q + v * q := fun u v => add_mul u v q
  have hmq : q ≤ m * q := by nlinarith
  have hzq : (0 : ℤ) * q = 0 := zero_mul q
  have hresid : ∀ j a : ℤ, 0 ≤ a → a < q → (j * q + a) % q = a := fun j a h0 h1 => by
    rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt h0 h1]
  -- the end `(j + m) q + a = N` forces `j + m = r` and `a = w`
  have hendEq : ∀ j a : ℤ, 0 ≤ a → a < q → (j + m) * q + a = r * q + w →
      j + m = r ∧ a = w := by
    intro j a ha0 haq h
    have hz : j + m = r := by
      rcases lt_trichotomy (j + m) r with hh | hh | hh
      · have := hstr _ _ (by omega : j + m + 1 ≤ r)
        omega
      · exact hh
      · have := hstr _ _ (by omega : r + 1 ≤ j + m)
        omega
    subst hz
    omega
  have hbig : ∀ j a : ℤ, 0 ≤ a → r + 1 ≤ j + m → r * q + w < (j + m) * q + a := by
    intro j a ha0 hh
    have := hstr _ _ hh
    omega
  have hsmall : ∀ j a : ℤ, a < q → j + m + 1 ≤ r → (j + m) * q + a < r * q := by
    intro j a haq hh
    have := hstr _ _ hh
    omega
  have hchain : ∀ x : ℤ, 1 ≤ x → x % q ≠ s → x % q ≠ t → ∀ i : ℤ, 0 ≤ i →
      x + i * q ≤ r * q + w - 1 → B (x + i * q) = B x := by
    intro x hx h1 h2 i hi hle
    have := word_chain (N := r * q + w) hq hPer hx h1 h2 i.toNat (by
      rw [Int.toNat_of_nonneg hi]; exact hle)
    rwa [Int.toNat_of_nonneg hi] at this
  constructor
  · rintro ⟨hk0, hkN, hst, hend⟩
    obtain ⟨j, a, ha0, haq, hka⟩ : ∃ j a, 0 ≤ a ∧ a < q ∧ k = j * q + a :=
      ⟨k / q, k % q, Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq, by
        have := Int.mul_ediv_add_emod k q
        linarith [mul_comm q (k / q)]⟩
    have hj0 : 0 ≤ j := by
      by_contra hh
      have := hstr j (-1 + 1) (by omega)
      have h0 : (-1 + 1 : ℤ) * q = 0 := by ring
      omega
    have hkm : k + m * q = (j + m) * q + a := by rw [hka, hadd]; ring
    have hkq : k + q ≤ r * q + w := by omega
    by_cases has : a = s
    · left
      subst has
      have hjn := hnn j hj0
      have hk1 : 1 ≤ k := by omega
      have hB : B k = 0 := hst.resolve_left (by omega)
      rw [hka, hPs j hj0 (by omega)] at hB
      have hjr : j + m ≤ r := by
        by_contra hh
        have := hbig j a ha0 (by omega)
        omega
      refine ⟨j, hka, hj0, hjr, hB, ?_⟩
      by_cases hjeq : j + m = r
      · rw [hjeq]; exact hBxr
      · rcases hend with he | he
        · have := hendEq j a ha0 haq (by omega)
          exact absurd this.1 hjeq
        · rw [hkm] at he
          have hlt : (j + m) * q + a ≤ r * q + w - 1 := by
            have := hsmall j a haq (by omega)
            omega
          rw [← hPs (j + m) (by omega) hlt]
          exact he
    · by_cases hat : a = t
      · right
        subst hat
        have hjr : j + m ≤ r := by
          by_contra hh
          have := hbig j a ha0 (by omega)
          omega
        have hjn := hnn j hj0
        have hAj : Ax j = 1 := by
          by_cases hk0 : k = 0
          · have hj : j = 0 := by
              by_contra hh
              have hj1 : 1 ≤ j := by omega
              have := hmono 1 j hj1
              omega
            subst hj
            exact hAx0
          · have h0 := hst.resolve_left hk0
            have := hPt j hj0 (by omega) (by omega)
            rw [← hka, h0] at this
            omega
        refine ⟨j, hka, hj0, hjr, hAj, ?_⟩
        have hne : k + m * q ≠ r * q + w := by
          intro h
          have := hendEq j a ha0 haq (by omega)
          omega
        have he := hend.resolve_left hne
        rw [hkm] at he
        have hlt : (j + m) * q + a ≤ r * q + w - 1 := by
          rcases lt_or_eq_of_le hjr with h1 | h1
          · have := hsmall j a haq (by omega)
            omega
          · subst h1
            omega
        have := hPt (j + m) (by omega) hlt (by
          have := hnn (j + m) (by omega)
          omega)
        omega
      · exfalso
        by_cases hk : k = 0
        · -- the window starts at the first diagonal
          have ha : a = 0 := by
            have := hnn j hj0
            omega
          have ht1 : 1 ≤ t := by omega
          rcases hend with he | he
          · have := hendEq 0 0 le_rfl hq (by rw [zero_add, add_zero]; rw [hk] at he; omega)
            omega
          · have hne : m * q ≠ r * q + w := by
              intro h
              have := hendEq 0 0 le_rfl hq (by rw [zero_add, add_zero]; exact h)
              omega
            have hq1 : q % q = 0 := Int.emod_self
            have hch := hchain q (by omega) (by rw [hq1]; omega) (by rw [hq1]; omega)
              (m - 1) (by omega) (by
                have : q + (m - 1) * q = m * q := by ring
                omega)
            have e : q + (m - 1) * q = k + m * q := by rw [hk]; ring
            rw [e] at hch
            rw [hch, hFq ht1] at he
            omega
        · have hk1 : 1 ≤ k := by omega
          have hB : B k = 0 := hst.resolve_left hk
          have hres1 : k % q ≠ s := by rw [hka, hresid j a ha0 haq]; exact has
          have hres2 : k % q ≠ t := by rw [hka, hresid j a ha0 haq]; exact hat
          rcases hend with he | he
          · -- the window ends at the last diagonal: `a = w`
            have h1 := hendEq j a ha0 haq (by omega)
            have haw : a = w := h1.2
            have hsw : s < w := by omega
            have hw1 := hFw hsw
            have hwmod : w % q = w := Int.emod_eq_of_lt hw.le hwq
            have hch := hchain w (by omega) (by rw [hwmod]; omega) (by rw [hwmod]; omega)
              (r - m) (by omega) (by
                have : (r - m) * q = r * q - m * q := by ring
                omega)
            have e : w + (r - m) * q = k := by
              have : (r - m) * q = r * q - m * q := by ring
              omega
            rw [e, hB, hw1] at hch
            omega
          · have hne : k + m * q ≤ r * q + w - 1 := by
              by_contra hh
              have h2 : k + m * q = r * q + w := by omega
              have h1 := hendEq j a ha0 haq (by omega)
              have haw : a = w := h1.2
              have hsw : s < w := by omega
              have hw1 := hFw hsw
              have hwmod : w % q = w := Int.emod_eq_of_lt hw.le hwq
              have hch := hchain w (by omega) (by rw [hwmod]; omega) (by rw [hwmod]; omega)
                (r - m) (by omega) (by
                  have : (r - m) * q = r * q - m * q := by ring
                  omega)
              have e : w + (r - m) * q = k := by
                have : (r - m) * q = r * q - m * q := by ring
                omega
              rw [e, hB, hw1] at hch
              omega
            have hch := hchain k hk1 hres1 hres2 m (by omega) (by omega)
            rw [hB] at hch
            omega
  · rintro (⟨j, hk, hj0, hjr, hB0, hB1⟩ | ⟨j, hk, hj0, hjr, hA1, hA0⟩)
    · have hkm : k + m * q = (j + m) * q + s := by rw [hk, hadd]; ring
      have hle : (j + m) * q + s ≤ r * q + w := by
        rcases lt_or_eq_of_le hjr with h1 | h1
        · have := hsmall j s (by omega) (by omega)
          omega
        · rw [h1]; omega
      have hk1 : 1 ≤ k := by
        have := hnn j hj0
        omega
      refine ⟨by omega, by omega, Or.inr ?_, ?_⟩
      · rw [hk, hPs j hj0 (by omega)]; exact hB0
      · by_cases he : k + m * q = r * q + w
        · exact Or.inl he
        · right
          rw [hkm, hPs (j + m) (by omega) (by omega)]; exact hB1
    · have hkm : k + m * q = (j + m) * q + t := by rw [hk, hadd]; ring
      have hle : (j + m) * q + t ≤ r * q + w - 1 := by
        rcases lt_or_eq_of_le hjr with h1 | h1
        · have := hsmall j t (by omega) (by omega)
          omega
        · rw [h1]; omega
      have hjn := hnn j hj0
      refine ⟨by omega, by omega, ?_, Or.inr ?_⟩
      · by_cases h0 : k = 0
        · exact Or.inl h0
        · right
          have := hPt j hj0 (by omega) (by omega)
          rw [hk, this]; omega
      · rw [hkm, hPt (j + m) (by omega) hle (by have := hnn (j + m) (by omega); omega)]
        omega

end Corner

end Plan

end GluingCore
