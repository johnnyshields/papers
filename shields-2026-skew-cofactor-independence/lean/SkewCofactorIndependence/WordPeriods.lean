/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# Periods of finite words

The finite-word argument in «Integral dilation» (`sec:dilation`), used in
`lem:endpoint-normalization`.  A period is asserted only for pairs of indices
inside the finite word.  The subtraction step includes both boundary regimes.
-/

namespace SkewCofactorIndependence

/-- A period of a word with domain `Fin L`; no values outside the word are used. -/
def WordPeriod {α : Type*} {L : ℕ} (w : Fin L → α) (p : ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < L) (hip : i + p < L),
    w ⟨i, hi⟩ = w ⟨i + p, hip⟩

/-- The zero period is valid, including for an empty word. -/
theorem wordPeriod_zero {α : Type*} {L : ℕ} (w : Fin L → α) : WordPeriod w 0 := by
  intro i hi hip
  rfl

/-- Euclidean subtraction, with comparisons made entirely inside the word. -/
theorem WordPeriod.sub {α : Type*} {L p q : ℕ} {w : Fin L → α}
    (hp : WordPeriod w p) (hq : WordPeriod w q)
    (hpq : p ≤ q) (hL : p + q ≤ L) : WordPeriod w (q - p) := by
  intro i hi hid
  by_cases hpi : p ≤ i
  · have him : i - p < L := by omega
    have hiq : i - p + q < L := by omega
    have hip : i - p + p < L := by omega
    have ep := hp (i - p) him hip
    have eq := hq (i - p) him hiq
    have ei : i - p + p = i := by omega
    have ed : i - p + q = i + (q - p) := by omega
    simpa only [ei, ed] using ep.symm.trans eq
  · have hiq : i + q < L := by omega
    have hidp : i + (q - p) + p < L := by omega
    have eq := hq i hi hiq
    have ep := hp (i + (q - p)) hid hidp
    have ed : i + (q - p) + p = i + q := by omega
    have ep' : w ⟨i + (q - p), hid⟩ = w ⟨i + q, hiq⟩ := by
      simpa only [ed] using ep
    exact eq.trans ep'.symm

/-- Positive periods whose sum fits in the word have their gcd as a period. -/
theorem WordPeriod.gcd {α : Type*} {L p q : ℕ} {w : Fin L → α}
    (hp : WordPeriod w p) (hq : WordPeriod w q)
    (hp0 : 0 < p) (hq0 : 0 < q) (hL : p + q ≤ L) :
    WordPeriod w (Nat.gcd p q) := by
  have main : ∀ s p q : ℕ, p + q = s → 0 < p → 0 < q → p + q ≤ L →
      WordPeriod w p → WordPeriod w q → WordPeriod w (Nat.gcd p q) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro p q hs hp0 hq0 hL hp hq
      rcases lt_trichotomy p q with hpq | hpq | hqp
      · have hd0 : 0 < q - p := by omega
        have hd := hp.sub hq (by omega) hL
        have hs' : p + (q - p) < s := by omega
        have hg := ih (p + (q - p)) hs' p (q - p) rfl hp0 hd0 (by omega) hp hd
        simpa only [Nat.gcd_sub_self_right (by omega : p ≤ q)] using hg
      · subst q
        simpa using hp
      · have hd0 : 0 < p - q := by omega
        have hd := hq.sub hp (by omega) (by omega)
        have hs' : q + (p - q) < s := by omega
        have hg := ih (q + (p - q)) hs' q (p - q) rfl hq0 hd0 (by omega) hq hd
        rw [Nat.gcd_sub_self_right (by omega : q ≤ p), Nat.gcd_comm] at hg
        exact hg
  exact main (p + q) p q rfl hp0 hq0 hL hp hq

/-- The paper's one-based endpoint formulation of a period. -/
def OneBasedWordPeriod {α : Type*} (w : ℕ → α) (L p : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i + p ≤ L → w i = w (i + p)

/-- Zero-based finite words and the one-based endpoint convention agree. -/
theorem oneBasedWordPeriod_iff {α : Type*} (w : ℕ → α) (L p : ℕ) :
    OneBasedWordPeriod w L p ↔ WordPeriod (fun i : Fin L => w (i.val + 1)) p := by
  constructor
  · intro h i hi hip
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      h (i + 1) (by omega) (by omega)
  · intro h i hi hip
    have hi' : i - 1 < L := by omega
    have hip' : i - 1 + p < L := by omega
    have he := h (i - 1) hi' hip'
    change w (i - 1 + 1) = w (i - 1 + p + 1) at he
    have e₁ : i - 1 + 1 = i := by omega
    have e₂ : i - 1 + p + 1 = i + p := by omega
    simpa only [e₁, e₂] using he

/-- Finite-word gcd lemma in the exact endpoint convention of `sec:dilation`. -/
theorem OneBasedWordPeriod.gcd {α : Type*} {w : ℕ → α} {L p q : ℕ}
    (hp : OneBasedWordPeriod w L p) (hq : OneBasedWordPeriod w L q)
    (hp0 : 0 < p) (hq0 : 0 < q) (hL : p + q ≤ L) :
    OneBasedWordPeriod w L (Nat.gcd p q) := by
  apply (oneBasedWordPeriod_iff _ _ _).2
  exact ((oneBasedWordPeriod_iff _ _ _).1 hp).gcd
    ((oneBasedWordPeriod_iff _ _ _).1 hq) hp0 hq0 hL

end SkewCofactorIndependence
