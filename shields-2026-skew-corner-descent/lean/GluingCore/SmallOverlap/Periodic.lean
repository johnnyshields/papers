/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/SmallOverlap/Periodic.lean`. -/
import GluingCore.SmallOverlap.Words

/-!
# Period words of two roots

Formalizes `shields-2026-skew-factor-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`): the use of `lem:gluing-periods` on the boundary words of a diagram
with a root of width zero.

* `PeriodExcept.eq_of_dvd`: a word with period `g` except at the residues `S` is constant along a
  residue class modulo `g` not in `S`.
* `periodExcept_gcd_empty_ordinary`: an empty root of period `p` and an ordinary root of period
  `Q` (neither period dividing the other) put both boundary words at period `gcd p Q` except at
  the residue zero (`lem:gluing-periods` (ii)).
* `empty_mixed_false`: an empty root and a mixed root of periods that do not divide one another
  cannot coexist (the mixed root's fixed boundary becomes `g`-periodic, against its two private
  endpoint bits).

Sorry-free.
-/

namespace GluingCore

open MarkedInner

namespace SmallOverlap

/-- A word with period `g` except at the residues `S` is constant along a residue class modulo
`g` that avoids `S`. -/
theorem periodExcept_eq_of_dvd {α : Type*} {L g : ℕ} {S : Finset ℤ} {f : ℤ → α}
    (hf : PeriodWords.PeriodExcept L g S f) (hg : 0 < g) {x y : ℤ} (hx : 1 ≤ x) (hy : y ≤ L)
    (hxy : x ≤ y) (hd : (g : ℤ) ∣ y - x) (hS : x % (g : ℤ) ∉ S) : f x = f y := by
  obtain ⟨k, hk⟩ := hd
  have hk0 : 0 ≤ k := by
    by_contra h
    have : (g : ℤ) * k < 0 := Int.mul_neg_of_pos_of_neg (by exact_mod_cast hg) (by omega)
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  have key : ∀ m : ℕ, m ≤ n → f x = f (x + g * m) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have hmem : x + g * m ∈ Finset.Icc (1 : ℤ) ((L : ℤ) - g) := by
        rw [Finset.mem_Icc]
        have : (g : ℤ) * (m + 1 : ℕ) ≤ g * n := by
          apply mul_le_mul_of_nonneg_left (by exact_mod_cast hm) (by positivity)
        push_cast at this ⊢
        constructor <;> nlinarith
      have hres : (x + g * m) % (g : ℤ) = x % (g : ℤ) := by
        simp
      have h2 := hf (x + g * m) hmem (by rw [hres]; exact hS)
      rw [h1, h2]
      congr 1
      push_cast
      ring
  have := key n le_rfl
  rw [this]
  congr 1
  omega

/-- **`lem:gluing-periods` (ii), empty root.**  A word of the positions `1, …, N - 1` with period
`p`
except at the residue zero (`N = r p`) and period `Q` except at one residue `h ∈ [0, u]`
(`N = m Q + u`), neither period dividing the other and `r, m ≥ 2`, has period `gcd p Q` except at
the residue zero. -/
theorem periodExcept_gcd_zero_hole {α : Type*} {f : ℤ → α} {p Q N r m u : ℕ} {h : ℤ}
    (hp : 0 < p) (hQ : 0 < Q) (hr : 2 ≤ r) (hm : 2 ≤ m) (hu : u < Q) (hNp : N = r * p)
    (hNQ : N = m * Q + u) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p) (hh : 0 ≤ h ∧ h ≤ u)
    (hfp : PeriodWords.PeriodExcept (N - 1) p {0} f)
    (hfQ : PeriodWords.PeriodExcept (N - 1) Q {h} f) :
    PeriodWords.PeriodExcept (N - 1) (Nat.gcd p Q) {0} f := by
  have hN1 : 1 ≤ N := by
    have : 1 * p ≤ r * p := Nat.mul_le_mul_right p (by omega)
    omega
  have hL : (N - 1) + 1 = N := by omega
  intro x hx hS
  have hgp : (Nat.gcd p Q : ℤ) ∣ p := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have hg : 0 < Nat.gcd p Q := Nat.gcd_pos_of_pos_left _ hp
  simp only [Finset.mem_Icc] at hx
  have hxmem : x ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ) := by
    rw [Finset.mem_Icc]; push_cast [Nat.cast_sub hN1] at hx ⊢; omega
  have hymem : x + (Nat.gcd p Q : ℤ) ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ) := by
    rw [Finset.mem_Icc]; push_cast [Nat.cast_sub hN1] at hx ⊢; omega
  have hnh : ∀ y : ℤ, y % (Nat.gcd p Q : ℤ) ≠ 0 →
      ¬ PeriodWords.IsSimultaneousHole p Q {0} {h} y := by
    intro y hy hsim
    apply hy
    have h1 : y % (p : ℤ) = 0 := by simpa using hsim.1
    have h2 : (p : ℤ) ∣ y := Int.dvd_of_emod_eq_zero h1
    exact Int.emod_eq_zero_of_dvd (dvd_trans hgp h2)
  have hx0 : x % (Nat.gcd p Q : ℤ) ≠ 0 := by simpa using hS
  have hx1 : (x + (Nat.gcd p Q : ℤ)) % (Nat.gcd p Q : ℤ) ≠ 0 := by simpa using hS
  exact PeriodWords.eq_of_periods_two_holes (w := 0) (h₁ := 0) (h₂ := h) hp hQ hr hm
    (by omega) hu (by simpa using hNp) hNQ hpQ hQp (by simp) hh hL hfp hfQ hxmem hymem
    ⟨1, by ring⟩ (hnh x hx0) (hnh _ hx1)

/-! ### Periodicity of the words of the diagram presented by a root -/

/-- The parent of a chart with proper legal data is connected skew. -/
theorem _root_.GluingCore.Chart.IsProperRoot.parent_conn {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) :
    IsConnectedSkew χ.parent :=
  h.1.2.2.2.isConnectedSkew_compose h.1.1

theorem _root_.GluingCore.Chart.IsProperRoot.span_eq {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) :
    span F = span χ.parent := by
  obtain ⟨t, ht⟩ := h.2.1
  rw [ht]; exact span_translate _

theorem _root_.GluingCore.Chart.IsProperRoot.wordA_eq {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) {k : ℤ}
    (h1 : 1 ≤ k) (h2 : k < (span F : ℤ)) : wordA F k = wordA χ.parent k := by
  obtain ⟨t, ht⟩ := h.2.1
  have hs := h.span_eq
  rw [ht]
  exact wordA_translate h.parent_conn t h1 (by rw [hs] at h2; exact h2)

theorem _root_.GluingCore.Chart.IsProperRoot.wordB_eq {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) {k : ℤ}
    (h1 : 1 ≤ k) (h2 : k < (span F : ℤ)) : wordB F k = wordB χ.parent k := by
  obtain ⟨t, ht⟩ := h.2.1
  have hs := h.span_eq
  rw [ht]
  exact wordB_translate h.parent_conn t h1 (by rw [hs] at h2; exact h2)

/-- A period constraint on the positions `1, …, N - 1` transfers along words that agree there. -/
theorem periodExcept_congr {α : Type*} {L p : ℕ} {S : Finset ℤ} {f f' : ℤ → α}
    (hf : ∀ x : ℤ, 1 ≤ x → x ≤ (L : ℤ) → f x = f' x) (h : PeriodWords.PeriodExcept L p S f') :
    PeriodWords.PeriodExcept L p S f := by
  intro x hx hS
  simp only [Finset.mem_Icc] at hx
  rw [hf x hx.1 (by omega), hf (x + p) (by omega) (by omega)]
  exact h x (by simp only [Finset.mem_Icc]; omega) hS

/-- The words of `F` have the periodicity of `eq:gluing-holes` for a proper root with a nonempty
copy and phases `s, t`. -/
theorem _root_.GluingCore.Chart.IsProperRoot.periodic_nonempty {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) (hW : χ.ω.W.Nonempty) {s t : ℤ} (hph : χ.ω.IsPhases s t) :
    PeriodWords.PeriodExcept (span F - 1) p (holesA χ.ω.case s t) (wordA F) ∧
    PeriodWords.PeriodExcept (span F - 1) p (holesB χ.ω.case s t) (wordB F) := by
  have hp : χ.ω.period.toNat = p := by
    have : χ.ω.period = p := h.2.2
    omega
  have hcod := MarkedInner.IsLegalNonempty.gluing_coding_periodic
    (ω := χ.ω) (D := χ.D) ⟨h.1.2.2.2, hW⟩ h.1.1 hph
  have hs := h.span_eq
  change PeriodWords.PeriodExcept (span χ.parent - 1) _ _ (wordA χ.parent) ∧
    PeriodWords.PeriodExcept (span χ.parent - 1) _ _ (wordB χ.parent) at hcod
  rw [hp] at hcod
  have hsp : 2 ≤ span F := h.arith.1.trans (by
    have := h.arith.2.1
    have h2 := h.arith.2.2.2
    have h3 : (0 : ℤ) ≤ χ.ω.width := by positivity
    have : (span χ.D : ℤ) ≤ span F := by nlinarith [h.arith.1]
    exact_mod_cast this)
  refine ⟨?_, ?_⟩
  · rw [hs]
    refine periodExcept_congr (fun x h1 h2 => ?_) hcod.1
    refine h.wordA_eq h1 ?_
    rw [hs] at *; omega
  · rw [hs]
    refine periodExcept_congr (fun x h1 h2 => ?_) hcod.2
    refine h.wordB_eq h1 ?_
    rw [hs] at *; omega

/-- The words of `F` have period `p` except at the residue zero for a proper root of width zero. -/
theorem _root_.GluingCore.Chart.IsProperRoot.periodic_empty {χ : Chart} {F : Diagram} {p : ℕ}
    (h : χ.IsProperRoot F p) (hW : χ.ω.W = ∅) :
    PeriodWords.PeriodExcept (span F - 1) p {0} (wordA F) ∧
    PeriodWords.PeriodExcept (span F - 1) p {0} (wordB F) := by
  have hp : χ.ω.period.toNat = p := by
    have : χ.ω.period = p := h.2.2
    omega
  have hcod := MarkedInner.IsLegalEmpty.periodExcept (ω := χ.ω) (D := χ.D) ⟨h.1.2.2.2, hW⟩ h.1.1
  have hs := h.span_eq
  change PeriodWords.PeriodExcept (span χ.parent - 1) _ _ (wordA χ.parent) ∧
    PeriodWords.PeriodExcept (span χ.parent - 1) _ _ (wordB χ.parent) at hcod
  rw [hp] at hcod
  refine ⟨?_, ?_⟩
  · rw [hs]
    refine periodExcept_congr (fun x h1 h2 => ?_) hcod.1
    refine h.wordA_eq h1 ?_
    rw [hs] at *; omega
  · rw [hs]
    refine periodExcept_congr (fun x h1 h2 => ?_) hcod.2
    refine h.wordB_eq h1 ?_
    rw [hs] at *; omega

/-- **`lem:gluing-periods` (i), both orders.**  A full period `Q` and a period `p` except at one
residue, neither dividing the other, on a word of length `L` with `2 p ≤ L + 1` and `2 Q ≤ L`, give
the full period `gcd Q p`. -/
theorem periodExcept_gcd_full_hole {α : Type*} {f : ℤ → α} {Q p L : ℕ} (hQ : 0 < Q) (hp : 0 < p)
    (hQp : ¬ Q ∣ p) (hpQ : ¬ p ∣ Q) (h : ℤ) (hL1 : 2 * p ≤ L + 1) (hL2 : 2 * Q ≤ L)
    (hfQ : PeriodWords.PeriodExcept L Q ∅ f) (hfp : PeriodWords.PeriodExcept L p {h} f) :
    PeriodWords.PeriodExcept L (Nat.gcd Q p) ∅ f := by
  rcases lt_trichotomy Q p with hlt | heq | hgt
  · exact PeriodWords.periodExcept_gcd_one_hole_of_lt hQ hlt hQp h hL1 hfQ hfp
  · exact absurd (heq ▸ dvd_refl Q) hQp
  · exact PeriodWords.periodExcept_gcd_one_hole hQ hp hQp hpQ h
      (by have : max Q p = Q := max_eq_left hgt.le
          omega) hfQ hfp

/-- The gcd `g = gcd Q p` of the periods divides `N = r p`, `Q` and the width `u = N - m Q`. -/
theorem gcd_dvd_data {p Q N r m u : ℕ} (hNp : N = r * p) (hNQ : N = m * Q + u) :
    (Nat.gcd Q p : ℤ) ∣ N ∧ (Nat.gcd Q p : ℤ) ∣ Q ∧ (Nat.gcd Q p : ℤ) ∣ u := by
  have hgN : (Nat.gcd Q p : ℤ) ∣ N := by
    rw [hNp]
    push_cast
    exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right Q p)) _
  have hgQ : (Nat.gcd Q p : ℤ) ∣ Q := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left Q p)
  refine ⟨hgN, hgQ, ?_⟩
  have : (u : ℤ) = N - m * Q := by omega
  rw [this]
  exact dvd_sub hgN (dvd_mul_of_dvd_right hgQ _)

/-- **`lem:gluing-periods` (i), empty root against a full period.**  A word of the positions
`1, …, N - 1` with period `p` except at the residue zero (`N = r p`, `r ≥ 2`) and a full period
`Q` (`N = m Q + u`, `1 ≤ u < Q`, `m ≥ 2`, neither period dividing the other) has the full period
`gcd Q p`. -/
theorem periodExcept_gcd_empty_full {α : Type*} {f : ℤ → α} {p Q N r m u : ℕ} (hp : 0 < p)
    (hQ : 0 < Q) (hr : 2 ≤ r) (hm : 2 ≤ m) (hu1 : 1 ≤ u) (hNp : N = r * p)
    (hNQ : N = m * Q + u) (hpQ : ¬ p ∣ Q) (hQp : ¬ Q ∣ p)
    (hfp : PeriodWords.PeriodExcept (N - 1) p {0} f)
    (hfQ : PeriodWords.PeriodExcept (N - 1) Q ∅ f) :
    PeriodWords.PeriodExcept (N - 1) (Nat.gcd Q p) ∅ f := by
  have hmQ : 2 * Q ≤ m * Q := Nat.mul_le_mul_right Q hm
  have hrp : 2 * p ≤ r * p := Nat.mul_le_mul_right p hr
  exact periodExcept_gcd_full_hole hQ hp hQp hpQ 0 (by omega) (by omega) hfQ hfp

end SmallOverlap
end GluingCore
