/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Seam
import SkewRibbonCoarsenings.Setting
import SkewRibbonCoarsenings.Labels
import SkewRibbonCoarsenings.ArithmeticBound

/-!
# The local alternative: the interface between detection and recognition

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, sections `sec:realization` and `sec:recognition`
(`prop:local-alternative`, `eq:common-factor`, `eq:coarse-local-budget`).

`LocalAlternative H` is the exact content of `prop:local-alternative` for a budget function
`H : ℕ → ℕ` (the largest number of blocks a detector may use at weight `n`): for two compositions of
weight `n`, either they are identical or reversed, or after orientation they have a proper literal
common inner factor (`eq:common-factor`), or some ordinary coefficient differs by one or two at a
partition with at most `H n` parts and distinct parts except possibly one pair.  It is the single
conditional interface of the recognition and main-theorem modules: they carry `hLA : LocalAlternative H`
as an explicit hypothesis, and it is proved from the detector and realization machinery.

`LocalAlternativeOmega` is `H n = Ω(n) + 2`, `LocalAlternativeB` is `H = B`
(`arithBound`); the latter implies the former (`LocalAlternativeB.toOmega`).  Sorry-free.
-/

namespace SkewRibbonCoarsenings

/-- `eq:coarse-certificate`: `lam` is a coarse certificate that the compositions of weight `n` with
cut sets `S, S'` are distinguished by the budget `H`: a partition of `n` with at most `H n` parts,
an ordinary coefficient difference `Δm ∈ {-2, -1, 1, 2}`, and distinct parts except possibly one
repeated pair. -/
def CoarseCertificate (H : ℕ → ℕ) (n : ℕ) (S S' : Finset ℕ) (lam : Multiset ℕ) : Prop :=
  (∀ x ∈ lam, 0 < x) ∧ lam.sum = n ∧ Multiset.card lam ≤ H n ∧
    ((mult n S lam : ℤ) - mult n S' lam ∈ ({-2, -1, 1, 2} : Set ℤ)) ∧ DistinctExceptPair lam

/-- `prop:local-alternative`, for the budget `H`.  For cut sets `S, S'` of weight `n`, one of:

* `S = S'`, or `S' = S*` (identical or reversed);
* a proper literal common inner factor after orientation (`eq:common-factor`): an inner weight `p`
  with `3 ≤ p`, `p ∣ n`, and an inner cut set `E` of weight `p` with
  `S = compCuts (n / p) A p E` and `S'' = compCuts (n / p) A' p E` for an
  orientation `S''` of `S'` (`S'` itself or `S'*`), the outer cut sets `A, A'`
  having weight `n / p`; the inner size obeys `3 ≤ p ≤ d < n`, where
  `d = gcd(n, supp v)` is the divisor of `eq:gcd-normalization` for the oriented pair `S, S''`
  (`v = b - c` of `eq:uv`), so `p ∣ d ∣ n`;
* a coarse certificate `CoarseCertificate H n S S' λ`.

At weights `n ≤ 4` the detectors of the paper do not apply; the statement is proved there by the
two-block argument of `prop:budget` (at weights at most four, two-block data fix every symmetric cut
pair and the midpoint, with at most one asymmetric reflected pair left, whose two orientations are
global reversals), and weight one has a single composition.  The statement has no hypothesis
`1 ≤ n`: at `n = 0` it is the first alternative. -/
def LocalAlternative (H : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (S S' : Finset ℕ), IsCutSet n S → IsCutSet n S' →
    S' = S ∨ S' = revCuts n S ∨
    (∃ (p d : ℕ) (A A' E S'' : Finset ℕ), 3 ≤ p ∧ p ∣ d ∧ p ≤ d ∧ d ∣ n ∧ d < n ∧
        IsCutSet (n / p) A ∧ IsCutSet (n / p) A' ∧ IsCutSet p E ∧
        S = compCuts (n / p) A p E ∧ (S'' = S' ∨ S'' = revCuts n S') ∧
        S'' = compCuts (n / p) A' p E ∧ d = supportGcd (vFun n S S'')) ∨
    ∃ lam : Multiset ℕ, CoarseCertificate H n S S' lam

/-- `prop:local-alternative` with the budget `H(n) = Ω(n) + 2` of `eq:coarse-local-budget`. -/
def LocalAlternativeOmega : Prop :=
  LocalAlternative (fun n => ArithmeticFunction.cardFactors n + 2)

/-- `prop:local-alternative` with the arithmetic budget `H = B` of `def:arithmetic-bound`. -/
def LocalAlternativeB : Prop := LocalAlternative arithBound

/-- `H` is monotone under divisibility on positive integers (the hypothesis of `prop:budget`). -/
def MonotoneDvd (H : ℕ → ℕ) : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m ∣ n → H m ≤ H n

/-- `prop:budget`: the budget `Ω(n) + 2` is monotone under divisibility. -/
theorem monotoneDvd_omega : MonotoneDvd (fun n => ArithmeticFunction.cardFactors n + 2) := by
  intro m n hm hn hmn
  obtain ⟨k, rfl⟩ := hmn
  have hk : k ≠ 0 := by rintro rfl; omega
  have := ArithmeticFunction.cardFactors_mul (by omega : m ≠ 0) hk
  show ArithmeticFunction.cardFactors m + 2 ≤ ArithmeticFunction.cardFactors (m * k) + 2
  omega

/-- `prop:budget`: the arithmetic budget `B` is monotone under divisibility. -/
theorem monotoneDvd_arithBound : MonotoneDvd arithBound :=
  fun _ _ hm hn h => arithBound_mono hm hn h

/-- A larger budget keeps the alternative. -/
theorem LocalAlternative.mono {H H' : ℕ → ℕ} (hHH : ∀ n, 1 ≤ n → H n ≤ H' n)
    (h : LocalAlternative H) : LocalAlternative H' := by
  intro n S S' hS hS'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    have e : (Finset.Ioo 0 0 : Finset ℕ) = ∅ := Finset.Ioo_self 0
    have h1 : S = ∅ := Finset.subset_empty.mp (e ▸ hS)
    have h2 : S' = ∅ := Finset.subset_empty.mp (e ▸ hS')
    rw [h1, h2]
  · rcases h n S S' hS hS' with h1 | h1 | h1 | ⟨lam, hp, hs, hc, hm, hd⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr ⟨lam, hp, hs, hc.trans (hHH n hn), hm, hd⟩))

/-- The arithmetic budget `B` is at most `Ω + 2`, so `LocalAlternativeB` implies
`LocalAlternativeOmega`. -/
theorem LocalAlternativeB.toOmega (h : LocalAlternativeB) : LocalAlternativeOmega :=
  LocalAlternative.mono (fun _ hn => arithBound_le_Omega_add_two hn) h

end SkewRibbonCoarsenings
