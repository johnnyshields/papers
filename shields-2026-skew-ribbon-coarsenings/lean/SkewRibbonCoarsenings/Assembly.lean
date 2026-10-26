/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.MainTheorems
import SkewRibbonCoarsenings.LocalAlternativeProof
import SkewRibbonCoarsenings.OddCharacteristic
import SkewRibbonCoarsenings.Recovery
import SkewRibbonCoarsenings.Normalization
import SkewRibbonCoarsenings.Support

/-!
# The main theorems, unconditionally

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, the introduction (`thm:main-recognition`,
`thm:main-structure`, `thm:main-depth`, `eq:REV`, `eq:frontier`), the recognition section
(`eq:congruence`, `cor:class`'s inclusion `⊇`, `cor:modular-budget`), `eq:two-factor-cancel` and
`cor:odd-characteristic`.

The recognition modules carry `prop:local-alternative` as an explicit hypothesis, and
`LocalAlternativeProof` proves it for both budgets (`localAlternativeB`, `localAlternativeOmega`).
This module applies the proof, so each headline statement below has no hypothesis beyond the
paper's own parameters.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

/-- `thm:main-structure`: `G_β = G_γ`, `Ψ_β = Ψ_γ` and the existence of a factor-reversal witness
are equivalent. -/
theorem thm_main_structure {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') {S S' : Finset ℕ}
    (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    List.TFAE [G n S = G n' S', Psi n S = Psi n' S', n = n' ∧ FactorWitness n S S'] :=
  main_structure localAlternativeOmega hn hn' hS hS'

/-- `eq:congruence`: inventory equivalence is a two-sided congruence for `∘`. -/
theorem eq_congruence {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {A A' E E' : Finset ℕ}
    (hA : IsCutSet m A) (hA' : IsCutSet m A') (hE : IsCutSet n E) (hE' : IsCutSet n E')
    (hα : G m A = G m A') (hβ : G n E = G n E') :
    G (m * n) (compCuts m A n E) = G (m * n) (compCuts m A' n E') :=
  congruence localAlternativeOmega hm hn hA hA' hE hE' hα hβ

/-- `eq:REV`: equal inventories have equal near-power inventories. -/
theorem eq_REV {n m : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (h : G n S = G n S') :
    G (m * n) (nearPowerCuts n S m) = G (m * n) (nearPowerCuts n S' m) :=
  REV localAlternativeOmega hn hS hS' h

/-- `eq:two-factor-cancel`: for products with the same two factor weights, `α ∘ β ∼ α' ∘ β'` if and
only if `α ∼ α'` and `β ∼ β'`. -/
theorem eq_two_factor_cancel {m n : ℕ} {A A' E E' : Finset ℕ} (hm : 0 < m) (hn : 0 < n)
    (hA : IsCutSet m A) (hA' : IsCutSet m A') (hE : IsCutSet n E) (hE' : IsCutSet n E') :
    Equivalent (m * n) (compCuts m A n E) (compCuts m A' n E') ↔
      Equivalent m A A' ∧ Equivalent n E E' :=
  two_factor_cancel_iff hm hn hA hA' hE hE'
    (fun h1 h2 => eq_congruence hm hn hA hA' hE hE' h1 h2)

/-- `thm:main-recognition`: for compositions of weight `n`, exactly one of equal inventories and a
short certificate holds, and `B(n) ≤ Ω(n) + 2`. -/
theorem thm_main_recognition {n : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') :
    Xor (G n S = G n S') (∃ lam, CoarseCertificate arithBound n S S' lam) ∧
      arithBound n ≤ ArithmeticFunction.cardFactors n + 2 :=
  main_recognition localAlternativeB hn hS hS'

/-- `eq:main-modular`: for every `q ≥ 3`, congruence of the truncations through ordinary degree
`B(n)` modulo `q` is equivalent to equality of the inventories. -/
theorem eq_main_modular {q : ℕ} (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ}
    (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    PolyCongr q (truncLT (arithBound n + 1) (G n S)) (truncLT (arithBound n + 1) (G n S')) ↔
      G n S = G n S' :=
  main_modular localAlternativeB hq hn hS hS'

/-- `thm:main-depth`, `eq:frontier`: the cumulative distinguishing depth. -/
theorem thm_main_depth :
    cumDepth 1 = 0 ∧ (∀ N, 2 ≤ N → N ≤ 4 → cumDepth N = 2) ∧
      (∀ N, 5 ≤ N → N ≤ 11 → cumDepth N = 3) ∧
      ∀ j N : ℕ, 12 * 6 ^ j ≤ N → N < 72 * 6 ^ j →
        cumDepth N = 2 * j + 4 + (if 30 * 6 ^ j ≤ N then 1 else 0) :=
  frontier localAlternativeB

/-- `thm:main-depth`, the modular clause: the cumulative frontier is sharp for the modular tests,
for every `q ≥ 3`. -/
theorem thm_main_depth_modular {q : ℕ} (hq : 3 ≤ q) {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N)
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    PolyCongr q (truncLT (uBound N + 1) (G n S)) (truncLT (uBound N + 1) (G n S')) ↔
      G n S = G n S' :=
  modular_frontier localAlternativeB hq hn hnN hS hS'

/-- `cor:odd-characteristic`: over `𝔽_q`, `q` an odd prime, two ribbon Schur functions become
equal if and only if they were equal over `ℤ`. -/
theorem cor_odd_characteristic {q : ℕ} (hq : 3 ≤ q) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    modq q (ribbon n S) = modq q (ribbon n' S') ↔ ribbon n S = ribbon n' S' :=
  odd_characteristic_of_localAlternative localAlternativeB hq hn hn' hS hS'


/-- `prop:normalization`: two compositions of weight `n` with equal two-block inventories and
`eq:FE` that are neither identical nor reversed are in the normalized setting, after orienting the
second.  The support-separation input is `supportSeparation` (`thm:support`). -/
theorem prop_normalization {n : ℕ} {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (h2 : TwoBlockEq n S S') (hfe : FEq (uFun n S S') (vFun n S S')) (hid : S ≠ S')
    (hrev : S' ≠ revCuts n S) :
    ∃ S'' : Finset ℕ, (S'' = S' ∨ S'' = revCuts n S') ∧ ∃ d e : ℕ, NormalizedSetting n S S'' d e :=
  normalization supportSeparation hS hS' h2 hfe hid hrev

/-- `thm:coarse`: for compositions of weight `n`, exactly one of a factor-reversal witness (with
equal substitution maps) and a certificate of magnitude one or two with at most `Ω(n) + 2` blocks
holds. -/
theorem thm_coarse {n : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') :
    Xor (FactorWitness n S S' ∧ Psi n S = Psi n S')
      (∃ lam, CoarseCertificate (fun n => ArithmeticFunction.cardFactors n + 2) n S S' lam) :=
  coarse_recognition localAlternativeOmega hn hS hS'

/-- `prop:budget`: `thm:coarse` with any budget `H` that is monotone under divisibility and
covers the detectors (`BudgetCovers H`) in place of `Ω(n) + 2`. -/
theorem prop_budget {H : ℕ → ℕ} (hH : MonotoneDvd H) (hc : BudgetCovers H) {n : ℕ} (hn : 1 ≤ n)
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    Xor (FactorWitness n S S' ∧ Psi n S = Psi n S') (∃ lam, CoarseCertificate H n S S' lam) :=
  budget_recognition hH (localAlternative_of_covers hc) hn hS hS'

/-- `cor:modular-budget`: under a budget `H` as in `prop:budget`, ordinary inventory coefficients
through `H(n)` modulo any `q ≥ 3` determine the complete inventory. -/
theorem cor_modular_budget {H : ℕ → ℕ} (hH : MonotoneDvd H) (hc : BudgetCovers H) {q : ℕ}
    (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') :
    (∀ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) → lam.sum = n → Multiset.card lam ≤ H n →
        (q : ℤ) ∣ (mult n S lam : ℤ) - mult n S' lam) ↔ G n S = G n S' :=
  modular_budget hH (localAlternative_of_covers hc) hq hn hS hS'

/-- `rem:shallow-induction`: shallow congruence of the outer pair, transferred from a composition
product with a common inner factor, gives equality of the outer inventories. -/
theorem rem_shallow_induction {H : ℕ → ℕ} (hH : MonotoneDvd H) (hc : BudgetCovers H) {m p : ℕ}
    {A A' E : Finset ℕ} (hm : 1 ≤ m) (hp : 0 < p) (hA : IsCutSet m A) (hA' : IsCutSet m A')
    (hE : IsCutSet p E)
    (h : ∀ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) → lam.sum = m * p → Multiset.card lam ≤ H (m * p) →
      mult (m * p) (compCuts m A p E) lam = mult (m * p) (compCuts m A' p E) lam) :
    G m A = G m A' :=
  shallow_induction hH (localAlternative_of_covers hc) hm hp hA hA' hE h

end SkewRibbonCoarsenings
