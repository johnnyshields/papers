/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.SmallWeights
import SkewRibbonCoarsenings.DetectorBudget
import SkewRibbonCoarsenings.Termination
import SkewRibbonCoarsenings.Support
import SkewRibbonCoarsenings.Normalization
import SkewRibbonCoarsenings.LowOrder
import SkewRibbonCoarsenings.FourStart
import SkewRibbonCoarsenings.Nonlinear

/-!
# Proof of the local alternative

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:realization`
(`prop:local-alternative`, `eq:coarse-local-budget`).

`localAlternative_of_budget` proves `LocalAlternative H` for every budget `H` covering the
detector blocks; `localAlternativeB` and `localAlternativeOmega` are the two budgets of the paper.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Nested

section Assembly

/-- The coverage of detector blocks that a budget must provide (`prop:budget`): three blocks at
weight `n ≥ 5`, two blocks for `2 ≤ n`, and `L + 4` blocks after `L` strict increases (`L = 0`
for the starting mask) in a normalized setting. -/
structure BudgetCovers (H : ℕ → ℕ) : Prop where
  two : ∀ n, 2 ≤ n → 2 ≤ H n
  three : ∀ n, 5 ≤ n → 3 ≤ H n
  start : ∀ {n S S' d e}, NormalizedSetting n S S' d e → 4 ≤ e → 4 ≤ H n
  chain : ∀ {n S S' d e L p}, NormalizedSetting n S S' d e → MaskChain n S d e L p →
    LeastChain n S L p → 4 ≤ e → L + 4 ≤ H n

theorem budgetCovers_arithBound : BudgetCovers arithBound where
  two n hn := two_le_arithBound hn
  three n hn := three_le_arithBound hn
  start h he := four_blocks_le_arithBound h he
  chain {n S S' d e L p} h hc hl he := by
    haveI : NeZero n := ⟨(h.n_pos).ne'⟩
    exact chain_blocks_le_arithBound h hc hl he

theorem budgetCovers_omega : BudgetCovers (fun n => ArithmeticFunction.cardFactors n + 2) where
  two n hn := by
    have : 0 < ArithmeticFunction.cardFactors n :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
    omega
  three n hn := by
    have : 0 < ArithmeticFunction.cardFactors n :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
    show 3 ≤ _
    omega
  start h _ := by
    have := omega_budget_le h.n_pos.ne' h.e_dvd_d h.d_dvd_n h.three_le_e h.three_le_ratio
    show 4 ≤ _
    omega
  chain h hc _ _ := chain_blocks_le_omega h hc

/-- A positive labeled list of total `n` with `0 < |ΔK| ≤ 2` gives a coarse certificate. -/
theorem cert_of_list {H : ℕ → ℕ} {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') {r : ℕ} (a : Fin r → ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hr : r ≤ H n) (h0 : (K S a : ℤ) - K S' a ≠ 0) (h2 : |(K S a : ℤ) - K S' a| ≤ 2) :
    ∃ lam : Multiset ℕ, CoarseCertificate H n S S' lam := by
  obtain ⟨hm, hd⟩ := labeled_diff_small hn hS hS' a ha hsum h0 h2
  refine ⟨sortParts a, fun x hx => ?_, ?_, ?_, hm, hd⟩
  · obtain ⟨i, _, rfl⟩ := Multiset.mem_map.1 hx
    exact ha i
  · unfold sortParts; rw [← Finset.sum_eq_multiset_sum]; exact hsum
  · simpa [sortParts] using hr

lemma pair_distinct (p q : ℕ) : DistinctExceptPair ({p, q} : Multiset ℕ) := by
  refine ⟨fun j => (Multiset.count_le_card j _).trans (by simp), ?_⟩
  apply Finset.card_le_one.2
  intro a ha b hb
  have key : ∀ j, ({p, q} : Multiset ℕ).count j = 2 → j = p ∧ j = q := by
    intro j hj
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hj
    split_ifs at hj <;> simp_all
  have h1 := key a (Finset.mem_filter.1 ha).2
  have h2 := key b (Finset.mem_filter.1 hb).2
  omega

/-- `mult` is invariant under reversal. -/
lemma mult_revCuts_eq {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) {lam : Multiset ℕ}
    (hlam : ∀ x ∈ lam, 0 < x) : mult n (revCuts n S) lam = mult n S lam := by
  have h1 := coeff_G hn (revCuts_isCutSet hS) lam hlam
  have h2 := coeff_G hn hS lam hlam
  rw [G_revCuts n S hS] at h1
  exact_mod_cast h1.symm.trans h2

lemma cert_transfer {H : ℕ → ℕ} {n : ℕ} (hn : 0 < n) {S S' S'' : Finset ℕ} (hS' : IsCutSet n S')
    (hor : S'' = S' ∨ S'' = revCuts n S') {lam : Multiset ℕ}
    (h : CoarseCertificate H n S S'' lam) : CoarseCertificate H n S S' lam := by
  rcases hor with rfl | rfl
  · exact h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨h1, h2, h3, ?_, h5⟩
    rwa [mult_revCuts_eq hn hS' h1] at h4

/-- `prop:local-alternative`: the local alternative for every budget covering the detector
blocks. -/
theorem localAlternative_of_covers {H : ℕ → ℕ} (hc : BudgetCovers H) : LocalAlternative H := by
  intro n S S' hS hS'
  by_cases hn4 : n ≤ 4
  · exact (small_alternative hn4 (hc.two n) hS hS').imp id (fun h => h.imp id
      (fun h => Or.inr h))
  have hn5 : 5 ≤ n := by omega
  have hn : 0 < n := by omega
  by_cases hid : S' = S
  · exact Or.inl hid
  by_cases hrev : S' = revCuts n S
  · exact Or.inr (Or.inl hrev)
  right; right
  by_cases h2 : TwoBlockEq n S S'
  swap
  · right
    simp only [TwoBlockEq, not_forall] at h2
    obtain ⟨p, q, hp, hq, hpq, hne⟩ := h2
    have a1 := mult_two_le hS hp hq hpq
    have a2 := mult_two_le hS' hp hq hpq
    refine ⟨{p, q}, ?_, ?_, ?_, ?_, pair_distinct p q⟩
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      omega
    · simpa using hpq
    · have := hc.two n (by omega); simp; omega
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  have htau := tau_eq_of_twoBlockEq hn hS hS' h2
  have htau' : ∀ x : ZMod n, cutInd n S x + cutInd n S (-x) =
      cutInd n S' x + cutInd n S' (-x) := htau
  by_cases hfe : FEq (uFun n S S') (vFun n S S')
  swap
  · right
    have hex : ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = n ∧
        triangleSum (uFun n S S') (vFun n S S') (a : ZMod n) (b : ZMod n) (c : ZMod n) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hfe (fe_of_triangle_zero (uFun_odd htau') (vFun_odd htau') (uFun_mul_vFun htau') hn
        (fun a b c ha hb hc' habc => hcon a b c ha hb hc' habc))
    obtain ⟨a, b, c, ha, hb, hc', habc, hne⟩ := hex
    have hlist : ∀ i, 0 < (![a, b, c] : Fin 3 → ℕ) i := by
      intro i; fin_cases i <;> simpa
    have hsum : ∑ i, (![a, b, c] : Fin 3 → ℕ) i = n := by
      rw [Fin.sum_univ_three]; simpa using habc
    have h3 := three_difference hS hS' htau' hlist hsum
    have hlab : ∀ i, lab n ![a, b, c] i = ((![a, b, c] : Fin 3 → ℕ) i : ZMod n) := fun i => rfl
    rw [hlab 0, hlab 1, hlab 2] at h3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h3
    have hD0 : (K S ![a, b, c] : ℤ) - K S' ![a, b, c] ≠ 0 := by
      rw [h3]; exact neg_ne_zero.mpr hne
    have hD2 : |(K S ![a, b, c] : ℤ) - K S' ![a, b, c]| ≤ 2 := by
      rw [h3, abs_neg]
      exact triangleSum_abs_le (fun x => uFun_ternary S S' x) (fun x => vFun_ternary S S' x)
        (uFun_mul_vFun (fun x => htau x)) _ _ _
    exact cert_of_list hn hS hS' _ hlist hsum (by have := hc.three n hn5; simpa using this) hD0 hD2
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨S'', hor, d, e, hN⟩ := normalization supportSeparation hS hS' h2 hfe (Ne.symm hid) hrev
  have hn9 := setting_nine_le hN
  have hS'' : IsCutSet n S'' := hN.cuts'
  have hfin : ∀ (p : ℕ) (A A' E : Finset ℕ), 3 ≤ p → p ∣ d → p ∣ n → IsCutSet (n / p) A →
      IsCutSet (n / p) A' → IsCutSet p E → S = compCuts (n / p) A p E →
      S'' = compCuts (n / p) A' p E →
      (∃ (p d : ℕ) (A A' E S'' : Finset ℕ), 3 ≤ p ∧ p ∣ d ∧ p ≤ d ∧ d ∣ n ∧ d < n ∧
        IsCutSet (n / p) A ∧ IsCutSet (n / p) A' ∧ IsCutSet p E ∧
        S = compCuts (n / p) A p E ∧ (S'' = S' ∨ S'' = revCuts n S') ∧
        S'' = compCuts (n / p) A' p E ∧ d = supportGcd (vFun n S S'')) := by
    intro p A A' E h3 hpd _ hA hA' hE h1 h2
    exact ⟨p, d, A, A', E, S'', h3, hpd, Nat.le_of_dvd hN.d_pos hpd, hN.d_dvd_n, hN.d_lt, hA, hA',
      hE, h1, hor, h2, hN.d_eq⟩
  by_cases he3 : e = 3
  · left
    subst he3
    obtain ⟨h3n, -, -, -, -, A, A', E, hA, hA', hE, h1, h2⟩ := ratios_three hN
    exact hfin 3 A A' E le_rfl hN.e_dvd_d h3n hA hA' hE h1 h2
  have he4 : 4 ≤ e := by have := hN.three_le_e; omega
  by_cases hfv : FourBlockVanish n S S'' d
  swap
  · right
    simp only [FourBlockVanish, not_forall] at hfv
    obtain ⟨a, r, s, z, ha, hr, hs, hz, hva, hrd, hsd, hzd, hsum, hne⟩ := hfv
    have hb := four_bound hN ha hr hs hz hva hrd hsd hzd hsum
    have hlist : ∀ i, 0 < (![a, r, s, z] : Fin 4 → ℕ) i := by
      intro i; fin_cases i <;> simpa
    have hsum' : ∑ i, (![a, r, s, z] : Fin 4 → ℕ) i = n := by
      rw [Fin.sum_univ_four]; simpa using hsum
    obtain ⟨lam, hl⟩ := cert_of_list hn hS hS'' _ hlist hsum'
      (by simpa using hc.start hN he4) hne hb
    exact ⟨lam, cert_transfer hn hS' hor hl⟩
  have h0 := mask_periodic_of_four_vanish hN hfv
  rcases termination_or_detector hN h0 with
    ⟨p, A, A', E, h3, -, hpd, hpn, -, hA, hA', hE, h1, h2⟩ | ⟨L, a, r, s, z, y, hcm, hl, hpd⟩
  · left
    exact hfin p A A' E h3 hpd hpn hA hA' hE h1 h2
  · right
    obtain ⟨-, hb, -, hsum⟩ := nested_identity hN hpd.data
    obtain ⟨lam, hl'⟩ := cert_of_list hn hS hS'' _ (fun i => hpd.data.detList_pos i) hsum
      (by simpa using hc.chain hN hcm hl he4) hpd.ne hb
    exact ⟨lam, cert_transfer hn hS' hor hl'⟩

/-- `prop:local-alternative` with the arithmetic budget `B`. -/
theorem localAlternativeB : LocalAlternativeB := localAlternative_of_covers budgetCovers_arithBound

/-- `prop:local-alternative` with the budget `Ω(n) + 2` of `eq:coarse-local-budget`. -/
theorem localAlternativeOmega : LocalAlternativeOmega :=
  localAlternative_of_covers budgetCovers_omega

end Assembly

end SkewRibbonCoarsenings
