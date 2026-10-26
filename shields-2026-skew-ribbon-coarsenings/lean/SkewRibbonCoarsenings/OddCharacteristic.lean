/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.RibbonExpansion
import SkewRibbonCoarsenings.MainTheorems

/-!
# Ribbon equality in odd characteristic

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, sections `sec:depth` and `sec:realization`
(`cor:odd-characteristic`, `rem:exact-scope`).

`modq q` is reduction of coefficients modulo `q`, `Λ_ℤ → Λ_{𝔽_q}`.  `odd_characteristic` is
`cor:odd-characteristic`: for `q ≥ 3` (in particular an odd prime), two individual ribbon Schur
functions have equal images in `Λ_{ZMod q} = ZMod q[h₁, h₂, …]` exactly when they are equal over
`ℤ`.  The coefficient of `h_n` in `eq:ribbon-expansion` (`coeff_ribbon_single`) first forces the
weight and the parity of the length, the sign twist then cancels, and the modular clause of
`thm:main-recognition` finishes.

**Conditional on one hypothesis.**  The nontrivial direction of `odd_characteristic` carries the
explicit hypothesis `hrec : ModularRecognition q`, which is verbatim the modular clause
`eq:main-modular` of `thm:main-recognition` for the prime `q`: for every `n ≥ 1` and every pair of
compositions of weight `n`, `G_β^{[≤ B(n)]} ≡ G_γ^{[≤ B(n)]} (mod q)` coefficientwise if and only if
`G_β = G_γ`.  `modularRecognition_of_localAlternative` derives it from `main_modular` of `MainTheorems` given
`LocalAlternativeB` (`prop:local-alternative` for the budget `B`), so the final assembly supplies
`hrec` by `modularRecognition_of_localAlternative localAlternativeB`.

`exact_scope_unsigned` and `exact_scope_signed` are the example of `rem:exact-scope`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open MvPolynomial Finset

/-- Reduction of the coefficients of `Λ_ℤ` modulo `q`. -/
noncomputable def modq (q : ℕ) : Lam →+* MvPolynomial ℕ+ (ZMod q) :=
  MvPolynomial.map (Int.castRingHom (ZMod q))

lemma coeff_modq (q : ℕ) (f : Lam) (d : ℕ+ →₀ ℕ) :
    (modq q f).coeff d = ((f.coeff d : ℤ) : ZMod q) := by
  simp [modq, MvPolynomial.coeff_map]

/-- `eq:main-modular` for the modulus `q` (the modular clause of `thm:main-recognition`): for every
`n ≥ 1` and every pair of compositions of weight `n`, the truncations `G^{[≤ B(n)]}` of the two
coarsening polynomials are congruent modulo `q` coefficientwise if and only if the polynomials are
equal.  This is the single hypothesis of `odd_characteristic`. -/
def ModularRecognition (q : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ S S' : Finset ℕ, IsCutSet n S → IsCutSet n S' →
    (PolyCongr q (truncLT (arithBound n + 1) (G n S)) (truncLT (arithBound n + 1) (G n S')) ↔
      G n S = G n S')

lemma polyCongr_truncLT {q s : ℕ} {f g : Lam} (h : PolyCongr q f g) :
    PolyCongr q (truncLT s f) (truncLT s g) := by
  intro d
  rw [coeff_truncLT, coeff_truncLT]
  split_ifs
  · exact h d
  · simp

lemma polyCongr_of_modq {q : ℕ} {f g : Lam} (h : ∀ d, ((f.coeff d : ℤ) : ZMod q) = (g.coeff d : ℤ)) :
    PolyCongr q f g := by
  intro d
  have := h d
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  exact this

/-- The coefficient of `h_n` in `eq:ribbon-expansion` over `𝔽_q`: equal images of two ribbon
functions force equal weights and `(-1)^{ℓ(β)} = (-1)^{ℓ(γ)}` in `ZMod q`, so equal parity of the
lengths when `q` is odd. -/
lemma weight_sign_of_modq_eq {q : ℕ} (hq : 3 ≤ q) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n' S')
    (h : modq q (ribbon n S) = modq q (ribbon n' S')) :
    n = n' ∧ ((-1 : ZMod q)) ^ S.card = (-1) ^ S'.card := by
  have : Fact (1 < q) := ⟨by omega⟩
  have hcn := congrArg (fun f => f.coeff (Finsupp.single (Nat.toPNat n hn) 1)) h
  simp only [coeff_modq] at hcn
  rw [coeff_ribbon_single hn hS hn, coeff_ribbon_single hn' hS' hn] at hcn
  by_cases hne : n = n'
  · subst hne
    rw [if_pos rfl, if_pos rfl] at hcn
    exact ⟨rfl, by exact_mod_cast hcn⟩
  · rw [if_pos rfl, if_neg hne] at hcn
    have h0 : ((-1 : ZMod q)) ^ S.card = 0 := by exact_mod_cast hcn
    exact absurd h0 ((isUnit_one.neg.pow _).ne_zero)

/-- `cor:odd-characteristic`: for `q ≥ 3` (in particular for an odd prime `q`), two ribbon Schur
functions become equal over `𝔽_q` if and only if they were equal over `ℤ`.  The compositions are
given by weight and cut set (weights `n, n' ≥ 1`), and the weights are not assumed equal.

The coefficient of `h_n` in `eq:ribbon-expansion` is `(-1)^{|S|}` (`coeff_ribbon_single`), nonzero
modulo `q`; so it forces equal weights and, as `1 ≠ -1` in odd characteristic, equal length parity.
Equal parity cancels the sign twist `𝒜`, giving `G_β ≡ G_γ (mod q)` coefficientwise.  The
hypothesis `hrec` (`eq:main-modular`, the modular clause of `thm:main-recognition`) turns this into
`G_β = G_γ`, and `ribbon_eq_iff` into equality of the ribbon functions.  This is not an assertion
about linear combinations of ribbons.

**Conditional on** `hrec : ModularRecognition q`. -/
theorem odd_characteristic {q : ℕ} (hq : 3 ≤ q) (hrec : ModularRecognition q) {n n' : ℕ}
    (hn : 1 ≤ n) (hn' : 1 ≤ n') {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    modq q (ribbon n S) = modq q (ribbon n' S') ↔ ribbon n S = ribbon n' S' := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have : Fact (1 < q) := ⟨by omega⟩
  obtain ⟨hweight, hpar⟩ := weight_sign_of_modq_eq hq hn hn' hS hS' h
  subst hweight
  have hpoly : PolyCongr q (G n S) (G n S') := by
    refine polyCongr_of_modq fun d => ?_
    have hd := congrArg (fun f => f.coeff d) h
    simp only [coeff_modq, coeff_ribbon hn hS, coeff_ribbon hn hS'] at hd
    push_cast at hd
    rw [pow_add, pow_add, pow_add, pow_add, ← hpar] at hd
    have hu : IsUnit (((-1 : ZMod q)) ^ S.card * (-1) ^ 1 * (-1) ^ d.degree) :=
      ((isUnit_one.neg.pow _).mul (isUnit_one.neg.pow _)).mul (isUnit_one.neg.pow _)
    exact (hu.mul_right_inj).mp (by simpa [mul_assoc] using hd)
  have hG : G n S = G n S' := (hrec n hn S S' hS hS').mp (polyCongr_truncLT hpoly)
  exact (ribbon_eq_iff hn hS hS').mpr hG

/-- `cor:odd-characteristic` for an odd prime `q`.  **Conditional on**
`hrec : ModularRecognition q`. -/
theorem odd_characteristic_prime {q : ℕ} (hqp : q.Prime) (hq2 : q ≠ 2)
    (hrec : ModularRecognition q) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') {S S' : Finset ℕ}
    (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    modq q (ribbon n S) = modq q (ribbon n' S') ↔ ribbon n S = ribbon n' S' :=
  odd_characteristic (by have := hqp.two_le; omega) hrec hn hn' hS hS'

/-- The hypothesis `ModularRecognition q` of `odd_characteristic` follows from the local alternative
`prop:local-alternative` for the budget `B`, by `eq:main-modular` (`main_modular`). -/
theorem modularRecognition_of_localAlternative (hLA : LocalAlternativeB) {q : ℕ} (hq : 3 ≤ q) :
    ModularRecognition q :=
  fun _ hn _ _ hS hS' => main_modular hLA hq hn hS hS'

/-- `cor:odd-characteristic`, conditional only on `prop:local-alternative` for the budget `B`. -/
theorem odd_characteristic_of_localAlternative (hLA : LocalAlternativeB) {q : ℕ} (hq : 3 ≤ q)
    {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n' S') :
    modq q (ribbon n S) = modq q (ribbon n' S') ↔ ribbon n S = ribbon n' S' :=
  odd_characteristic hq (modularRecognition_of_localAlternative hLA hq) hn hn' hS hS'

/-! ### `rem:exact-scope`: unsigned versus signed discrepancies -/

lemma G_two_one : G 2 {1} = hgen 2 + hgen 1 * hgen 1 := by
  have e : (({1} : Finset ℕ).powerset.val.map (gaps 2)) = {{2}, {1, 1}} := by decide
  rw [G_eq_sum, e]
  simp

/-- `rem:exact-scope`, unsigned side: the unsigned pair `(1,1)`, `(2)` has equal coefficients below
ordinary degree two (`G_{(1,1)} - G_{(2)}` has no monomial of ordinary degree `< 2`) and first
differs in degree two: the first distinguishing depth is `2`. -/
theorem exact_scope_unsigned : G 2 {1} ≠ G 2 ∅ ∧ dep 2 {1} ∅ = 2 := by
  have hS : IsCutSet 2 {1} := by unfold IsCutSet; decide
  have hS' : IsCutSet 2 ∅ := Finset.empty_subset _
  have hlow : ordGE 2 (G 2 {1} - G 2 ∅) := by
    rw [G_two_one, G_empty]
    have : hgen 2 + hgen 1 * hgen 1 - hgen 2 = hgen 1 * hgen 1 := by ring
    rw [this]
    have h1 : ordGE 1 (hgen 1) := by
      rw [show hgen 1 = MvPolynomial.X 1 by simp [hgen]]
      exact ordGE_X _
    exact ordGE_mul h1 h1
  exact dep_eq_of_witness (by norm_num) hS hS' hlow ⟨{1, 1}, by decide, by decide⟩
    (by decide) rfl

/-- `rem:exact-scope`, signed side: the coefficient of `h_2` in the ribbon Schur functions
`r_{(1,1)}` and `r_{(2)}` is `-1` and `+1`, so their signed difference already has an `h_2` term
(ordinary degree one), although the unsigned pair first differs in degree two.  The coefficient of
`h_n` records the parity of the composition length. -/
theorem exact_scope_signed :
    (ribbon 2 {1}).coeff (Finsupp.single (Nat.toPNat 2 (by norm_num)) 1) = -1 ∧
    (ribbon 2 ∅).coeff (Finsupp.single (Nat.toPNat 2 (by norm_num)) 1) = 1 := by
  have hS : IsCutSet 2 {1} := by unfold IsCutSet; decide
  have hS' : IsCutSet 2 ∅ := Finset.empty_subset _
  refine ⟨?_, ?_⟩
  · rw [coeff_ribbon_single (by norm_num) hS (by norm_num)]
    simp
  · rw [coeff_ribbon_single (by norm_num) hS' (by norm_num)]
    simp

end SkewRibbonCoarsenings
