/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Recognition
import SkewRibbonCoarsenings.DepthFamilies

/-!
# The main theorems

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, sections `sec:introduction` and `sec:recognition`
(`thm:main-structure`, `eq:congruence`, `eq:REV`, `cor:class`, `thm:main-recognition`,
`eq:main-modular`, `thm:main-depth`, `eq:frontier`, `eq:old-inclusion`).

Every theorem that uses recognition carries the explicit hypothesis `hLA : LocalAlternative H`
(`prop:local-alternative`, see `LocalAlternative.lean`) for the relevant budget `H`
(`Ω(n) + 2` for `thm:main-structure`, `B` for `thm:main-recognition` and `thm:main-depth`).
`LocalAlternativeProof` proves that hypothesis for both budgets, and `Assembly` applies it, so the
statements there carry no such binder.  The inclusion `⊆` of `cor:class` is
`eq:old-inclusion`, taken here as the instance hypothesis `OldInclusion` of `class_subset_of_cited`
and proved for every instance in `ClassInclusion`.  The lower bounds and the modular sharpness of
`thm:main-depth` are unconditional (`modular_sharp_frontier`).  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-! ### Equal inventories force equal weights, and `G = Ψ(h₁)` -/

lemma G_ne_zero {n : ℕ} (hn : 1 ≤ n) {S : Finset ℕ} (hS : IsCutSet n S) : G n S ≠ 0 := by
  intro h
  have := coeff_G (by omega) hS {n} (by simp; omega)
  rw [h, mult_single hS] at this
  simp at this

/-- Compositions with equal coarsening polynomials have equal weight. -/
lemma weight_eq_of_G_eq {n n' : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n' S') (h : G n S = G n' S') : n = n' :=
  (G_isWeightedHomogeneous hS).inj_right (G_ne_zero hn hS) (h ▸ G_isWeightedHomogeneous hS')

/-- `G_β = Ψ_β(h₁)`. -/
lemma G_eq_Psi_hgen_one (n : ℕ) (S : Finset ℕ) : G n S = Psi n S (hgen 1) := by
  rw [Psi_hgen, one_mul]
  simp [nearPowerCuts]

/-! ### `thm:main-structure` -/

/-- `thm:main-structure`: for compositions `β, γ` (weights `n, n'`, cut sets `S, S'`) the following
are equivalent: (1) `G_β = G_γ`; (2) `Ψ_β = Ψ_γ`; (3) the weights agree and there are factorizations
`β = δ₁ ∘ ⋯ ∘ δ_s`, `γ = ε₁ ∘ ⋯ ∘ ε_s` with `ε_i ∈ {δ_i, δ_i*}` (`FactorWitness`).

Conditional on `hLA : LocalAlternative (Ω + 2)`.  The implication (1) ⇒ (3) is the exclusivity in
`thm:coarse`: the certificate alternative is impossible for equal inventories; (3) ⇒ (2) is
`eq:Psi-laws` (`reversal_suffices`); (2) ⇒ (1) is evaluation at `h₁`. -/
theorem main_structure (hLA : LocalAlternativeOmega) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    List.TFAE [G n S = G n' S', Psi n S = Psi n' S', n = n' ∧ FactorWitness n S S'] := by
  tfae_have 1 → 3 := by
    intro h
    have hnn := weight_eq_of_G_eq hn hS hS' h
    subst hnn
    refine ⟨rfl, ?_⟩
    rcases coarse_recognition hLA hn hS hS' with ⟨⟨hw, _⟩, _⟩ | ⟨⟨lam, hpos, _, _, hdiff, _⟩, _⟩
    · exact hw
    · exfalso
      rw [mult_eq_of_G_eq hn hS hS' h hpos] at hdiff
      simp at hdiff
  tfae_have 3 → 2 := by
    rintro ⟨rfl, hw⟩
    exact hw.Psi_eq
  tfae_have 2 → 1 := by
    intro h
    rw [G_eq_Psi_hgen_one, G_eq_Psi_hgen_one n' S', h]
  tfae_finish

/-- `thm:main-structure`, (1) ⇔ (2): equality of inventories is equality of the substitution maps. -/
theorem G_eq_iff_Psi_eq (hLA : LocalAlternativeOmega) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n' S') :
    G n S = G n' S' ↔ Psi n S = Psi n' S' :=
  (main_structure hLA hn hn' hS hS').out 1 2

/-- `thm:main-structure`, (1) ⇔ (3): equality of inventories is the existence of a factor-reversal
witness (the classification of Billera–Thomas–van Willigenburg, reproved). -/
theorem G_eq_iff_factorWitness (hLA : LocalAlternativeOmega) {n : ℕ} (hn : 1 ≤ n)
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    G n S = G n S' ↔ FactorWitness n S S' := by
  have := (main_structure hLA hn hn hS hS').out 1 3
  rw [this]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- `eq:congruence`: inventory equivalence is a two-sided congruence for `∘`.  If `α ∼ α'` (weight
`m`, cut sets `A, A'`) and `β ∼ β'` (weight `n`, cut sets `E, E'`), then `α ∘ β ∼ α' ∘ β'`.  The proof
uses `Ψ_{α ∘ β} = Ψ_β Ψ_α`; equality of the maps `Ψ_β = Ψ_{β'}` comes from `thm:main-structure`. -/
theorem congruence (hLA : LocalAlternativeOmega) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {A A' E E' : Finset ℕ} (hA : IsCutSet m A) (hA' : IsCutSet m A') (hE : IsCutSet n E)
    (hE' : IsCutSet n E') (hα : G m A = G m A') (hβ : G n E = G n E') :
    G (m * n) (compCuts m A n E) = G (m * n) (compCuts m A' n E') := by
  have hP : Psi n E = Psi n E' := (G_eq_iff_Psi_eq hLA hn hn hE hE').mp hβ
  rw [← Psi_G n E (by omega) hE m A hA, ← Psi_G n E' (by omega) hE' m A' hA', hP, hα]

/-- `eq:REV`: `G_β = G_γ` implies `G_{β^{⊙ m}} = G_{γ^{⊙ m}}` for every `m ≥ 1` (`β, γ` of weight
`n`).  Equality of `Ψ_β` and `Ψ_γ` on the generator `h_m`. -/
theorem REV (hLA : LocalAlternativeOmega) {n m : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ}
    (hS : IsCutSet n S) (hS' : IsCutSet n S') (h : G n S = G n S') :
    G (m * n) (nearPowerCuts n S m) = G (m * n) (nearPowerCuts n S' m) := by
  have hP : Psi n S = Psi n S' := (G_eq_iff_Psi_eq hLA hn hn hS hS').mp h
  rw [← Psi_hgen, ← Psi_hgen, hP]

/-! ### `cor:class` -/

/-- The class `ℰ(β) = {γ : G_γ = G_β}` of compositions of weight `n`, as a set of cut sets. -/
def invClass (n : ℕ) (S : Finset ℕ) : Set (Finset ℕ) := {γ | IsCutSet n γ ∧ G n γ = G n S}

/-- `eq:old-inclusion`: the cited inclusion `ℰ((m) ∘ β) ⊆ {(m) ∘ γ : γ ∈ ℰ(β)}` at one instance
(the inclusion of Billera–Thomas–van Willigenburg for the one-part outer factor `(m)`),
for `β` of weight `n` with cut set `S`.  `(m) ∘ β` is `compCuts m ∅ n S`, the near-power `β^{⊙ m}`. -/
def OldInclusion (m n : ℕ) (S : Finset ℕ) : Prop :=
  invClass (m * n) (compCuts m ∅ n S) ⊆ {η | ∃ γ ∈ invClass n S, η = compCuts m ∅ n γ}

/-- `cor:class`, the inclusion `⊇`: `{(m) ∘ γ : γ ∈ ℰ(β)} ⊆ ℰ((m) ∘ β)`, which is `eq:REV`. -/
theorem class_supset (hLA : LocalAlternativeOmega) {m n : ℕ} {S : Finset ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hS : IsCutSet n S) :
    {η | ∃ γ ∈ invClass n S, η = compCuts m ∅ n γ} ⊆ invClass (m * n) (compCuts m ∅ n S) := by
  rintro η ⟨γ, ⟨hγ, hGγ⟩, rfl⟩
  refine ⟨compCuts_isCutSet (by omega) (fun x hx => by simp at hx) hγ, ?_⟩
  simp only [compCuts_empty]
  exact REV hLA hn hγ hS hGγ

/-- `cor:class`, the inclusion `⊆`, from a given instance of `eq:old-inclusion`
(`hThm45 : OldInclusion m n S`).  `ClassInclusion.oldInclusion` proves every instance, so
`cor_class_unconditional` carries no such hypothesis. -/
theorem class_subset_of_cited {m n : ℕ} {S : Finset ℕ} (hThm45 : OldInclusion m n S) :
    invClass (m * n) (compCuts m ∅ n S) ⊆ {η | ∃ γ ∈ invClass n S, η = compCuts m ∅ n γ} :=
  hThm45

/-- `cor:class`: for every `m ≥ 1`, `ℰ((m) ∘ β) = {(m) ∘ γ : γ ∈ ℰ(β)}`, from `eq:old-inclusion`
at this instance (`hThm45`) and `eq:REV` (`class_supset`, from `hLA`).  The unconditional statement
is `cor_class_unconditional` in `ClassInclusion`. -/
theorem cor_class (hLA : LocalAlternativeOmega) {m n : ℕ} {S : Finset ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hS : IsCutSet n S) (hThm45 : OldInclusion m n S) :
    invClass (m * n) (compCuts m ∅ n S) = {η | ∃ γ ∈ invClass n S, η = compCuts m ∅ n γ} :=
  Set.Subset.antisymm (class_subset_of_cited hThm45) (class_supset hLA hm hn hS)

/-! ### `thm:main-recognition` -/

/-- `thm:main-recognition`: for compositions `β, γ` of weight `n` (cut sets `S, S'`), either the
inventories are equal or there is a partition `λ ⊢ n` with `ℓ(λ) ≤ B(n) ≤ Ω(n) + 2` and
`m_β(λ) - m_γ(λ) ∈ {-2, -1, 1, 2}`, with all parts distinct except possibly one repeated pair.  The
two alternatives are exclusive.  Conditional on `hLA : LocalAlternative arithBound`. -/
theorem main_recognition (hLA : LocalAlternativeB) {n : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ}
    (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    Xor (G n S = G n S') (∃ lam, CoarseCertificate arithBound n S S' lam) ∧
      arithBound n ≤ ArithmeticFunction.cardFactors n + 2 := by
  refine ⟨?_, arithBound_le_Omega_add_two hn⟩
  rcases budget_recognition monotoneDvd_arithBound hLA hn hS hS' with ⟨⟨hw, _⟩, hnc⟩ | ⟨hc, hnw⟩
  · exact Or.inl ⟨hw.G_eq, hnc⟩
  · refine Or.inr ⟨hc, fun hG => hnw ⟨?_, ?_⟩⟩
    · exact (G_eq_iff_factorWitness hLA.toOmega hn hS hS').mp hG
    · exact ((G_eq_iff_Psi_eq hLA.toOmega hn hn hS hS').mp hG)

/-- `thm:main-recognition`, the logarithmic bound `B(n) ≤ 2 log₆ n + log₆ 9`
(`prop:logarithmic-cutoff`). -/
theorem main_recognition_logb {n : ℕ} (hn : 1 ≤ n) :
    (arithBound n : ℝ) ≤ 2 * Real.logb 6 n + Real.logb 6 9 :=
  arithBound_le_logb hn

/-- The ordinary-degree truncation `G^{[≤ s]}` is `truncLT (s + 1)`. -/
lemma coeff_truncLT_posParts {n s : ℕ} (hn : 1 ≤ n) {S : Finset ℕ} (hS : IsCutSet n S)
    {lam : Multiset ℕ} (hpos : ∀ x ∈ lam, 0 < x) (hcard : Multiset.card lam ≤ s) :
    (truncLT (s + 1) (G n S)).coeff (Multiset.toFinsupp (posParts lam)) = (mult n S lam : ℤ) := by
  rw [coeff_truncLT, if_pos, coeff_G (by omega) hS lam hpos]
  rw [degree_toFinsupp, card_posParts hpos]
  omega

/-- `eq:main-modular`, for every cutoff `s ≥ B(n)`: for every `q ≥ 3`, the truncations
`G^{[≤ s]}` of the two inventories are congruent modulo `q` (coefficientwise) exactly when the
inventories are equal.  Conditional on `hLA : LocalAlternative arithBound`. -/
theorem main_modular_of_cutoff (hLA : LocalAlternativeB) {q : ℕ} (hq : 3 ≤ q) {n s : ℕ}
    (hn : 1 ≤ n) (hs : arithBound n ≤ s) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') :
    PolyCongr q (truncLT (s + 1) (G n S)) (truncLT (s + 1) (G n S')) ↔ G n S = G n S' := by
  constructor
  · intro hc
    by_contra hne
    rcases (main_recognition hLA hn hS hS').1 with ⟨hG, _⟩ | ⟨⟨lam, hpos, _, hcard, hdiff, _⟩, _⟩
    · exact hne hG
    · have h := hc (Multiset.toFinsupp (posParts lam))
      rw [coeff_truncLT_posParts hn hS hpos (hcard.trans hs),
        coeff_truncLT_posParts hn hS' hpos (hcard.trans hs)] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdiff
      exact not_dvd_of_abs_le_two (by omega) (by rcases hdiff with h | h | h | h <;> rw [h] <;>
        norm_num) hq h
  · intro h d
    rw [h]
    simp

/-- `eq:main-modular`: for every `q ≥ 3`, `G_β^{[≤ B(n)]} ≡ G_γ^{[≤ B(n)]} (mod q)` if and only if
`G_β = G_γ`.  Conditional on `hLA : LocalAlternative arithBound`. -/
theorem main_modular (hLA : LocalAlternativeB) {q : ℕ} (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n)
    {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    PolyCongr q (truncLT (arithBound n + 1) (G n S)) (truncLT (arithBound n + 1) (G n S')) ↔
      G n S = G n S' :=
  main_modular_of_cutoff hLA hq hn le_rfl hS hS'

/-! ### `thm:main-depth` -/

/-- The weight-only budget: every unequal pair of weight `n ≥ 2` is distinguished through degree
`B(n)` (the hypothesis `hbud` of `cumDepth_le_uBound_of_budget`).  Conditional on
`hLA : LocalAlternative arithBound`. -/
theorem dep_le_arithBound (hLA : LocalAlternativeB) {n : ℕ} (hn : 2 ≤ n) {S S' : Finset ℕ}
    (hS : IsCutSet n S) (hS' : IsCutSet n S') (hne : G n S ≠ G n S') :
    dep n S S' ≤ arithBound n := by
  rcases (main_recognition hLA (by omega) hS hS').1 with ⟨hG, _⟩ | ⟨⟨lam, hpos, hsum, hcard, hdiff, _⟩, _⟩
  · exact absurd hG hne
  · have hne' : mult n S lam ≠ mult n S' lam := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdiff
      omega
    exact (dep_le_card ⟨lam, fun {i} hi => hpos i hi, hsum⟩ hne').trans hcard

/-- `thm:main-depth`, upper bound: `C(N) ≤ U(N)` for every `N ≥ 1`.  Conditional on
`hLA : LocalAlternative arithBound`. -/
theorem cumDepth_le_uBound (hLA : LocalAlternativeB) {N : ℕ} (hN : 1 ≤ N) :
    cumDepth N ≤ uBound N :=
  cumDepth_le_uBound_of_budget
    (fun n hn S S' hS hS' hne => dep_le_arithBound hLA hn hS hS' hne) hN

/-- `thm:main-depth`, `eq:frontier` in the form `C(N) = U(N)` for every `N ≥ 1`: the lower bound is
unconditional (`uBound_le_cumDepth'`); the upper bound is conditional on
`hLA : LocalAlternative arithBound`. -/
theorem cumDepth_eq_uBound' (hLA : LocalAlternativeB) {N : ℕ} (hN : 1 ≤ N) :
    cumDepth N = uBound N :=
  cumDepth_eq_uBound_of_upper (fun _ hN' => cumDepth_le_uBound hLA hN') hN

/-- `thm:main-depth`, `eq:frontier`: the piecewise formula
`C(N) = 0` for `N = 1`, `2` for `2 ≤ N ≤ 4`, `3` for `5 ≤ N ≤ 11`, and
`2j + 4 + 𝟙[N ≥ 30 · 6^j]` for `12 · 6^j ≤ N < 72 · 6^j`, `j ≥ 0`.  Conditional on
`hLA : LocalAlternative arithBound`. -/
theorem frontier (hLA : LocalAlternativeB) :
    cumDepth 1 = 0 ∧ (∀ N, 2 ≤ N → N ≤ 4 → cumDepth N = 2) ∧
      (∀ N, 5 ≤ N → N ≤ 11 → cumDepth N = 3) ∧
      ∀ j N : ℕ, 12 * 6 ^ j ≤ N → N < 72 * 6 ^ j →
        cumDepth N = 2 * j + 4 + (if 30 * 6 ^ j ≤ N then 1 else 0) := by
  have hpos : ∀ j : ℕ, 0 < 6 ^ j := fun j => by positivity
  refine ⟨cumDepth_one, fun N h2 h4 => ?_, fun N h5 h11 => ?_, fun j N h1 h2 => ?_⟩
  · rw [cumDepth_eq_uBound' hLA (by omega), uBound_small.2.1 N h2 h4]
  · rw [cumDepth_eq_uBound' hLA (by omega), uBound_small.2.2 N h5 h11]
  · have := hpos j
    rw [cumDepth_eq_uBound' hLA (by omega), uBound_of_bracket h1 h2]

/-- `thm:main-depth`, modular sharpness (unconditional): for every `N ≥ 2` there is a pair of
compositions of weight `n ≤ N` whose coarsening polynomials are unequal, agree in all ordinary degrees
`< U(N)`, and whose truncations through degree `U(N)` are not congruent modulo any `q ≥ 2` (in
particular any `q ≥ 3`).  The pairs are the recursive families `evenPair`, `oddPair`, with a unit first
discrepancy. -/
theorem modular_sharp_frontier {N : ℕ} (hN : 2 ≤ N) :
    ∃ (n : ℕ) (S S' : Finset ℕ), n ≤ N ∧ IsCutSet n S ∧ IsCutSet n S' ∧
      truncLT (uBound N) (G n S) = truncLT (uBound N) (G n S') ∧
      ∀ q : ℕ, 2 ≤ q → ¬ PolyCongr q (truncLT (uBound N + 1) (G n S))
        (truncLT (uBound N + 1) (G n S')) := by
  have hpos : ∀ j : ℕ, 0 < 6 ^ j := fun j => by positivity
  by_cases h4 : N ≤ 4
  · rw [uBound_small.2.1 N hN h4]
    obtain ⟨h1, h2⟩ := even_modular_sharp 0
    obtain ⟨hR, hS, _⟩ := even_family 0
    exact ⟨2 * 6 ^ 0, _, _, by simpa using hN, hR, hS, by simpa using h1, by simpa using h2⟩
  by_cases h11 : N < 12
  · rw [uBound_small.2.2 N (by omega) (by omega)]
    obtain ⟨h1, h2⟩ := odd_modular_sharp 0
    obtain ⟨hR, hS, _⟩ := odd_family 0
    exact ⟨5 * 6 ^ 0, _, _, by simpa using (by omega : 5 ≤ N), hR, hS, by simpa using h1,
      by simpa using h2⟩
  · obtain ⟨j, hj⟩ : ∃ j, Nat.log 6 (N / 12) = j := ⟨_, rfl⟩
    have hp := hpos j
    have hdiv : 0 < N / 12 := by omega
    have hle : 12 * 6 ^ j ≤ N := by
      have := Nat.pow_log_le_self 6 (Nat.pos_iff_ne_zero.mp hdiv)
      rw [hj] at this
      omega
    have hlt : N < 72 * 6 ^ j := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 6) (N / 12)
      rw [hj, pow_succ] at this
      omega
    have hU := uBound_of_bracket hle hlt
    by_cases h30 : 30 * 6 ^ j ≤ N
    · rw [hU, if_pos h30]
      obtain ⟨h1, h2⟩ := odd_modular_sharp (j + 1)
      obtain ⟨hR, hS, _⟩ := odd_family (j + 1)
      have e : 5 * 6 ^ (j + 1) = 30 * 6 ^ j := by ring
      have e2 : 2 * (j + 1) + 3 = 2 * j + 4 + 1 := by ring
      have e3 : 2 * (j + 1) + 4 = 2 * j + 4 + 1 + 1 := by ring
      rw [e2] at h1
      rw [e3] at h2
      exact ⟨5 * 6 ^ (j + 1), _, _, by omega, hR, hS, h1, h2⟩
    · rw [hU, if_neg h30]
      obtain ⟨h1, h2⟩ := even_modular_sharp (j + 1)
      obtain ⟨hR, hS, _⟩ := even_family (j + 1)
      have e : 2 * 6 ^ (j + 1) = 12 * 6 ^ j := by ring
      have e2 : 2 * (j + 1) + 2 = 2 * j + 4 + 0 := by ring
      have e3 : 2 * (j + 1) + 3 = 2 * j + 4 + 0 + 1 := by ring
      rw [e2] at h1
      rw [e3] at h2
      exact ⟨2 * 6 ^ (j + 1), _, _, by omega, hR, hS, h1, h2⟩

/-- `thm:main-depth`, modular sufficiency at the frontier: for `N ≥ 1`, any pair of weight `n ≤ N`
whose truncations through degree `U(N)` are congruent modulo some `q ≥ 3` has equal inventories.
Together with `modular_sharp_frontier` this says the cumulative frontier `U(N)` is sharp for the
modular tests `eq:main-modular`, for every `q ≥ 3`.  Conditional on
`hLA : LocalAlternative arithBound`. -/
theorem modular_frontier (hLA : LocalAlternativeB) {q : ℕ} (hq : 3 ≤ q) {N n : ℕ} (hn : 1 ≤ n)
    (hnN : n ≤ N) {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    PolyCongr q (truncLT (uBound N + 1) (G n S)) (truncLT (uBound N + 1) (G n S')) ↔
      G n S = G n S' := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    have e : (Finset.Ioo 0 1 : Finset ℕ) = ∅ := by decide
    have hs : S = ∅ := Finset.subset_empty.mp (e ▸ hS)
    have hs' : S' = ∅ := Finset.subset_empty.mp (e ▸ hS')
    subst hs hs'
    exact ⟨fun _ => rfl, fun _ d => by simp⟩
  · exact main_modular_of_cutoff hLA hq hn
      ((arithBound_le_uBound h).trans (uBound_mono (by omega) hnN)) hS hS'

end SkewRibbonCoarsenings
