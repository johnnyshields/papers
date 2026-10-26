/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.DepthDefs
import SkewRibbonCoarsenings.LogarithmicCutoff

/-!
# The threshold families and the lower bound of the exact cumulative depth

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:depth` (`thm:main-depth`, lower
bound; `eq:even-threshold`, `eq:odd-threshold`, `eq:frontier`,).

The even family starts at `R₀ = (1,1)`, `S₀ = (2)` and the odd family at `R₀ = (1,1,3)`,
`S₀ = (1,2,2)`; both are iterated by the lift of `eq:sharpness-lift` (`liftR`, `liftS`).  The
all-odd invariant `OA` holds at the seeds (`OA_even_seed`, `OA_odd_seed`; the latter by the
two-block reflection argument), `thm_lift` propagates it, and the unit witnesses are transported
by the exact-degree clause.  This gives pairs of weight `2 · 6^r` with first discrepancy `2r + 2`
and of weight `5 · 6^r` with first discrepancy `2r + 3`, hence `C(N) ≥ U(N)` for `N ≥ 2`
(`uBound_le_cumDepth`).  The upper bound `C(N) ≤ U(N)` is not part of this module; it is
reduced to the budget statement of `prop:refined-budget` in `cumDepth_le_uBound_of_budget`.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open MvPolynomial Finset

/-! ### Cut sets of the lifted roots -/

lemma isCutSet_liftR {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) : IsCutSet (6 * w) (liftR w R S) := by
  rw [liftR_eq]
  exact isCutSet_wordBd hw hR hS 0 6 (A := {2, 3}) (by intro x hx; simp at hx; omega)

lemma isCutSet_liftS {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) : IsCutSet (6 * w) (liftS w R S) := by
  rw [liftS_eq]
  exact isCutSet_wordBd hw hR hS 0 6 (A := {3, 4}) (by intro x hx; simp at hx; omega)

/-! ### A positive coefficient difference is a witness -/

lemma mult_ne_of_unit {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') (lam : Multiset ℕ) (hpos : ∀ x ∈ lam, 0 < x)
    (hunit : (G n S - G n S').coeff (Multiset.toFinsupp (posParts lam)) = 1 ∨
      (G n S - G n S').coeff (Multiset.toFinsupp (posParts lam)) = -1) :
    mult n S lam ≠ mult n S' lam := by
  intro h
  have h0 : (G n S - G n S').coeff (Multiset.toFinsupp (posParts lam)) = 0 := by
    rw [MvPolynomial.coeff_sub, coeff_G hn hS _ hpos, coeff_G hn hS' _ hpos, h]; simp
  rcases hunit with h1 | h1 <;> rw [h1] at h0 <;> norm_num at h0

/-- The ordinary two-sided data of a first discrepancy: no monomial of ordinary degree `< s` in
`G_β - G_γ` and an ordinary unit witness at a partition with `s` parts give `dep(β,γ) = s`. -/
theorem dep_eq_of_unit_witness {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') {s : ℕ} (hlow : ordGE s (G n S - G n S'))
    (lam : Multiset ℕ) (hpos : ∀ x ∈ lam, 0 < x) (hsum : lam.sum = n)
    (hcard : Multiset.card lam = s)
    (hunit : (G n S - G n S').coeff (Multiset.toFinsupp (posParts lam)) = 1 ∨
      (G n S - G n S').coeff (Multiset.toFinsupp (posParts lam)) = -1) :
    G n S ≠ G n S' ∧ dep n S S' = s :=
  dep_eq_of_witness hn hS hS' hlow ⟨lam, fun {i} hi => hpos i hi, hsum⟩
    (mult_ne_of_unit hn hS hS' lam hpos hunit) hcard

/-! ### The seeds -/

/-- `OA_2` holds for every pair of compositions of a common weight: every composition of a given
weight has the same one-block term. -/
theorem OA_two {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R) (hS : IsCutSet w S) :
    OA w R S 2 := by
  rw [OA_iff]
  intro j
  have hA := isCutSet_altCuts hR hS j
  have hB := isCutSet_altCuts hS hR j
  have hn : 0 < (2 * j + 1) * w := by positivity
  have e : G ((2 * j + 1) * w) (altCuts w R S j) - G ((2 * j + 1) * w) (altCuts w S R j) =
      (G ((2 * j + 1) * w) (altCuts w R S j) - hgen ((2 * j + 1) * w)) -
        (G ((2 * j + 1) * w) (altCuts w S R j) - hgen ((2 * j + 1) * w)) := by ring
  rw [e]
  exact ordGE_sub (ordGE_G_sub hn hA) (ordGE_G_sub hn hB)

lemma wordCuts_mem_iff {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) {p m x : ℕ} :
    x ∈ wordCuts w R S p m ↔
      x / w < m ∧ x % w ∈ (if Even (x / w + p) then R else S) := by
  constructor
  · intro h
    obtain ⟨k, hk, y, hy, rfl⟩ := mem_wordCuts.mp h
    have hy' : 0 < y ∧ y < w := by
      split_ifs at hy
      · exact Finset.mem_Ioo.mp (hR hy)
      · exact Finset.mem_Ioo.mp (hS hy)
    have e1 : (k * w + y) / w = k := by
      apply Nat.div_eq_of_lt_le
      · omega
      · nlinarith
    have e2 : (k * w + y) % w = y := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy'.2]
    rw [e1, e2]
    exact ⟨hk, hy⟩
  · rintro ⟨h1, h2⟩
    exact mem_wordCuts.mpr ⟨x / w, h1, x % w, h2, Nat.div_add_mod' x w⟩

private lemma isCutSet_seedR : IsCutSet 5 ({1, 2} : Finset ℕ) := by
  simp [IsCutSet, Finset.subset_iff]

private lemma isCutSet_seedS : IsCutSet 5 ({1, 3} : Finset ℕ) := by
  simp [IsCutSet, Finset.subset_iff]

private lemma seed_mem_iff (a b : Finset ℕ) (ha : a = {1, 2} ∨ a = {1, 3})
    (hb : b = {1, 2} ∨ b = {1, 3}) (hab : a ≠ b) (m x : ℕ) :
    x ∈ wordCuts 5 a b 0 m ↔
      x / 5 < m ∧ ((x / 5) % 2 = 0 ∧ x % 5 ∈ a ∨ (x / 5) % 2 = 1 ∧ x % 5 ∈ b) := by
  have hcs : ∀ c : Finset ℕ, (c = {1, 2} ∨ c = {1, 3}) → IsCutSet 5 c := by
    rintro c (rfl | rfl)
    · exact isCutSet_seedR
    · exact isCutSet_seedS
  rw [wordCuts_mem_iff (by norm_num) (hcs a ha) (hcs b hb)]
  refine and_congr_right fun _ => ?_
  simp only [add_zero]
  by_cases h : Even (x / 5)
  · have h' : (x / 5) % 2 = 0 := by simpa [Nat.even_iff] using h
    simp [h, h']
  · have h' : (x / 5) % 2 = 1 := by
      have : ¬ (x / 5) % 2 = 0 := by simpa [Nat.even_iff] using h
      omega
    simp [h, h']

/-- The two-block data of the odd seeds in every odd alternating length: for `p + q = n`,
the number of cuts of `Alt_j(R₀,S₀)` among `{p, q}` equals that of `Alt_j(S₀,R₀)`.  The reflection
`x ↦ n - x` preserves the parity of the cell index and sends the cell position `y` to `5 - y`, and
`[y ∈ {1,2}] + [5 - y ∈ {1,2}] = [y ∈ {1,3}] + [5 - y ∈ {1,3}]` for every `y`. -/
lemma odd_seed_two_block (j p q : ℕ) (hpq : p + q = (2 * j + 1) * 5) :
    ((if p ∈ wordCuts 5 ({1, 2} : Finset ℕ) {1, 3} 0 (2 * j + 1) then 1 else 0) +
        (if q ∈ wordCuts 5 ({1, 2} : Finset ℕ) {1, 3} 0 (2 * j + 1) then 1 else 0) : ℕ) =
      (if p ∈ wordCuts 5 ({1, 3} : Finset ℕ) {1, 2} 0 (2 * j + 1) then 1 else 0) +
        (if q ∈ wordCuts 5 ({1, 3} : Finset ℕ) {1, 2} 0 (2 * j + 1) then 1 else 0) := by
  have h12 : ({1, 2} : Finset ℕ) ≠ {1, 3} := by decide
  have h21 : ({1, 3} : Finset ℕ) ≠ {1, 2} := by decide
  simp only [seed_mem_iff {1, 2} {1, 3} (Or.inl rfl) (Or.inr rfl) h12,
    seed_mem_iff {1, 3} {1, 2} (Or.inr rfl) (Or.inl rfl) h21]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> omega

lemma card_parts_cases {n : ℕ} (hn : 0 < n) (P : n.Partition) (hP : Multiset.card P.parts < 3) :
    P.parts = {n} ∨ ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ p + q = n ∧ P.parts = {p, q} := by
  have hsum := P.parts_sum
  have hc : Multiset.card P.parts = 0 ∨ Multiset.card P.parts = 1 ∨ Multiset.card P.parts = 2 := by
    omega
  rcases hc with h | h | h
  · rw [Multiset.card_eq_zero] at h
    rw [h] at hsum
    simp at hsum
    omega
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
    rw [ha] at hsum
    simp at hsum
    left
    rw [ha, hsum]
  · obtain ⟨p, q, hpq⟩ := Multiset.card_eq_two.mp h
    right
    refine ⟨p, q, P.parts_pos (by rw [hpq]; simp), P.parts_pos (by rw [hpq]; simp), ?_, hpq⟩
    rw [hpq] at hsum
    simpa using hsum

/-- `thm:main-depth`, odd seeds: `OA_3(R₀,S₀)` for `R₀ = (1,1,3)` (cuts `{1,2}`) and
`S₀ = (1,2,2)` (cuts `{1,3}`), at every odd alternating length.  The two-block data of
`Alt_j(R₀,S₀)` and `Alt_j(S₀,R₀)` agree by `odd_seed_two_block`, and the one-block data agree
because every composition of a given weight has the same one-block term. -/
theorem OA_odd_seed : OA 5 ({1, 2} : Finset ℕ) {1, 3} 3 := by
  rw [OA_iff]
  intro j
  have hA := isCutSet_altCuts isCutSet_seedR isCutSet_seedS j
  have hB := isCutSet_altCuts isCutSet_seedS isCutSet_seedR j
  have hn : 0 < (2 * j + 1) * 5 := by omega
  rw [ordGE_G_sub_iff hn hA hB]
  intro P hP
  rcases card_parts_cases hn P hP with h | ⟨p, q, hp, hq, hpq, h⟩
  · rw [h, mult_single hA, mult_single hB]
  · rw [h, mult_two hA hp hq hpq, mult_two hB hp hq hpq, altCuts_eq_wordCuts,
      altCuts_eq_wordCuts]
    have hne : p ≠ q := by omega
    rw [if_neg hne, if_neg hne]
    exact odd_seed_two_block j p q hpq

/-- `thm:main-depth`, even seeds: `OA_2(R₀,S₀)` for `R₀ = (1,1)` (cuts `{1}`) and `S₀ = (2)`
(no cuts). -/
theorem OA_even_seed : OA 2 ({1} : Finset ℕ) ∅ 2 :=
  OA_two (by norm_num) (by simp [IsCutSet, Finset.subset_iff]) (by simp [IsCutSet])

/-! ### Iterating the lift -/

/-- The iterated lifted pairs: stage `0` is `P₀` of weight `w₀`; stage `r + 1` lifts stage `r`
of weight `w₀ · 6^r`. -/
def liftPair (w₀ : ℕ) (P₀ : Finset ℕ × Finset ℕ) : ℕ → Finset ℕ × Finset ℕ
  | 0 => P₀
  | r + 1 => (liftR (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 (liftPair w₀ P₀ r).2,
      liftS (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 (liftPair w₀ P₀ r).2)

/-- The invariant carried through the lifts: the cut sets, `OA_{s₀+2r}`, and a unit witness at a
partition of the stage weight with `s₀ + 2r` parts. -/
structure LiftSpec (w₀ s₀ r : ℕ) (P₀ : Finset ℕ × Finset ℕ) : Prop where
  cutR : IsCutSet (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1
  cutS : IsCutSet (w₀ * 6 ^ r) (liftPair w₀ P₀ r).2
  oa : OA (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 (liftPair w₀ P₀ r).2 (s₀ + 2 * r)
  wit : ∃ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) ∧ lam.sum = w₀ * 6 ^ r ∧
    Multiset.card lam = s₀ + 2 * r ∧
    ((G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 - G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).2).coeff
        (Multiset.toFinsupp (posParts lam)) = 1 ∨
      (G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 - G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).2).coeff
        (Multiset.toFinsupp (posParts lam)) = -1)

theorem liftSpec_succ {w₀ s₀ r : ℕ} {P₀ : Finset ℕ × Finset ℕ} (hw₀ : 0 < w₀) (hs₀ : 2 ≤ s₀)
    (h : LiftSpec w₀ s₀ r P₀) : LiftSpec w₀ s₀ (r + 1) P₀ := by
  have hw : 0 < w₀ * 6 ^ r := by positivity
  have e : w₀ * 6 ^ (r + 1) = 6 * (w₀ * 6 ^ r) := by ring
  obtain ⟨lam, hpos, hsum, hcard, hunit⟩ := h.wit
  obtain ⟨_, b⟩ := lift_first_differs hw h.cutR h.cutS (by omega) h.oa lam hpos hsum hcard hunit
  obtain ⟨hord, hdeg, hcoef, hu⟩ := b
  have hs : 2 ≤ s₀ + 2 * r := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [liftPair]
    rw [e]
    exact isCutSet_liftR hw h.cutR h.cutS
  · simp only [liftPair]
    rw [e]
    exact isCutSet_liftS hw h.cutR h.cutS
  · simp only [liftPair]
    rw [e, show s₀ + 2 * (r + 1) = s₀ + 2 * r + 2 by ring]
    exact OA_lift hw h.cutR h.cutS hs h.oa
  · refine ⟨lam + {2 * (w₀ * 6 ^ r), 3 * (w₀ * 6 ^ r)}, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact hpos x hx
      · simp at hx; omega
    · simp only [Multiset.sum_add, hsum]
      simp
      rw [e]; ring
    · simp [hcard]; ring
    · simp only [liftPair]
      rw [e]
      exact hu

theorem liftSpec_all {w₀ s₀ : ℕ} {P₀ : Finset ℕ × Finset ℕ} (hw₀ : 0 < w₀) (hs₀ : 2 ≤ s₀)
    (h0 : LiftSpec w₀ s₀ 0 P₀) (r : ℕ) : LiftSpec w₀ s₀ r P₀ := by
  induction r with
  | zero => exact h0
  | succ r ih => exact liftSpec_succ hw₀ hs₀ ih

/-- Every `LiftSpec` stage is a pair of unequal compositions whose first distinguishing depth is
`s₀ + 2r`, with no monomial of ordinary degree `< s₀ + 2r` in the difference and an ordinary unit
witness. -/
theorem LiftSpec.dep_eq {w₀ s₀ r : ℕ} {P₀ : Finset ℕ × Finset ℕ} (hw₀ : 0 < w₀)
    (h : LiftSpec w₀ s₀ r P₀) :
    ordGE (s₀ + 2 * r) (G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 - G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).2) ∧
    G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 ≠ G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).2 ∧
    dep (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 (liftPair w₀ P₀ r).2 = s₀ + 2 * r := by
  have hw : 0 < w₀ * 6 ^ r := by positivity
  have hlow : ordGE (s₀ + 2 * r)
      (G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).1 - G (w₀ * 6 ^ r) (liftPair w₀ P₀ r).2) := by
    have := OA_iff.mp h.oa 0
    simpa [altCuts] using this
  obtain ⟨lam, hpos, hsum, hcard, hunit⟩ := h.wit
  exact ⟨hlow, dep_eq_of_unit_witness hw h.cutR h.cutS hlow lam hpos hsum hcard hunit⟩

/-! ### The even family -/

/-- The even family `R_r`, `S_r` of the proof of `thm:main-depth`: seeds `(1,1)` and `(2)`,
weight `2 · 6^r`. -/
def evenPair : ℕ → Finset ℕ × Finset ℕ := liftPair 2 ({1}, ∅)

/-- The odd family `R_r`, `S_r` of the proof of `thm:main-depth`: seeds `(1,1,3)` and `(1,2,2)`,
weight `5 · 6^r`. -/
def oddPair : ℕ → Finset ℕ × Finset ℕ := liftPair 5 ({1, 2}, {1, 3})

lemma evenSeed_spec : LiftSpec 2 2 0 ({1}, ∅) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [liftPair, IsCutSet, Finset.subset_iff]
  · simp [liftPair, IsCutSet]
  · simpa [liftPair] using OA_even_seed
  · refine ⟨{1, 1}, by decide, by decide, by decide, Or.inl ?_⟩
    have hR : IsCutSet 2 ({1} : Finset ℕ) := by simp [IsCutSet, Finset.subset_iff]
    have hS : IsCutSet 2 (∅ : Finset ℕ) := by simp [IsCutSet]
    simp only [liftPair, pow_zero, mul_one]
    rw [MvPolynomial.coeff_sub, coeff_G (by norm_num) hR _ (by decide),
      coeff_G (by norm_num) hS _ (by decide)]
    have h1 : mult 2 ({1} : Finset ℕ) {1, 1} = 1 := by decide
    have h2 : mult 2 (∅ : Finset ℕ) {1, 1} = 0 := by decide
    rw [h1, h2]; norm_num

lemma oddSeed_spec : LiftSpec 5 3 0 ({1, 2}, {1, 3}) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [liftPair] using isCutSet_seedR
  · simpa [liftPair] using isCutSet_seedS
  · simpa [liftPair] using OA_odd_seed
  · refine ⟨{3, 1, 1}, by decide, by decide, by decide, Or.inl ?_⟩
    simp only [liftPair, pow_zero, mul_one]
    rw [MvPolynomial.coeff_sub, coeff_G (by norm_num) isCutSet_seedR _ (by decide),
      coeff_G (by norm_num) isCutSet_seedS _ (by decide)]
    have h1 : mult 5 ({1, 2} : Finset ℕ) {3, 1, 1} = 1 := by decide
    have h2 : mult 5 ({1, 3} : Finset ℕ) {3, 1, 1} = 0 := by decide
    rw [h1, h2]; norm_num

/-- `thm:main-depth`, even family: after `r` lifts the pair has weight `2 · 6^r`, no monomial of
ordinary degree `< 2r + 2` in `G_R - G_S`, and first distinguishing depth exactly `2r + 2` with
an ordinary unit witness. -/
theorem even_family (r : ℕ) :
    IsCutSet (2 * 6 ^ r) (evenPair r).1 ∧ IsCutSet (2 * 6 ^ r) (evenPair r).2 ∧
    ordGE (2 * r + 2) (G (2 * 6 ^ r) (evenPair r).1 - G (2 * 6 ^ r) (evenPair r).2) ∧
    G (2 * 6 ^ r) (evenPair r).1 ≠ G (2 * 6 ^ r) (evenPair r).2 ∧
    dep (2 * 6 ^ r) (evenPair r).1 (evenPair r).2 = 2 * r + 2 := by
  have h := liftSpec_all (by norm_num) (by norm_num) evenSeed_spec r
  obtain ⟨a, b, c⟩ := h.dep_eq (by norm_num)
  refine ⟨h.cutR, h.cutS, ?_, b, ?_⟩
  · simpa [add_comm, evenPair] using a
  · simpa [add_comm, evenPair] using c

/-- `thm:main-depth`, odd family: after `r` lifts the pair has weight `5 · 6^r` and first
distinguishing depth exactly `2r + 3` with an ordinary unit witness. -/
theorem odd_family (r : ℕ) :
    IsCutSet (5 * 6 ^ r) (oddPair r).1 ∧ IsCutSet (5 * 6 ^ r) (oddPair r).2 ∧
    ordGE (2 * r + 3) (G (5 * 6 ^ r) (oddPair r).1 - G (5 * 6 ^ r) (oddPair r).2) ∧
    G (5 * 6 ^ r) (oddPair r).1 ≠ G (5 * 6 ^ r) (oddPair r).2 ∧
    dep (5 * 6 ^ r) (oddPair r).1 (oddPair r).2 = 2 * r + 3 := by
  have h := liftSpec_all (by norm_num) (by norm_num) oddSeed_spec r
  obtain ⟨a, b, c⟩ := h.dep_eq (by norm_num)
  refine ⟨h.cutR, h.cutS, ?_, b, ?_⟩
  · simpa [add_comm, oddPair] using a
  · simpa [add_comm, oddPair] using c

/-- The unit witnesses of the two families, in the form of `thm:lift`: a partition of the stage
weight with the stated number of parts at which the difference has coefficient `±1`. -/
theorem even_family_witness (r : ℕ) :
    ∃ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) ∧ lam.sum = 2 * 6 ^ r ∧
      Multiset.card lam = 2 * r + 2 ∧
      ((G (2 * 6 ^ r) (evenPair r).1 - G (2 * 6 ^ r) (evenPair r).2).coeff
          (Multiset.toFinsupp (posParts lam)) = 1 ∨
        (G (2 * 6 ^ r) (evenPair r).1 - G (2 * 6 ^ r) (evenPair r).2).coeff
          (Multiset.toFinsupp (posParts lam)) = -1) := by
  have h := (liftSpec_all (by norm_num) (by norm_num) evenSeed_spec r).wit
  simpa [add_comm, evenPair] using h

theorem odd_family_witness (r : ℕ) :
    ∃ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) ∧ lam.sum = 5 * 6 ^ r ∧
      Multiset.card lam = 2 * r + 3 ∧
      ((G (5 * 6 ^ r) (oddPair r).1 - G (5 * 6 ^ r) (oddPair r).2).coeff
          (Multiset.toFinsupp (posParts lam)) = 1 ∨
        (G (5 * 6 ^ r) (oddPair r).1 - G (5 * 6 ^ r) (oddPair r).2).coeff
          (Multiset.toFinsupp (posParts lam)) = -1) := by
  have h := (liftSpec_all (by norm_num) (by norm_num) oddSeed_spec r).wit
  simpa [add_comm, oddPair] using h

/-! ### The pairs at the thresholds -/

/-- `eq:even-threshold`: for every `j`, an unequal pair of weight `12 · 6^j` with first
distinguishing depth `2j + 4` and an ordinary unit witness. -/
theorem even_transition (j : ℕ) :
    ∃ S S' : Finset ℕ, IsCutSet (12 * 6 ^ j) S ∧ IsCutSet (12 * 6 ^ j) S' ∧
      ordGE (2 * j + 4) (G (12 * 6 ^ j) S - G (12 * 6 ^ j) S') ∧ G (12 * 6 ^ j) S ≠ G (12 * 6 ^ j) S' ∧
      dep (12 * 6 ^ j) S S' = 2 * j + 4 := by
  have e : 2 * 6 ^ (j + 1) = 12 * 6 ^ j := by ring
  have h := even_family (j + 1)
  rw [e, show 2 * (j + 1) + 2 = 2 * j + 4 by ring] at h
  exact ⟨_, _, h⟩

/-- `eq:odd-threshold`: for every `j`, an unequal pair of weight `30 · 6^j` with first
distinguishing depth `2j + 5` and an ordinary unit witness. -/
theorem odd_transition (j : ℕ) :
    ∃ S S' : Finset ℕ, IsCutSet (30 * 6 ^ j) S ∧ IsCutSet (30 * 6 ^ j) S' ∧
      ordGE (2 * j + 5) (G (30 * 6 ^ j) S - G (30 * 6 ^ j) S') ∧ G (30 * 6 ^ j) S ≠ G (30 * 6 ^ j) S' ∧
      dep (30 * 6 ^ j) S S' = 2 * j + 5 := by
  have e : 5 * 6 ^ (j + 1) = 30 * 6 ^ j := by ring
  have h := odd_family (j + 1)
  rw [e, show 2 * (j + 1) + 3 = 2 * j + 5 by ring] at h
  exact ⟨_, _, h⟩

/-! ### Modular sharpness -/

/-- Coefficientwise congruence modulo `q` of two polynomials in the `h_j`. -/
def PolyCongr (q : ℕ) (f g : Lam) : Prop := ∀ d : ℕ+ →₀ ℕ, (q : ℤ) ∣ f.coeff d - g.coeff d

/-- `thm:main-depth`, modular sharpness: for a pair with `G_β - G_γ` vanishing below ordinary
degree `s` and a unit coefficient at degree `s`, the truncations `G^{[<s]}` agree (so are
congruent modulo every `q`), while the truncations `G^{[≤ s]}` are not congruent modulo any
`q ≥ 2` (in particular any `q ≥ 3`). -/
theorem modular_sharp_of_unit {n : ℕ} {S S' : Finset ℕ} {s : ℕ}
    (hlow : ordGE s (G n S - G n S')) (lam : Multiset ℕ) (hpos : ∀ x ∈ lam, 0 < x)
    (hcard : Multiset.card lam = s)
    (hunit : (G n S - G n S').coeff (Multiset.toFinsupp (posParts lam)) = 1 ∨
      (G n S - G n S').coeff (Multiset.toFinsupp (posParts lam)) = -1) :
    truncLT s (G n S) = truncLT s (G n S') ∧
    ∀ q : ℕ, 2 ≤ q → ¬ PolyCongr q (truncLT (s + 1) (G n S)) (truncLT (s + 1) (G n S')) := by
  refine ⟨?_, ?_⟩
  · ext d
    rw [coeff_truncLT, coeff_truncLT]
    split_ifs with hd
    · have := hlow d hd
      rw [MvPolynomial.coeff_sub] at this
      omega
    · rfl
  · intro q hq hcon
    have hdeg : Finsupp.degree (Multiset.toFinsupp (posParts lam)) = s := by
      rw [degree_toFinsupp, card_posParts hpos, hcard]
    have h := hcon (Multiset.toFinsupp (posParts lam))
    rw [coeff_truncLT, coeff_truncLT, if_pos (by omega), if_pos (by omega),
      ← MvPolynomial.coeff_sub] at h
    rcases hunit with h1 | h1 <;> rw [h1] at h
    · have := Int.le_of_dvd one_pos h
      omega
    · have := Int.le_of_dvd one_pos ((dvd_neg).mp h)
      omega

/-- `thm:main-depth`, modular sharpness for the even family: at every stage the truncations
through degree below `2r + 2` coincide, and the truncations through degree `2r + 2` are not
congruent modulo any `q ≥ 2`. -/
theorem even_modular_sharp (r : ℕ) :
    truncLT (2 * r + 2) (G (2 * 6 ^ r) (evenPair r).1) =
      truncLT (2 * r + 2) (G (2 * 6 ^ r) (evenPair r).2) ∧
    ∀ q : ℕ, 2 ≤ q → ¬ PolyCongr q (truncLT (2 * r + 3) (G (2 * 6 ^ r) (evenPair r).1))
      (truncLT (2 * r + 3) (G (2 * 6 ^ r) (evenPair r).2)) := by
  obtain ⟨_, _, hlow, _, _⟩ := even_family r
  obtain ⟨lam, hpos, _, hcard, hunit⟩ := even_family_witness r
  exact modular_sharp_of_unit hlow lam hpos hcard hunit

/-- `thm:main-depth`, modular sharpness for the odd family. -/
theorem odd_modular_sharp (r : ℕ) :
    truncLT (2 * r + 3) (G (5 * 6 ^ r) (oddPair r).1) =
      truncLT (2 * r + 3) (G (5 * 6 ^ r) (oddPair r).2) ∧
    ∀ q : ℕ, 2 ≤ q → ¬ PolyCongr q (truncLT (2 * r + 4) (G (5 * 6 ^ r) (oddPair r).1))
      (truncLT (2 * r + 4) (G (5 * 6 ^ r) (oddPair r).2)) := by
  obtain ⟨_, _, hlow, _, _⟩ := odd_family r
  obtain ⟨lam, hpos, _, hcard, hunit⟩ := odd_family_witness r
  exact modular_sharp_of_unit hlow lam hpos hcard hunit

/-! ### Monotonicity of `U` -/

/-- `U` is nondecreasing (used for `C(N) ≤ U(N)` from the weight-only bound). -/
theorem uBound_mono {n m : ℕ} (hn1 : 1 ≤ n) (h : n ≤ m) : uBound n ≤ uBound m := by
  by_cases hn : n < 12
  · by_cases hm : m < 12
    · have hsm : ∀ n < 12, ∀ m < 12, 1 ≤ n → n ≤ m → uBound n ≤ uBound m := by decide
      exact hsm n hn m hm hn1 h
    · have hm4 : 4 ≤ uBound m := by
        unfold uBound
        simp only [show m ≠ 1 by omega, show ¬ m ≤ 4 by omega, show ¬ m < 12 by omega, if_false]
        omega
      have hn3 : uBound n ≤ 3 := by
        unfold uBound
        split_ifs <;> omega
      omega
  · have hn12 : 12 ≤ n := by omega
    have hm12 : 12 ≤ m := by omega
    have hdiv : n / 12 ≤ m / 12 := Nat.div_le_div_right h
    have hlog : Nat.log 6 (n / 12) ≤ Nat.log 6 (m / 12) := Nat.log_mono_right hdiv
    unfold uBound
    simp only [show n ≠ 1 by omega, show ¬ n ≤ 4 by omega, show ¬ n < 12 by omega,
      show m ≠ 1 by omega, show ¬ m ≤ 4 by omega, show ¬ m < 12 by omega, if_false]
    rcases Nat.lt_or_ge (Nat.log 6 (n / 12)) (Nat.log 6 (m / 12)) with hlt | hge
    · split_ifs <;> omega
    · have heq : Nat.log 6 (m / 12) = Nat.log 6 (n / 12) := by omega
      rw [heq]
      split_ifs <;> omega

/-! ### The lower bound `C(N) ≥ U(N)` -/

lemma two_le_cumDepth {N : ℕ} (hN : 2 ≤ N) : 2 ≤ cumDepth N := by
  obtain ⟨hR, hS, _, hne, hdep⟩ := even_family 0
  have h := dep_le_cumDepth (n := 2 * 6 ^ 0) (N := N) (by norm_num) (by simpa using hN) hR hS hne
  rw [hdep] at h
  simpa using h

lemma three_le_cumDepth {N : ℕ} (hN : 5 ≤ N) : 3 ≤ cumDepth N := by
  obtain ⟨hR, hS, _, hne, hdep⟩ := odd_family 0
  have h := dep_le_cumDepth (n := 5 * 6 ^ 0) (N := N) (by norm_num) (by simpa using hN) hR hS hne
  rw [hdep] at h
  simpa using h

lemma even_le_cumDepth {j N : ℕ} (hN : 12 * 6 ^ j ≤ N) : 2 * j + 4 ≤ cumDepth N := by
  obtain ⟨S, S', hS, hS', _, hne, hdep⟩ := even_transition j
  have hpos : 1 ≤ 12 * 6 ^ j := by have : 0 < 6 ^ j := by positivity
                                   omega
  have h := dep_le_cumDepth hpos hN hS hS' hne
  rwa [hdep] at h

lemma odd_le_cumDepth {j N : ℕ} (hN : 30 * 6 ^ j ≤ N) : 2 * j + 5 ≤ cumDepth N := by
  obtain ⟨S, S', hS, hS', _, hne, hdep⟩ := odd_transition j
  have hpos : 1 ≤ 30 * 6 ^ j := by have : 0 < 6 ^ j := by positivity
                                   omega
  have h := dep_le_cumDepth hpos hN hS hS' hne
  rwa [hdep] at h

/-- `thm:main-depth`, lower bound: `U(N) ≤ C(N)` for `N ≥ 2`.  The intervals `2 ≤ N ≤ 4` and
`5 ≤ N ≤ 11` are covered by the seed pairs of the two families (weights `2` and `5`, depths `2`
and `3`), and `N ≥ 12` by the pairs at the thresholds `eq:even-threshold` and
`eq:odd-threshold`. -/
theorem uBound_le_cumDepth {N : ℕ} (hN : 2 ≤ N) : uBound N ≤ cumDepth N := by
  by_cases h4 : N ≤ 4
  · rw [uBound_small.2.1 N hN h4]
    exact two_le_cumDepth hN
  · by_cases h12 : N < 12
    · rw [uBound_small.2.2 N (by omega) (by omega)]
      exact three_le_cumDepth (by omega)
    · have hpos : 0 < 6 ^ Nat.log 6 (N / 12) := by positivity
      have hdiv : 0 < N / 12 := by omega
      have hle : 12 * 6 ^ Nat.log 6 (N / 12) ≤ N := by
        have := Nat.pow_log_le_self 6 (Nat.pos_iff_ne_zero.mp hdiv)
        omega
      have h1 := even_le_cumDepth hle
      unfold uBound
      simp only [show N ≠ 1 by omega, show ¬ N ≤ 4 by omega, show ¬ N < 12 by omega, if_false]
      split_ifs with h30
      · exact odd_le_cumDepth h30
      · omega

/-- `thm:main-depth`, lower bound at every positive weight: `U(N) ≤ C(N)` (at `N = 1` both
are `0`). -/
theorem uBound_le_cumDepth' {N : ℕ} (hN : 1 ≤ N) : uBound N ≤ cumDepth N := by
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this
    simp [uBound, cumDepth_one]
  · exact uBound_le_cumDepth h

/-! ### Reduction of the upper bound, and the assembled statement -/

/-- The upper bound `C(N) ≤ U(N)` follows from the weight-only budget statement
`prop:refined-budget` (every unequal pair of weight `n ≥ 2` is distinguished through degree
`B(n)`) together with `prop:logarithmic-cutoff` and the monotonicity of `U`.  This is the exact
hypothesis the assembler of `thm:main-depth` must supply. -/
theorem cumDepth_le_uBound_of_budget
    (hbud : ∀ n : ℕ, 2 ≤ n → ∀ S S' : Finset ℕ, IsCutSet n S → IsCutSet n S' →
      G n S ≠ G n S' → dep n S S' ≤ arithBound n) {N : ℕ} (hN : 1 ≤ N) :
    cumDepth N ≤ uBound N := by
  refine cumDepth_le_of_forall fun n h1 hn S S' hS hS' hne => ?_
  rcases Nat.lt_or_ge n 2 with h | h
  · exfalso
    have : n = 1 := by omega
    subst this
    have hs : S = ∅ := by
      have : S ⊆ (Finset.Ioo 0 1 : Finset ℕ) := hS
      have e : (Finset.Ioo 0 1 : Finset ℕ) = ∅ := by decide
      rw [e] at this
      exact Finset.subset_empty.mp this
    have hs' : S' = ∅ := by
      have : S' ⊆ (Finset.Ioo 0 1 : Finset ℕ) := hS'
      have e : (Finset.Ioo 0 1 : Finset ℕ) = ∅ := by decide
      rw [e] at this
      exact Finset.subset_empty.mp this
    exact hne (by rw [hs, hs'])
  · exact (hbud n h S S' hS hS' hne).trans
      ((arithBound_le_uBound h).trans (uBound_mono (by omega) hn))

/-- `thm:main-depth` (`eq:frontier`, assembled): given the upper bound
`∀ N ≥ 1, C(N) ≤ U(N)`, the cumulative depth equals `U(N)` for every positive `N`. -/
theorem cumDepth_eq_uBound_of_upper (hup : ∀ N : ℕ, 1 ≤ N → cumDepth N ≤ uBound N) {N : ℕ}
    (hN : 1 ≤ N) : cumDepth N = uBound N :=
  le_antisymm (hup N hN) (uBound_le_cumDepth' hN)

end SkewRibbonCoarsenings
