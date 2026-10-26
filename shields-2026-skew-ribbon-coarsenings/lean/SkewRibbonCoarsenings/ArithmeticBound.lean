/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.ArithmeticOptimization

/-!
# The arithmetic detector budget `B(n)`

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:depth`
(`def:arithmetic-bound`, `eq:arithmetic-bound`, `prop:refined-budget`).

`arithBound n` is the budget `B(n)`: `B(1) = 1`, `B(2) = B(3) = B(4) = 2`, and for `n ≥ 5` the
minimum of `n` and the maximum of `3` and the numbers `4 + T_e(d/e)` over divisor pairs
`e ∣ d ∣ n` with `e ≥ 4` and `n/d ≥ 3`.  The arithmetic content of `prop:refined-budget` is
proved: monotonicity under divisibility, `B(n) ≤ Ω(n) + 2`, and the closed formulas for
`B(2^a)`, `B(3^a)`, `B(p^a)`.  Sorry-free.
-/

open scoped ArithmeticFunction.Omega

namespace SkewRibbonCoarsenings

/-- The candidate values `4 + T_e(d/e)` over divisor pairs `e ∣ d ∣ n`, `e ≥ 4`, `n/d ≥ 3`
(the set in `eq:arithmetic-bound`). -/
def arithCandidates (n : ℕ) : Finset ℕ :=
  ((n.divisors ×ˢ n.divisors).filter
    (fun p => p.1 ∣ p.2 ∧ 4 ≤ p.1 ∧ 3 ≤ n / p.2)).image
    (fun p => 4 + arithT p.1 (p.2 / p.1))

/-- Membership in the candidate set. -/
lemma mem_arithCandidates {n x : ℕ} :
    x ∈ arithCandidates n ↔
      n ≠ 0 ∧ ∃ e d, e ∣ d ∧ d ∣ n ∧ 4 ≤ e ∧ 3 ≤ n / d ∧ x = 4 + arithT e (d / e) := by
  constructor
  · intro h
    obtain ⟨⟨e, d⟩, hp, rfl⟩ := Finset.mem_image.1 h
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hp
    obtain ⟨⟨⟨_, hn⟩, ⟨h2, _⟩⟩, h3, h4, h5⟩ := hp
    exact ⟨hn, e, d, h3, h2, h4, h5, rfl⟩
  · rintro ⟨hn, e, d, h3, h2, h4, h5, rfl⟩
    refine Finset.mem_image.2 ⟨(e, d), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
    exact ⟨⟨⟨h3.trans h2, hn⟩, ⟨h2, hn⟩⟩, h3, h4, h5⟩

/-- The inner maximum of `eq:arithmetic-bound`: `max ({3} ∪ candidates)`. -/
def arithBoundMax (n : ℕ) : ℕ := (insert 3 (arithCandidates n)).sup id

/-- `def:arithmetic-bound`: the arithmetic budget `B(n)` of `eq:arithmetic-bound`, with
`B(1) = 1` and `B(2) = B(3) = B(4) = 2`. -/
def arithBound (n : ℕ) : ℕ :=
  if n = 1 then 1 else if n ≤ 4 then 2 else min n (arithBoundMax n)

/-- `def:arithmetic-bound`: `B(1) = 1`. -/
lemma arithBound_one : arithBound 1 = 1 := by simp [arithBound]

/-- `def:arithmetic-bound`: `B(2) = B(3) = B(4) = 2`. -/
lemma arithBound_of_two_le_le_four {n : ℕ} (h2 : 2 ≤ n) (h4 : n ≤ 4) : arithBound n = 2 := by
  unfold arithBound
  rw [if_neg (by omega)]
  exact if_pos h4

/-- `eq:arithmetic-bound` for `n ≥ 5`. -/
lemma arithBound_of_five_le {n : ℕ} (h : 5 ≤ n) :
    arithBound n = min n (arithBoundMax n) := by
  unfold arithBound
  rw [if_neg (by omega)]
  exact if_neg (by omega)

lemma three_le_arithBoundMax (n : ℕ) : 3 ≤ arithBoundMax n :=
  Finset.le_sup (f := id) (Finset.mem_insert_self 3 _)

lemma le_arithBoundMax_of_mem {n x : ℕ} (h : x ∈ arithCandidates n) : x ≤ arithBoundMax n :=
  Finset.le_sup (f := id) (Finset.mem_insert_of_mem h)

lemma arithBoundMax_le {n c : ℕ} (h3 : 3 ≤ c) (h : ∀ x ∈ arithCandidates n, x ≤ c) :
    arithBoundMax n ≤ c := by
  unfold arithBoundMax
  apply Finset.sup_le
  intro x hx
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact h3
  · exact h x hx

/-- Upper bounds on `B(n)` from bounds on every divisor candidate. -/
lemma arithBound_le_of_cands {n c : ℕ} (hn : 5 ≤ n) (h3 : 3 ≤ c)
    (h : ∀ e d, e ∣ d → d ∣ n → 4 ≤ e → 3 ≤ n / d → 4 + arithT e (d / e) ≤ c) :
    arithBound n ≤ c := by
  rw [arithBound_of_five_le hn]
  refine (min_le_right _ _).trans (arithBoundMax_le h3 ?_)
  intro x hx
  obtain ⟨_, e, d, h1, h2, h4, h5, rfl⟩ := mem_arithCandidates.1 hx
  exact h e d h1 h2 h4 h5

/-- Lower bound on `B(n)` from one divisor candidate. -/
lemma le_arithBound_of_cand {n e d : ℕ} (hn : 5 ≤ n) (h1 : e ∣ d) (h2 : d ∣ n) (h4 : 4 ≤ e)
    (h5 : 3 ≤ n / d) (hle : 4 + arithT e (d / e) ≤ n) : 4 + arithT e (d / e) ≤ arithBound n := by
  rw [arithBound_of_five_le hn]
  exact le_min hle (le_arithBoundMax_of_mem
    (mem_arithCandidates.2 ⟨by omega, e, d, h1, h2, h4, h5, rfl⟩))

lemma three_le_arithBound {n : ℕ} (hn : 5 ≤ n) : 3 ≤ arithBound n := by
  rw [arithBound_of_five_le hn]
  exact le_min (by omega) (three_le_arithBoundMax n)

lemma one_le_arithBound {n : ℕ} (hn : 1 ≤ n) : 1 ≤ arithBound n := by
  by_cases h1 : n = 1
  · subst h1; simp [arithBound_one]
  by_cases h4 : n ≤ 4
  · rw [arithBound_of_two_le_le_four (by omega) h4]; omega
  · have := three_le_arithBound (show 5 ≤ n by omega); omega

lemma two_le_arithBound {n : ℕ} (hn : 2 ≤ n) : 2 ≤ arithBound n := by
  by_cases h4 : n ≤ 4
  · rw [arithBound_of_two_le_le_four hn h4]
  · have := three_le_arithBound (show 5 ≤ n by omega); omega

/-- Candidates for a divisor `m` of `n` are candidates for `n`. -/
lemma arithCandidates_mono {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    arithCandidates m ⊆ arithCandidates n := by
  intro x hx
  obtain ⟨hm, e, d, h1, h2, h4, h5, rfl⟩ := mem_arithCandidates.1 hx
  refine mem_arithCandidates.2 ⟨hn, e, d, h1, h2.trans h, h4, ?_, rfl⟩
  exact h5.trans (Nat.div_le_div_right (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h))

/-- `prop:refined-budget` (monotone under divisibility): if `m ∣ n` and `m, n ≥ 1` then
`B(m) ≤ B(n)`. -/
theorem arithBound_mono {m n : ℕ} (hm : 1 ≤ m) (hn1 : 1 ≤ n) (h : m ∣ n) :
    arithBound m ≤ arithBound n := by
  have hn : n ≠ 0 := by omega
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h
  by_cases h1 : m = 1
  · subst h1
    rw [arithBound_one]
    exact one_le_arithBound (by omega)
  by_cases h4 : m ≤ 4
  · rw [arithBound_of_two_le_le_four (by omega) h4]
    exact two_le_arithBound (by omega)
  · rw [arithBound_of_five_le (by omega), arithBound_of_five_le (by omega)]
    refine min_le_min hmn ?_
    unfold arithBoundMax
    exact Finset.sup_mono (Finset.insert_subset_insert _ (arithCandidates_mono hn h))

/-- Each candidate is at most `Ω(n) + 2`. -/
lemma candidate_le_Omega {n e d : ℕ} (hn : n ≠ 0) (hed : e ∣ d) (hdn : d ∣ n) (he : 4 ≤ e)
    (h3 : 3 ≤ n / d) : 4 + arithT e (d / e) ≤ ArithmeticFunction.cardFactors n + 2 := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hdn
  have he0 : e ≠ 0 := by omega
  have hde : d / e ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hed)
    (by omega)).ne'
  have hnd : n / d ≠ 0 := by omega
  have hfac : n = (n / d) * (e * (d / e)) := by
    rw [Nat.mul_div_cancel' hed, Nat.div_mul_cancel hdn]
  have h1 : ArithmeticFunction.cardFactors n =
      ArithmeticFunction.cardFactors (n / d) +
        (ArithmeticFunction.cardFactors e + ArithmeticFunction.cardFactors (d / e)) := by
    conv_lhs => rw [hfac]
    rw [ArithmeticFunction.cardFactors_mul hnd (mul_ne_zero he0 hde),
      ArithmeticFunction.cardFactors_mul he0 hde]
  have h2 : 0 < ArithmeticFunction.cardFactors (n / d) :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
  have h3' : 0 < ArithmeticFunction.cardFactors e :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
  have h4 := arithT_le_Omega (e := e) hde
  omega

/-- `prop:refined-budget` (`B(n) ≤ Ω(n) + 2`), for `n ≥ 1`. -/
theorem arithBound_le_Omega_add_two {n : ℕ} (hn : 1 ≤ n) :
    arithBound n ≤ ArithmeticFunction.cardFactors n + 2 := by
  by_cases h1 : n = 1
  · subst h1; simp [arithBound_one]
  by_cases h4 : n ≤ 4
  · rw [arithBound_of_two_le_le_four (by omega) h4]
    have : 0 < ArithmeticFunction.cardFactors n :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
    omega
  · have hO : 0 < ArithmeticFunction.cardFactors n :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.2 (by omega)
    refine arithBound_le_of_cands (by omega) (by omega) ?_
    intro e d h1 h2 h4' h5
    exact candidate_le_Omega (by omega) h1 h2 h4' h5

/-! ### Closed formulas -/

section closed

private lemma twoVal_pow_two (a : ℕ) : twoVal (2 ^ a) = a := by
  unfold twoVal; exact padicValNat.prime_pow a

private lemma oddCount_pow_two (a : ℕ) : oddCount (2 ^ a) = 0 := by
  unfold oddCount
  rw [ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two, padicValNat.prime_pow]
  simp

private lemma twoVal_pow_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    twoVal (p ^ a) = 0 := by
  unfold twoVal
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm

private lemma oddCount_pow_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    oddCount (p ^ a) = a := by
  have := twoVal_pow_odd hp hp2 a
  unfold twoVal at this
  unfold oddCount
  rw [this, ArithmeticFunction.cardFactors_apply_prime_pow hp]
  rfl

/-- `T_e(2^m) = ⌊(2m + ε_e)/3⌋`. -/
lemma arithT_pow_two (e m : ℕ) : arithT e (2 ^ m) = (2 * m + epsE e) / 3 := by
  have : epsE e ≤ 1 := by unfold epsE; split_ifs <;> omega
  unfold arithT
  rw [twoVal_pow_two, oddCount_pow_two]
  omega

/-- `T_e(p^m) = m` for an odd prime `p`. -/
lemma arithT_pow_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e m : ℕ) :
    arithT e (p ^ m) = m := by
  have : epsE e ≤ 1 := by unfold epsE; split_ifs <;> omega
  unfold arithT
  rw [twoVal_pow_odd hp hp2, oddCount_pow_odd hp hp2]
  omega

/-- Divisor pairs of a prime power. -/
private lemma prime_pow_pair {p a e d : ℕ} (hp : p.Prime) (h1 : e ∣ d) (h2 : d ∣ p ^ a) :
    ∃ i k, i ≤ k ∧ k ≤ a ∧ e = p ^ i ∧ d = p ^ k := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).1 h2
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 h1
  exact ⟨i, k, (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h1 |>.trans le_rfl, hk, rfl, rfl⟩

private lemma pow_div_pow {p i k : ℕ} (hp : 1 < p) (h : i ≤ k) : p ^ k / p ^ i = p ^ (k - i) :=
  Nat.pow_div h (by omega)

/-- `prop:refined-budget` (closed formula for powers of two): `B(2^a) = 4 + ⌊2(a-4)/3⌋` for
`a ≥ 4`. -/
theorem arithBound_two_pow {a : ℕ} (ha : 4 ≤ a) :
    arithBound (2 ^ a) = 4 + 2 * (a - 4) / 3 := by
  have hn : 5 ≤ 2 ^ a := by
    have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  apply le_antisymm
  · refine arithBound_le_of_cands hn (by omega) ?_
    intro e d h1 h2 h4 h5
    obtain ⟨i, k, hik, hka, rfl, rfl⟩ := prime_pow_pair Nat.prime_two h1 h2
    rw [pow_div_pow (by norm_num) hik, arithT_pow_two]
    have hi : 2 ≤ i := by
      by_contra hlt
      have : 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk' : 2 ≤ a - k := by
      by_contra hlt
      rw [(Nat.pow_div hka (by norm_num) : 2 ^ a / 2 ^ k = 2 ^ (a - k))] at h5
      have : 2 ^ (a - k) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    by_cases hi2 : i = 2
    · subst hi2
      have : epsE (2 ^ 2) = 0 := by unfold epsE; simp
      rw [this]
      omega
    · have hi3 : 3 ≤ i := by omega
      have : epsE (2 ^ i) = 1 := by
        unfold epsE
        have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi3
        rw [if_neg (by omega)]
      rw [this]
      omega
  · have hd : 2 ^ 2 ∣ 2 ^ (a - 2) := pow_dvd_pow 2 (by omega)
    have hdn : 2 ^ (a - 2) ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
    have hq : 2 ^ a / 2 ^ (a - 2) = 2 ^ 2 := by
      rw [Nat.pow_div (by omega) (by norm_num)]
      congr 1; omega
    have hdiv : 2 ^ (a - 2) / 2 ^ 2 = 2 ^ (a - 4) := by
      rw [Nat.pow_div (by omega) (by norm_num)]
      congr 1
    have key := le_arithBound_of_cand (n := 2 ^ a) (e := 2 ^ 2) (d := 2 ^ (a - 2)) hn hd hdn
      (by norm_num) (by rw [hq]; norm_num) ?_
    · rw [hdiv, arithT_pow_two] at key
      have : epsE (2 ^ 2) = 0 := by unfold epsE; simp
      rw [this] at key
      simpa using key
    · rw [hdiv, arithT_pow_two]
      have : epsE (2 ^ 2) = 0 := by unfold epsE; simp
      rw [this]
      have := Nat.lt_two_pow_self (n := a)
      omega

/-- `prop:refined-budget` (closed formula for powers of three): `B(3^a) = a + 1` for `a ≥ 2`. -/
theorem arithBound_three_pow {a : ℕ} (ha : 2 ≤ a) : arithBound (3 ^ a) = a + 1 := by
  have hn : 5 ≤ 3 ^ a := by
    have : 3 ^ 2 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  apply le_antisymm
  · refine arithBound_le_of_cands hn (by omega) ?_
    intro e d h1 h2 h4 h5
    obtain ⟨i, k, hik, hka, rfl, rfl⟩ := prime_pow_pair Nat.prime_three h1 h2
    rw [pow_div_pow (by norm_num) hik, arithT_pow_odd Nat.prime_three (by norm_num)]
    have hi : 2 ≤ i := by
      by_contra hlt
      have : 3 ^ i ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk' : 1 ≤ a - k := by
      by_contra hlt
      rw [(Nat.pow_div hka (by norm_num) : 3 ^ a / 3 ^ k = 3 ^ (a - k))] at h5
      have : 3 ^ (a - k) = 3 ^ 0 := by congr 1; omega
      omega
    omega
  · by_cases ha2 : a = 2
    · subst ha2
      have := three_le_arithBound hn
      simpa using this
    · have hd : 3 ^ 2 ∣ 3 ^ (a - 1) := pow_dvd_pow 3 (by omega)
      have hdn : 3 ^ (a - 1) ∣ 3 ^ a := pow_dvd_pow 3 (by omega)
      have hq : 3 ^ a / 3 ^ (a - 1) = 3 := by
        rw [Nat.pow_div (by omega) (by norm_num)]
        have : a - (a - 1) = 1 := by omega
        rw [this]
      have hdiv : 3 ^ (a - 1) / 3 ^ 2 = 3 ^ (a - 3) := by
        rw [Nat.pow_div (by omega) (by norm_num)]
        congr 1
      have key := le_arithBound_of_cand (n := 3 ^ a) (e := 3 ^ 2) (d := 3 ^ (a - 1)) hn hd hdn
        (by norm_num) (by rw [hq]) ?_
      · rw [hdiv, arithT_pow_odd Nat.prime_three (by norm_num)] at key
        omega
      · rw [hdiv, arithT_pow_odd Nat.prime_three (by norm_num)]
        have := Nat.lt_pow_self (show 1 < 3 by norm_num) (n := a)
        omega

private lemma add_two_le_five_pow {a : ℕ} (ha : 1 ≤ a) : a + 2 ≤ 5 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- `prop:refined-budget` (closed formula for primes `p ≥ 5`): `B(p^a) = a + 2` for `a ≥ 1`. -/
theorem arithBound_prime_pow {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ha : 1 ≤ a) :
    arithBound (p ^ a) = a + 2 := by
  have hp2 : p ≠ 2 := by omega
  have hn : 5 ≤ p ^ a := by
    have : p ^ 1 ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
    rw [pow_one] at this
    omega
  apply le_antisymm
  · refine arithBound_le_of_cands hn (by omega) ?_
    intro e d h1 h2 h4 h5
    obtain ⟨i, k, hik, hka, rfl, rfl⟩ := prime_pow_pair hp h1 h2
    rw [pow_div_pow (by omega) hik, arithT_pow_odd hp hp2]
    have hi : 1 ≤ i := by
      by_contra hlt
      have : i = 0 := by omega
      subst this
      rw [pow_zero] at h4
      omega
    have hk' : 1 ≤ a - k := by
      by_contra hlt
      rw [(Nat.pow_div hka (by omega) : p ^ a / p ^ k = p ^ (a - k))] at h5
      have : p ^ (a - k) = p ^ 0 := by congr 1; omega
      rw [this, pow_zero] at h5
      omega
    omega
  · by_cases ha1 : a = 1
    · subst ha1
      have := three_le_arithBound hn
      simpa using this
    · have hd : p ^ 1 ∣ p ^ (a - 1) := pow_dvd_pow p (by omega)
      have hdn : p ^ (a - 1) ∣ p ^ a := pow_dvd_pow p (by omega)
      have hq : p ^ a / p ^ (a - 1) = p := by
        rw [Nat.pow_div (by omega) (by omega)]
        have : a - (a - 1) = 1 := by omega
        rw [this, pow_one]
      have hdiv : p ^ (a - 1) / p ^ 1 = p ^ (a - 2) := by
        rw [Nat.pow_div (by omega) (by omega)]
        congr 1
      have key := le_arithBound_of_cand (n := p ^ a) (e := p ^ 1) (d := p ^ (a - 1)) hn hd hdn
        (by simpa using (by omega : 4 ≤ p)) (by rw [hq]; omega) ?_
      · rw [hdiv, arithT_pow_odd hp hp2] at key
        omega
      · rw [hdiv, arithT_pow_odd hp hp2]
        have h1 : 5 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp5 a
        have h2 := add_two_le_five_pow ha
        omega

end closed

end SkewRibbonCoarsenings
