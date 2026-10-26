/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/ArithmeticOptimization.lean
import Mathlib

/-!
# The arithmetic optimization of ratio lists

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:depth`
(`eq:T`, `lem:arithmetic-optimization`).

`arithT e D` is the quantity `T_e(D)` of `eq:T`, and `IsRatioList e D l` says that `l` is a list
of integers at least two whose product divides `D`, with no two adjacent entries equal to two and
(when `e = 4`) with first entry different from two.  The largest length of such a list is
`arithT e D`.  Sorry-free.
-/

open scoped ArithmeticFunction.Omega

namespace SkewRibbonCoarsenings

/-- The exponent `a₂ = ν₂(D)` of two in `D`. -/
def twoVal (D : ℕ) : ℕ := padicValNat 2 D

/-- The count `a_o = Ω(D) - a₂` of odd prime factors of `D`, with multiplicity. -/
def oddCount (D : ℕ) : ℕ := ArithmeticFunction.cardFactors D - padicValNat 2 D

/-- The constant `ε_e` of `eq:T`: `0` for `e = 4` and `1` for `e ≥ 5`. -/
def epsE (e : ℕ) : ℕ := if e = 4 then 0 else 1

/-- `eq:T`: `T_e(D) = min {a₂ + a_o, ⌊(2a₂ + 4a_o + ε_e)/3⌋}`. -/
def arithT (e D : ℕ) : ℕ :=
  min (twoVal D + oddCount D) ((2 * twoVal D + 4 * oddCount D + epsE e) / 3)

/-- A list of integers at least two whose product divides `D`, with no two adjacent entries equal
to two and, when `e = 4`, with first entry different from two (the lists of
`lem:arithmetic-optimization`). -/
def IsRatioList (e D : ℕ) (l : List ℕ) : Prop :=
  (∀ x ∈ l, 2 ≤ x) ∧ l.prod ∣ D ∧ l.IsChain (fun a b => ¬ (a = 2 ∧ b = 2)) ∧
    (e = 4 → l.head? ≠ some 2)

section helpers

private lemma nu_le_Omega {x : ℕ} (hx : x ≠ 0) :
    padicValNat 2 x ≤ ArithmeticFunction.cardFactors x := by
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := 2) (n := x)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    exact hx hm
  have h := ArithmeticFunction.cardFactors_mul (pow_ne_zero (padicValNat 2 x) two_ne_zero) hm0
  rw [← hm, ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two] at h
  omega

private lemma twoVal_mul {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    twoVal (x * y) = twoVal x + twoVal y := by
  unfold twoVal
  exact padicValNat.mul hx hy

private lemma oddCount_mul {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    oddCount (x * y) = oddCount x + oddCount y := by
  have h1 := nu_le_Omega hx
  have h2 := nu_le_Omega hy
  have h3 : padicValNat 2 (x * y) = padicValNat 2 x + padicValNat 2 y := padicValNat.mul hx hy
  unfold oddCount
  rw [ArithmeticFunction.cardFactors_mul hx hy, h3]
  omega

/-- `twoVal` is monotone under divisibility. -/
lemma twoVal_le_of_dvd {x y : ℕ} (hy : y ≠ 0) (h : x ∣ y) : twoVal x ≤ twoVal y := by
  obtain ⟨m, rfl⟩ := h
  have hx : x ≠ 0 := left_ne_zero_of_mul hy
  have hm : m ≠ 0 := right_ne_zero_of_mul hy
  rw [twoVal_mul hx hm]
  omega

/-- `oddCount` is monotone under divisibility. -/
lemma oddCount_le_of_dvd {x y : ℕ} (hy : y ≠ 0) (h : x ∣ y) : oddCount x ≤ oddCount y := by
  obtain ⟨m, rfl⟩ := h
  have hx : x ≠ 0 := left_ne_zero_of_mul hy
  have hm : m ≠ 0 := right_ne_zero_of_mul hy
  rw [oddCount_mul hx hm]
  omega

/-- `T_e` is monotone under divisibility of its argument. -/
lemma arithT_mono {e x y : ℕ} (hy : y ≠ 0) (h : x ∣ y) : arithT e x ≤ arithT e y := by
  have h1 := twoVal_le_of_dvd hy h
  have h2 := oddCount_le_of_dvd hy h
  unfold arithT
  apply min_le_min <;> omega

/-- `T_e(D) ≤ a₂ + a_o = Ω(D)`. -/
lemma arithT_le_Omega {e D : ℕ} (hD : D ≠ 0) :
    arithT e D ≤ ArithmeticFunction.cardFactors D := by
  have h1 := nu_le_Omega hD
  have : arithT e D ≤ twoVal D + oddCount D := min_le_left _ _
  unfold twoVal oddCount at this
  omega

private lemma weight_two : twoVal 2 = 1 ∧ oddCount 2 = 0 := by
  have h1 : padicValNat 2 2 = 1 := padicValNat_self
  have h2 : ArithmeticFunction.cardFactors 2 = 1 :=
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two
  unfold twoVal oddCount
  omega

private lemma weight_pos {x : ℕ} (hx : 2 ≤ x) : 1 ≤ twoVal x + oddCount x := by
  have h1 := nu_le_Omega (show x ≠ 0 by omega)
  have h2 : 0 < ArithmeticFunction.cardFactors x :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.2 hx
  unfold twoVal oddCount
  omega

private lemma weight_ne_two {x : ℕ} (hx : 2 ≤ x) (hx2 : x ≠ 2) :
    4 ≤ 2 * twoVal x + 4 * oddCount x := by
  have h1 := nu_le_Omega (show x ≠ 0 by omega)
  have h2 := weight_pos hx
  by_contra hcon
  have ho : oddCount x = 0 := by omega
  have hv : twoVal x = 1 := by omega
  have hO : ArithmeticFunction.cardFactors x = 1 := by
    unfold twoVal oddCount at *
    omega
  have hp : x.Prime := ArithmeticFunction.cardFactors_eq_one_iff_prime.1 hO
  have hd : 2 ∣ x := dvd_of_one_le_padicValNat (by unfold twoVal at hv; omega)
  exact hx2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd).symm

private lemma twoVal_prod : ∀ l : List ℕ, (∀ x ∈ l, x ≠ 0) →
    twoVal l.prod = (l.map twoVal).sum
  | [], _ => by simp [twoVal]
  | x :: r, h => by
    have hx : x ≠ 0 := h x (by simp)
    have hr : ∀ y ∈ r, y ≠ 0 := fun y hy => h y (by simp [hy])
    have hrp : r.prod ≠ 0 := List.prod_ne_zero (fun h0 => hr 0 h0 rfl)
    rw [List.prod_cons, twoVal_mul hx hrp, twoVal_prod r hr]
    simp

private lemma oddCount_prod : ∀ l : List ℕ, (∀ x ∈ l, x ≠ 0) →
    oddCount l.prod = (l.map oddCount).sum
  | [], _ => by simp [oddCount]
  | x :: r, h => by
    have hx : x ≠ 0 := h x (by simp)
    have hr : ∀ y ∈ r, y ≠ 0 := fun y hy => h y (by simp [hy])
    have hrp : r.prod ≠ 0 := List.prod_ne_zero (fun h0 => hr 0 h0 rfl)
    rw [List.prod_cons, oddCount_mul hx hrp, oddCount_prod r hr]
    simp

private lemma length_le_weights : ∀ l : List ℕ, (∀ x ∈ l, 2 ≤ x) →
    l.length ≤ (l.map twoVal).sum + (l.map oddCount).sum
  | [], _ => by simp
  | x :: r, h => by
    have hx := weight_pos (h x (by simp))
    have hr := length_le_weights r (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private lemma potential : ∀ l : List ℕ, (∀ x ∈ l, 2 ≤ x) →
    l.IsChain (fun a b => ¬ (a = 2 ∧ b = 2)) →
    3 * l.length ≤ 2 * (l.map twoVal).sum + 4 * (l.map oddCount).sum + 1 ∧
      (l.head? ≠ some 2 → 3 * l.length ≤ 2 * (l.map twoVal).sum + 4 * (l.map oddCount).sum)
  | [], _, _ => by simp
  | x :: r, h, hc => by
    have hx2 : 2 ≤ x := h x (by simp)
    have hrc : r.IsChain (fun a b => ¬ (a = 2 ∧ b = 2)) := hc.tail
    have ih := potential r (fun y hy => h y (by simp [hy])) hrc
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.head?_cons]
    by_cases hx : x = 2
    · subst hx
      obtain ⟨hw1, hw2⟩ := weight_two
      have hhead : r.head? ≠ some 2 := by
        cases r with
        | nil => simp
        | cons y t =>
          intro hy
          simp only [List.head?_cons, Option.some.injEq] at hy
          subst hy
          simp at hc
      have := ih.2 hhead
      rw [hw1, hw2]
      refine ⟨by omega, fun hh => (hh rfl).elim⟩
    · have hw := weight_ne_two hx2 hx
      have := ih.1
      refine ⟨by omega, fun _ => by omega⟩

end helpers

/-- `lem:arithmetic-optimization`, upper bound: every list of the stated kind has length at most
`T_e(D)`. -/
theorem ratioList_length_le {e D : ℕ} (hD : D ≠ 0) {l : List ℕ} (hl : IsRatioList e D l) :
    l.length ≤ arithT e D := by
  obtain ⟨h2, hdvd, hc, hhead⟩ := hl
  have hne : ∀ x ∈ l, x ≠ 0 := fun x hx => by have := h2 x hx; omega
  have hprod : twoVal l.prod ≤ twoVal D := twoVal_le_of_dvd hD hdvd
  have hprod' : oddCount l.prod ≤ oddCount D := oddCount_le_of_dvd hD hdvd
  rw [twoVal_prod l hne] at hprod
  rw [oddCount_prod l hne] at hprod'
  have h1 := length_le_weights l h2
  obtain ⟨p1, p2⟩ := potential l h2 hc
  unfold arithT
  apply le_min
  · omega
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    by_cases he : e = 4
    · have := p2 (hhead he)
      unfold epsE
      simp only [he, ite_true]
      omega
    · unfold epsE
      simp only [he, ite_false]
      omega

private lemma chain_cons_of_head (x : ℕ) (l : List ℕ)
    (hc : l.IsChain (fun a b => ¬ (a = 2 ∧ b = 2))) (hh : x = 2 → l.head? ≠ some 2) :
    (x :: l).IsChain (fun a b => ¬ (a = 2 ∧ b = 2)) := by
  cases l with
  | nil => exact List.isChain_singleton x
  | cons y t =>
    rw [List.isChain_cons_cons]
    refine ⟨?_, hc⟩
    rintro ⟨h1, h2⟩
    exact hh h1 (by simp [h2])

/-- The construction behind the attainability half of `lem:arithmetic-optimization`: with
`a` twos and a list `ps` of entries at least three available, lists of length
`min (a + |ps|) ⌊(2a + 4|ps| + ε)/3⌋` exist. -/
private theorem construct : ∀ (n a : ℕ) (ps : List ℕ) (ε : ℕ), a + ps.length = n → ε ≤ 1 →
    (∀ p ∈ ps, 3 ≤ p) →
    ∃ l : List ℕ, (∀ x ∈ l, 2 ≤ x) ∧ l.prod ∣ 2 ^ a * ps.prod ∧
      l.IsChain (fun a b => ¬ (a = 2 ∧ b = 2)) ∧ (ε = 0 → l.head? ≠ some 2) ∧
      l.length = min (a + ps.length) ((2 * a + 4 * ps.length + ε) / 3) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ps ε hn hε hps
    -- peel an odd entry when possible and permitted
    by_cases hε1 : ε = 1 ∧ 1 ≤ a
    · obtain ⟨rfl, ha⟩ := hε1
      obtain ⟨l, h2, hd, hc, hh, hlen⟩ := ih (n - 1) (by omega) (a - 1) ps 0 (by omega)
        (by omega) hps
      refine ⟨2 :: l, ?_, ?_, ?_, by simp, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_rfl
        · exact h2 x hx
      · have : 2 ^ a = 2 * 2 ^ (a - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [List.prod_cons, this, mul_assoc]
        exact mul_dvd_mul_left 2 hd
      · exact chain_cons_of_head 2 l hc (fun _ => hh rfl)
      · simp only [List.length_cons, hlen]
        omega
    · rcases ps with _ | ⟨p, t⟩
      · -- no odd entries
        by_cases ha2 : 2 ≤ a ∧ ε = 0
        · obtain ⟨ha, rfl⟩ := ha2
          obtain ⟨l, h2, hd, hc, hh, hlen⟩ :=
            ih (n - 2) (by simp at hn; omega) (a - 2) [] 1 (by simp at hn ⊢; omega) le_rfl
              (by simp)
          refine ⟨4 :: l, ?_, ?_, ?_, by simp, ?_⟩
          · intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · norm_num
            · exact h2 x hx
          · have : 2 ^ a = 4 * 2 ^ (a - 2) := by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
              congr 1
              omega
            simp only [List.prod_nil, mul_one] at hd ⊢
            rw [List.prod_cons, this]
            exact mul_dvd_mul_left 4 hd
          · exact chain_cons_of_head 4 l hc (fun h => absurd h (by norm_num))
          · simp only [List.length_nil, List.length_cons, hlen] at hlen ⊢
            omega
        · refine ⟨[], by simp, by simp, List.isChain_nil, by simp, ?_⟩
          simp only [List.length_nil, List.length_nil]
          omega
      · -- peel the odd entry `p`
        have hp3 : 3 ≤ p := hps p (by simp)
        obtain ⟨l, h2, hd, hc, hh, hlen⟩ :=
          ih (n - 1) (by simp at hn; omega) a t 1 (by simp at hn; omega) le_rfl
            (fun q hq => hps q (by simp [hq]))
        refine ⟨p :: l, ?_, ?_, ?_, by simp; omega, ?_⟩
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · omega
          · exact h2 x hx
        · rw [List.prod_cons, List.prod_cons, mul_left_comm]
          exact mul_dvd_mul_left p hd
        · exact chain_cons_of_head p l hc (fun h => by omega)
        · simp only [List.length_cons, hlen] at hlen ⊢
          have hpos : ¬ (ε = 1 ∧ 1 ≤ a) := hε1
          omega

/-- `lem:arithmetic-optimization`, attainability: for `e ≥ 4` and `D ≥ 1` there is a list of the
stated kind of length exactly `T_e(D)`. -/
theorem exists_ratioList_length_eq {e D : ℕ} (hD : D ≠ 0) :
    ∃ l : List ℕ, IsRatioList e D l ∧ l.length = arithT e D := by
  obtain ⟨a, m, hm, hDm⟩ := Nat.exists_eq_two_pow_mul_odd hD
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hm2 : ¬ 2 ∣ m := by
    rintro h
    obtain ⟨k, hk⟩ := hm
    omega
  have hnu : twoVal D = a := by
    unfold twoVal
    rw [hDm, padicValNat.mul (pow_ne_zero _ two_ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm2]
    simp
  have hOm : ArithmeticFunction.cardFactors D = a + ArithmeticFunction.cardFactors m := by
    rw [hDm, ArithmeticFunction.cardFactors_mul (pow_ne_zero _ two_ne_zero) hm0,
      ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]
  have hao : oddCount D = m.primeFactorsList.length := by
    unfold oddCount
    have : padicValNat 2 D = a := hnu
    rw [this, hOm, ArithmeticFunction.cardFactors_apply]
    omega
  have hps : ∀ p ∈ m.primeFactorsList, 3 ≤ p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hpd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
    have h2 := hpp.two_le
    by_contra hlt
    have : p = 2 := by omega
    subst this
    exact hm2 hpd
  have hε : epsE e ≤ 1 := by unfold epsE; split_ifs <;> omega
  obtain ⟨l, h2, hd, hc, hh, hlen⟩ :=
    construct _ a m.primeFactorsList (epsE e) rfl hε hps
  refine ⟨l, ⟨h2, ?_, hc, ?_⟩, ?_⟩
  · rw [Nat.prod_primeFactorsList hm0] at hd
    rwa [hDm]
  · intro he
    apply hh
    unfold epsE
    simp [he]
  · rw [hlen]
    unfold arithT
    rw [hnu, hao]

/-- `lem:arithmetic-optimization`: for `e ≥ 4` and `D ≥ 1`, the largest length of a list of
integers at least two whose product divides `D`, with no adjacent entries equal to two and with
first entry different from two when `e = 4`, is `T_e(D)`. -/
theorem arithmetic_optimization {e D : ℕ} (_he : 4 ≤ e) (hD : 1 ≤ D) :
    IsGreatest {k : ℕ | ∃ l : List ℕ, IsRatioList e D l ∧ l.length = k} (arithT e D) := by
  have hD0 : D ≠ 0 := by omega
  refine ⟨exists_ratioList_length_eq hD0, ?_⟩
  rintro k ⟨l, hl, rfl⟩
  exact ratioList_length_le hD0 hl

end SkewRibbonCoarsenings
