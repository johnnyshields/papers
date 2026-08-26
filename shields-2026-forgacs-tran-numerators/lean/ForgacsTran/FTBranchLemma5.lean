/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchUpper

/-!
# `Forgacs2017RationalDenominator` Lemma 5, the real-rootedness half

Their Lemma 5 has two halves.  The second — a unique negative zero when `r = 1` —
is `existsUnique_neg_root_ftCriticalReal`.  The first is that **every** zero of

  `R(t) = t^{2r} d/dt(-P(t)/t^r) = r t^{r-1} P(t) - t^r P'(t)`

is real.  Since `R = -X^{r-1}·E` with `E = ftCriticalReal P r = X·P' - C r·P`,
that is real-rootedness of `E`, and it is what lets the paper read both endpoints
of the branch off `t^{r-1}(rQ(t) - tQ'(t))`.

This module builds toward it.  Two local facts first, since both are needed by
the count and neither depends on it.

## Main statements

* `coeff_natDegree_ftCriticalReal` — `E`'s top coefficient is `(n - r)·lc P`,
  so `deg E = n` unless `n = r`, where the leading terms cancel.
* `sub_one_le_rootMultiplicity_ftCriticalReal` — a zero of `P` of multiplicity
  `m` is a zero of `E` of multiplicity at least `m - 1`.

## Implementation notes

**Differs from the paper's route.**  Their proof is the classical one for
`{k - r}` acting on a polynomial with only positive zeros.  In coefficients
`E = ∑ (k - r) a_k t^k`, so this is a multiplier-sequence statement; Mathlib
carries no Pólya--Schur theory, so the route here is a root count instead —
`m - 1` at each zero of `P` of multiplicity `m`, one between each consecutive
pair, and one more outside — which sums to `deg E`.

Sorry-free.

## Tags

real-rootedness, denominator pencil, Forgacs-Tran
-/

namespace ForgacsTran

open Polynomial

/-- **`E`'s top coefficient.**  `E = X·P' - C r·P` multiplies the `k`th
coefficient of `P` by `k - r`, so at the top it is `(n - r)·lc P`. -/
theorem coeff_natDegree_ftCriticalReal (P : Polynomial ℝ) (r : ℕ) :
    (ftCriticalReal P r).coeff P.natDegree
      = ((P.natDegree : ℝ) - r) * P.leadingCoeff := by
  rcases Nat.eq_zero_or_pos P.natDegree with h | h
  · have h0 : (X * derivative P).coeff P.natDegree = 0 := by rw [h]; simp
    rw [ftCriticalReal, coeff_sub, h0, coeff_C_mul, leadingCoeff, h]
    push_cast
    ring
  · obtain ⟨m, hm⟩ : ∃ m, P.natDegree = m + 1 := ⟨P.natDegree - 1, by omega⟩
    rw [ftCriticalReal, coeff_sub, coeff_C_mul, leadingCoeff, hm, coeff_X_mul,
      coeff_derivative]
    push_cast
    ring

/-- `deg E = n` whenever `n ≠ r`; at `n = r` the leading terms cancel. -/
theorem natDegree_ftCriticalReal (P : Polynomial ℝ) (r : ℕ) (hP : P ≠ 0)
    (hnr : P.natDegree ≠ r) : (ftCriticalReal P r).natDegree = P.natDegree := by
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP
  have hne : ((P.natDegree : ℝ) - r) ≠ 0 := fun h => hnr (by exact_mod_cast sub_eq_zero.1 h)
  refine le_antisymm ?_ (le_natDegree_of_ne_zero ?_)
  · rw [ftCriticalReal]
    refine (natDegree_sub_le_of_le ?_ ?_).trans (le_of_eq (max_self _))
    · rcases eq_or_ne (derivative P) 0 with hd | hd
      · simp [hd]
      · rw [natDegree_X_mul hd]
        have hnd : P.natDegree ≠ 0 := by
          intro h
          obtain ⟨b, hb⟩ := natDegree_eq_zero.1 h
          exact hd (by rw [← hb, derivative_C])
        have := natDegree_derivative_lt hnd
        omega
    · exact (natDegree_C_mul_le _ _).trans le_rfl
  · rw [coeff_natDegree_ftCriticalReal]
    exact mul_ne_zero hne hlc

/-- **Multiplicity transfer.**  A zero of `P` of multiplicity `m` is a zero of
`E` of multiplicity at least `m - 1`: writing `P = (X - C σ)^m Q`, the factor
`(X - C σ)^(m-1)` survives both `X·P'` and `C r·P`. -/
theorem sub_one_le_rootMultiplicity_ftCriticalReal {P : Polynomial ℝ} {r : ℕ}
    (hE : ftCriticalReal P r ≠ 0) (σ : ℝ) :
    P.rootMultiplicity σ - 1 ≤ (ftCriticalReal P r).rootMultiplicity σ := by
  classical
  rcases Nat.eq_zero_or_pos (P.rootMultiplicity σ) with h0 | hpos
  · simp [h0]
  obtain ⟨j, hj⟩ : ∃ j, P.rootMultiplicity σ = j + 1 :=
    ⟨P.rootMultiplicity σ - 1, by omega⟩
  obtain ⟨Q, hQ⟩ := P.pow_rootMultiplicity_dvd σ
  rw [hj] at hQ
  have hd : derivative P
      = (X - C σ) ^ j * (C ((j : ℝ) + 1) * Q + (X - C σ) * derivative Q) := by
    rw [hQ, derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [le_rootMultiplicity_iff hE, hj, Nat.add_sub_cancel]
  refine ⟨X * (C ((j : ℝ) + 1) * Q + (X - C σ) * derivative Q)
    - C (r : ℝ) * ((X - C σ) * Q), ?_⟩
  rw [ftCriticalReal, hd, hQ]
  ring

/-- **Interleaving.**  Between two zeros of `P` with none of `P` strictly
between lies a zero of `E`, so the distinct zeros of `P` are at most one more
than those of `E` outside `P`.  This is `Polynomial.card_roots_toFinset_le_
card_roots_derivative_sdiff_roots_succ` with `E` in place of the derivative;
the interleaving step is `exists_ftCriticalReal_root_between`. -/
theorem card_roots_toFinset_le_ftCriticalReal_sdiff_succ {P : Polynomial ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hpos : ∀ x ∈ P.roots, 0 < x) (hE : ftCriticalReal P r ≠ 0) :
    P.roots.toFinset.card
      ≤ ((ftCriticalReal P r).roots.toFinset \ P.roots.toFinset).card + 1 := by
  classical
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy _ => ?_
  rw [Multiset.mem_toFinset] at hx hy
  have hx0 : 0 < x := hpos x hx
  rw [mem_roots hP] at hx hy
  obtain ⟨ξ, hξ, hξ0⟩ := exists_ftCriticalReal_root_between hr hx0 hxy hx hy
  exact ⟨ξ, by rw [Multiset.mem_toFinset, mem_roots hE]; exact hξ0, hξ.1, hξ.2⟩

/-- **The count.**  `E` has at least `deg P - 1` real zeros, counted with
multiplicity: `m - 1` at each zero of `P` of multiplicity `m`, and one between
each consecutive pair.  Mirrors `Polynomial.card_roots_le_derivative`. -/
theorem card_roots_le_ftCriticalReal {P : Polynomial ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hpos : ∀ x ∈ P.roots, 0 < x) (hE : ftCriticalReal P r ≠ 0) :
    Multiset.card P.roots ≤ Multiset.card (ftCriticalReal P r).roots + 1 := by
  classical
  set E := ftCriticalReal P r with hEdef
  calc Multiset.card P.roots = ∑ x ∈ P.roots.toFinset, P.roots.count x :=
        (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ P.roots.toFinset, (P.roots.count x - 1 + 1) :=
        (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
          Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x ∈ P.roots.toFinset, (P.rootMultiplicity x - 1)) + P.roots.toFinset.card := by
        simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x ∈ P.roots.toFinset, E.rootMultiplicity x)
          + ((E.roots.toFinset \ P.roots.toFinset).card + 1) :=
        add_le_add
          (Finset.sum_le_sum fun x _ => sub_one_le_rootMultiplicity_ftCriticalReal hE x)
          (card_roots_toFinset_le_ftCriticalReal_sdiff_succ hr hpos hE)
    _ ≤ (∑ x ∈ P.roots.toFinset, E.roots.count x)
          + ((∑ x ∈ E.roots.toFinset \ P.roots.toFinset, E.roots.count x) + 1) := by
        simp only [← count_roots, Finset.card_eq_sum_ones]
        gcongr with x hx
        rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
        exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card E.roots + 1 := by
        rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
          Finset.union_sdiff_self_eq_union, ← Multiset.toFinset_sum_count_eq,
          ← Finset.sum_subset Finset.subset_union_right]
        intro x _ hx₂
        simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

/-- `deg E ≤ deg P` always; equality unless `n = r`. -/
theorem natDegree_ftCriticalReal_le (P : Polynomial ℝ) (r : ℕ) :
    (ftCriticalReal P r).natDegree ≤ P.natDegree := by
  rw [ftCriticalReal]
  refine (natDegree_sub_le_of_le ?_ ?_).trans (le_of_eq (max_self _))
  · rcases eq_or_ne (derivative P) 0 with hd | hd
    · simp [hd]
    · rw [natDegree_X_mul hd]
      have hnd : P.natDegree ≠ 0 := by
        intro h
        obtain ⟨b, hb⟩ := natDegree_eq_zero.1 h
        exact hd (by rw [← hb, derivative_C])
      have := natDegree_derivative_lt hnd
      omega
  · exact (natDegree_C_mul_le _ _).trans le_rfl

/-- **A real polynomial cannot have exactly one non-real zero.**  So a real-zero
count within one of the degree is the degree.  Formalized without passing to
`ℂ`: the missing factor would have degree one, and a real linear polynomial has
a real zero. -/
theorem card_roots_eq_natDegree_of_sub_one_le {p : Polynomial ℝ} (hp : p ≠ 0)
    (h : p.natDegree - 1 ≤ Multiset.card p.roots) :
    Multiset.card p.roots = p.natDegree := by
  classical
  refine le_antisymm (card_roots' p) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hcard : Multiset.card p.roots = p.natDegree - 1 := by omega
  have hdeg1 : 1 ≤ p.natDegree := by omega
  obtain ⟨g, hg⟩ := p.prod_multiset_X_sub_C_dvd
  have hg0 : g ≠ 0 := fun hz => hp (by rw [hg, hz, mul_zero])
  have hP0 : (p.roots.map fun a => X - C a).prod ≠ 0 := fun hz => hp (by rw [hg, hz, zero_mul])
  have hdegP : ((p.roots.map fun a => X - C a).prod).natDegree = Multiset.card p.roots :=
    natDegree_multiset_prod_X_sub_C_eq_card _
  have hdegg : g.natDegree = 1 := by
    have hmul := natDegree_mul hP0 hg0
    rw [← hg, hdegP, hcard] at hmul
    omega
  obtain ⟨u, hu, v, huv⟩ := natDegree_eq_one.1 hdegg
  have hroot : g.eval (-v / u) = 0 := by
    rw [← huv]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    field
  have hmem : (-v / u) ∈ g.roots := (mem_roots hg0).2 hroot
  have hroots : p.roots = (p.roots.map fun a => X - C a).prod.roots + g.roots := by
    conv_lhs => rw [hg]
    exact roots_mul (by rw [← hg]; exact hp)
  rw [roots_multiset_prod_X_sub_C] at hroots
  have hc := congrArg Multiset.card hroots
  rw [Multiset.card_add] at hc
  have : Multiset.card g.roots = 0 := by omega
  rw [Multiset.card_eq_zero] at this
  rw [this] at hmem
  exact absurd hmem (Multiset.notMem_zero _)

/-- **`Forgacs2017RationalDenominator` Lemma 5, the real-rootedness half.**  If
`P` has only positive real zeros then every zero of `E = X·P' - C r·P` is real,
hence so is every zero of their `R(t) = r t^{r-1}P(t) - t^r P'(t) = -t^{r-1}E(t)`.

The count gives `deg E - 1` zeros directly — `m - 1` at each zero of `P` of
multiplicity `m`, one between each consecutive pair — and the parity step
supplies the last, since a real polynomial cannot have exactly one non-real
zero. -/
theorem card_roots_ftCriticalReal_eq_natDegree {P : Polynomial ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hpos : ∀ x ∈ P.roots, 0 < x)
    (hall : Multiset.card P.roots = P.natDegree) (hE : ftCriticalReal P r ≠ 0) :
    Multiset.card (ftCriticalReal P r).roots = (ftCriticalReal P r).natDegree := by
  refine card_roots_eq_natDegree_of_sub_one_le hE ?_
  have h1 := card_roots_le_ftCriticalReal hr hpos hE
  have h2 := natDegree_ftCriticalReal_le P r
  omega

/-- The pencil has degree `n`. -/
theorem natDegree_ftRootPolyReal {n : ℕ} {c : ℝ} (hc : c ≠ 0) (a : Fin n → ℝ) :
    (ftRootPolyReal c a).natDegree = n := by
  classical
  have hlin : ∀ k : Fin n, (C (a k) - X : Polynomial ℝ).natDegree = 1 := fun k => by
    rw [show (C (a k) - X : Polynomial ℝ) = -(X - C (a k)) by ring, natDegree_neg,
      natDegree_X_sub_C]
  rw [ftRootPolyReal, natDegree_C_mul hc, natDegree_prod]
  · simp [hlin]
  · intro k _ hz
    have := hlin k
    rw [hz] at this
    simp at this

/-- Each linear factor is nonzero, so the pencil is. -/
theorem ftRootPolyReal_ne_zero {n : ℕ} {c : ℝ} (hc : c ≠ 0) (a : Fin n → ℝ) :
    ftRootPolyReal c a ≠ 0 := by
  classical
  have hlin : ∀ k : Fin n, (C (a k) - X : Polynomial ℝ) ≠ 0 := fun k hz => by
    have : (C (a k) - X : Polynomial ℝ).natDegree = 1 := by
      rw [show (C (a k) - X : Polynomial ℝ) = -(X - C (a k)) by ring, natDegree_neg,
        natDegree_X_sub_C]
    rw [hz, natDegree_zero] at this
    exact absurd this (by norm_num)
  rw [ftRootPolyReal]
  exact mul_ne_zero (C_ne_zero.2 hc) (Finset.prod_ne_zero_iff.2 fun k _ => hlin k)

/-- The pencil splits, so its real zeros already exhaust its degree. -/
theorem splits_ftRootPolyReal {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    Polynomial.Splits (ftRootPolyReal c a) := by
  classical
  have hlin : ∀ k : Fin n, Polynomial.Splits (C (a k) - X : Polynomial ℝ) := fun k => by
    rw [show (C (a k) - X : Polynomial ℝ) = C (-1 : ℝ) * (X - C (a k)) by
      simp only [C_neg, C_1]; ring]
    exact (Polynomial.Splits.of_natDegree_eq_zero (natDegree_C _)).mul
      (Polynomial.Splits.of_natDegree_le_one_of_monic
        (by rw [natDegree_X_sub_C]) (monic_X_sub_C _))
  rw [ftRootPolyReal]
  exact (Polynomial.Splits.of_natDegree_eq_zero (natDegree_C _)).mul
    (Polynomial.Splits.prod fun k _ => hlin k)

/-- Every zero of the pencil is one of its `a k`, hence positive. -/
theorem pos_of_mem_roots_ftRootPolyReal {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (hc : c ≠ 0)
    (ha : ∀ k, 0 < a k) {x : ℝ} (hx : x ∈ (ftRootPolyReal c a).roots) : 0 < x := by
  classical
  have h0 : (ftRootPolyReal c a).eval x = 0 :=
    (mem_roots (ftRootPolyReal_ne_zero hc a)).1 hx
  rw [eval_ftRootPolyReal] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h hc
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    have hxk : x = a k := by linarith [sub_eq_zero.1 hk]
    rw [hxk]; exact ha k

/-- **`Forgacs2017RationalDenominator` Lemma 5, first half, at the pencil.**
For `Q(t) = c∏(a_k - t)` with every `a_k > 0`, every zero of
`E = X·Q' - C r·Q` is real, hence every zero of their
`R(t) = r t^{r-1}Q(t) - t^r Q'(t)` is.

There is **no** `n ≠ r` hypothesis.  The leading terms of `E` do cancel at
`n = r`, but `E ≠ 0` does not have to come from the leading coefficient: were
`E` zero then `t·Q'(t) = r·Q(t)` identically, and evaluating that at `0` forces
`Q(0) = 0`, while `Q(0) = c∏a_k ≠ 0`. -/
theorem card_roots_ftCriticalReal_ftRootPolyReal {n r : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) :
    Multiset.card (ftCriticalReal (ftRootPolyReal c a) r).roots
      = (ftCriticalReal (ftRootPolyReal c a) r).natDegree := by
  classical
  have hE : ftCriticalReal (ftRootPolyReal c a) r ≠ 0 := by
    intro hz
    have h0 : (ftCriticalReal (ftRootPolyReal c a) r).eval 0 = 0 := by rw [hz]; simp
    rw [eval_ftCriticalReal, eval_ftRootPolyReal] at h0
    have hprod : (0 : ℝ) < ∏ k, (a k - 0) :=
      Finset.prod_pos fun k _ => by simpa using ha k
    have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le one_pos hr
    have : (r : ℝ) * (c * ∏ k, (a k - 0)) = 0 := by linarith [h0]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt hr0)
    · rcases mul_eq_zero.1 h with h' | h'
      · exact hc h'
      · exact absurd h' (ne_of_gt hprod)
  exact card_roots_ftCriticalReal_eq_natDegree hr
    (fun x hx => pos_of_mem_roots_ftRootPolyReal hc ha hx)
    (Polynomial.splits_iff_card_roots.1 (splits_ftRootPolyReal c a)) hE

end ForgacsTran
