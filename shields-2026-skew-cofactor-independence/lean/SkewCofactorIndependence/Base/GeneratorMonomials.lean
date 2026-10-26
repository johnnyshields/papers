/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/GeneratorMonomials.lean
import SkewCofactorIndependence.Base.CompleteRing
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Count

/-!
# Free-generator monomials and exchange recognition

Exact free-generator algebra for "Capped cofactors and admissible convex weights"
(`sec:coordinates`) and the reduced three-index exchange in `lem:two-cofactor-reconstruction`.
Zero indices contribute the unit and are deliberately invisible. Sorry-free.
-/

namespace SkewCofactorIndependence.Base

/-- A natural complete index contributes one exponent, except that zero contributes none. -/
noncomputable def completeIndexExponent (k : ℕ) : ℕ+ →₀ ℕ :=
  if hk : 0 < k then Finsupp.single (⟨k, hk⟩ : ℕ+) 1 else 0

/-- The exponent vector of a list of complete indices, omitting every zero index. -/
noncomputable def exponentVector (l : List ℕ) : ℕ+ →₀ ℕ :=
  (l.map completeIndexExponent).sum

/-- The visible multiset of a generator product. -/
def positiveIndexMultiset (l : List ℕ) : Multiset ℕ :=
  (l : Multiset ℕ).filter (fun k => 0 < k)

theorem complete_eq_monomial_index (k : ℕ) :
    complete (k : ℤ) = MvPolynomial.monomial (completeIndexExponent k) (1 : ℤ) := by
  cases k with
  | zero => simp [completeIndexExponent]
  | succ k =>
      let p : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
      have hc : complete ((k + 1 : ℕ) : ℤ) = MvPolynomial.X p := complete_nat p
      rw [hc]
      simp only [completeIndexExponent, dite_eq_left (Nat.succ_pos k), MvPolynomial.X]
      congr 2

/-- Products of complete generators have exactly the sum of their visible exponents. -/
theorem prod_complete_eq_monomial (l : List ℕ) :
    (l.map (fun k : ℕ => complete (k : ℤ))).prod =
      MvPolynomial.monomial (exponentVector l) (1 : ℤ) := by
  induction l with
  | nil => simp [exponentVector]
  | cons k l ih =>
      rw [List.map_cons, List.prod_cons, ih, complete_eq_monomial_index,
        MvPolynomial.monomial_mul_monomial, one_mul]
      rfl

theorem completeIndexExponent_apply (k : ℕ) (p : ℕ+) :
    completeIndexExponent k p = if k = p.val then 1 else 0 := by
  classical
  by_cases hk : 0 < k
  · rw [completeIndexExponent, dite_eq_left hk]
    change (Finsupp.single (⟨k, hk⟩ : ℕ+) (1 : ℕ)) p =
      if k = p.val then 1 else 0
    have hv := Finsupp.single_apply (a := (⟨k, hk⟩ : ℕ+)) (a' := p) (b := (1 : ℕ))
    have he : (⟨k, hk⟩ : ℕ+) = p ↔ k = p.val := by
      constructor
      · intro h
        exact congrArg PNat.val h
      · intro h
        exact Subtype.ext h
    by_cases hkp : k = p.val
    · have hindex := he.mpr hkp
      simpa only [ite_eq_left hindex, ite_eq_left hkp] using hv
    · have hindex : (⟨k, hk⟩ : ℕ+) ≠ p := fun h => hkp (he.mp h)
      simpa only [ite_eq_right hindex, ite_eq_right hkp] using hv
  · have hk0 : k = 0 := by omega
    have hkp : k ≠ p.val := by have := p.pos; omega
    rw [completeIndexExponent, dite_eq_right hk, Finsupp.zero_apply, ite_eq_right hkp]

theorem exponentVector_apply_count (l : List ℕ) (p : ℕ+) :
    exponentVector l p = (l : Multiset ℕ).count p.val := by
  induction l with
  | nil => simp [exponentVector]
  | cons k l ih =>
      change (completeIndexExponent k + exponentVector l) p =
        (k ::ₘ (l : Multiset ℕ)).count p.val
      rw [Finsupp.add_apply, completeIndexExponent_apply, ih, Multiset.count_cons]
      simp only [eq_comm]
      omega

theorem exponentVector_apply (l : List ℕ) (p : ℕ+) :
    exponentVector l p = (positiveIndexMultiset l).count p.val := by
  rw [exponentVector_apply_count]
  exact (Multiset.count_filter_of_pos p.pos).symm

/-- Equality of exponent vectors is precisely equality of their positive-index multisets. -/
theorem exponentVector_eq_iff (l m : List ℕ) :
    exponentVector l = exponentVector m ↔ positiveIndexMultiset l = positiveIndexMultiset m := by
  constructor
  · intro h
    apply Multiset.ext.mpr
    intro k
    by_cases hk : 0 < k
    · let p : ℕ+ := ⟨k, hk⟩
      have he := congrArg (fun f : ℕ+ →₀ ℕ => f p) h
      have hc := (exponentVector_apply_count l p).symm.trans
        (he.trans (exponentVector_apply_count m p))
      change (Multiset.filter (fun a : ℕ => 0 < a) (l : Multiset ℕ)).count k =
        (Multiset.filter (fun a : ℕ => 0 < a) (m : Multiset ℕ)).count k
      rw [Multiset.count_filter_of_pos hk, Multiset.count_filter_of_pos hk]
      exact hc
    · simp [positiveIndexMultiset, hk]
  · intro h
    ext p
    rw [exponentVector_apply, exponentVector_apply, h]

/-- The unit coefficient prevents distinct visible monomials from becoming equal. -/
theorem prod_complete_eq_iff (l m : List ℕ) :
    (l.map (fun k : ℕ => complete (k : ℤ))).prod =
      (m.map (fun k : ℕ => complete (k : ℤ))).prod ↔
      positiveIndexMultiset l = positiveIndexMultiset m := by
  rw [prod_complete_eq_monomial, prod_complete_eq_monomial]
  exact (MvPolynomial.monomial_left_injective (show (1 : ℤ) ≠ 0 by omega)).eq_iff.trans
    (exponentVector_eq_iff l m)

theorem positiveIndexMultiset_of_pos (l : List ℕ) (h : ∀ k ∈ l, 0 < k) :
    positiveIndexMultiset l = (l : Multiset ℕ) := by
  apply Multiset.filter_eq_self.mpr
  intro k hk
  exact h k hk

/-- For positive row lengths, generator products recover the entire length multiset. -/
theorem prod_complete_eq_iff_of_pos (l m : List ℕ)
    (hl : ∀ k ∈ l, 0 < k) (hm : ∀ k ∈ m, 0 < k) :
    (l.map (fun k : ℕ => complete (k : ℤ))).prod =
      (m.map (fun k : ℕ => complete (k : ℤ))).prod ↔
      (l : Multiset ℕ) = (m : Multiset ℕ) := by
  rw [prod_complete_eq_iff, positiveIndexMultiset_of_pos l hl,
    positiveIndexMultiset_of_pos m hm]

/-- The number of positive factors is recovered together with the row lengths. -/
theorem length_eq_of_prod_complete_eq (l m : List ℕ)
    (hl : ∀ k ∈ l, 0 < k) (hm : ∀ k ∈ m, 0 < k)
    (heq : (l.map (fun k : ℕ => complete (k : ℤ))).prod =
      (m.map (fun k : ℕ => complete (k : ℤ))).prod) : l.length = m.length := by
  have h := (prod_complete_eq_iff_of_pos l m hl hm).mp heq
  simpa using congrArg Multiset.card h

/-- Laurent exponents indexed by natural complete indices, with the zero unit omitted. -/
noncomputable def laurentIndexExponent (k : ℕ) : ℕ →₀ ℤ :=
  if k = 0 then 0 else Finsupp.single k 1

theorem laurentIndexExponent_apply (k i : ℕ) :
    laurentIndexExponent k i = if k = 0 then 0 else if k = i then 1 else 0 := by
  classical
  by_cases hk : k = 0
  · simp only [laurentIndexExponent, ite_eq_left hk, Finsupp.zero_apply]
  · simp only [laurentIndexExponent, ite_eq_right hk, Finsupp.single_apply]

/-- The reduced exchange has two numerator indices and a unique negative index. -/
noncomputable def exchangeExponent (u rho z : ℕ) : ℕ →₀ ℤ :=
  laurentIndexExponent u + laurentIndexExponent z - laurentIndexExponent rho

/-- Strictly ordered reduced three-index exchanges are uniquely recognizable, including `z=0`. -/
theorem exchangeExponent_injective
    {u rho z u' rho' z' : ℕ} (hu : rho < u) (hz : z < rho)
    (hu' : rho' < u') (hz' : z' < rho')
    (h : exchangeExponent u rho z = exchangeExponent u' rho' z') :
    rho = rho' ∧ z = z' ∧ u = u' := by
  have hr0 : rho ≠ 0 := by omega
  have hr'0 : rho' ≠ 0 := by omega
  have hu0 : u ≠ 0 := by omega
  have hu'0 : u' ≠ 0 := by omega
  have hrr : rho = rho' := by
    by_contra hne
    have hne' : rho ≠ rho' := hne
    have he := congrArg (fun f : ℕ →₀ ℤ => f rho) h
    simp only [exchangeExponent, Finsupp.add_apply, Finsupp.sub_apply,
      laurentIndexExponent_apply, ite_eq_right hr0, ite_eq_right hr'0,
      ite_eq_right hu0, ite_eq_right hu'0, ite_eq_right (ne_of_gt hu),
      ite_eq_right (ne_of_lt hz), ite_eq_right (Ne.symm hne')] at he
    split_ifs at he <;> omega
  subst rho'
  have huu : u = u' := by
    by_contra hne
    have hne' : u ≠ u' := hne
    have he := congrArg (fun f : ℕ →₀ ℤ => f u) h
    have hzu : z ≠ u := by omega
    have hz'u : z' ≠ u := by omega
    simp only [exchangeExponent, Finsupp.add_apply, Finsupp.sub_apply,
      laurentIndexExponent_apply, ite_eq_right hr0, ite_eq_right hu0,
      ite_eq_right hu'0, ite_eq_right hzu, ite_eq_right hz'u,
      ite_eq_right (ne_of_lt hu), ite_eq_right (Ne.symm hne')] at he
    split_ifs at he <;> omega
  subst u'
  have hzz : laurentIndexExponent z = laurentIndexExponent z' := by
    have hsum : laurentIndexExponent u + laurentIndexExponent z =
        laurentIndexExponent u + laurentIndexExponent z' := by
      have he := congrArg (fun f : ℕ →₀ ℤ => f + laurentIndexExponent rho) h
      simpa only [exchangeExponent, sub_add_cancel] using he
    exact add_left_cancel hsum
  have hzzeq : z = z' := by
    by_cases hz0 : z = 0
    · subst z
      by_contra hne
      have he := congrArg (fun f : ℕ →₀ ℤ => f z') hzz
      have hne' : z' ≠ 0 := fun he => hne he.symm
      simp [laurentIndexExponent_apply, hne'] at he
    · by_contra hne
      have he := congrArg (fun f : ℕ →₀ ℤ => f z) hzz
      have hne' : z ≠ z' := hne
      simp only [laurentIndexExponent_apply, ite_eq_right hz0,
        ite_eq_right (Ne.symm hne')] at he
      split_ifs at he <;> omega
  exact ⟨rfl, hzzeq, rfl⟩

end SkewCofactorIndependence.Base
