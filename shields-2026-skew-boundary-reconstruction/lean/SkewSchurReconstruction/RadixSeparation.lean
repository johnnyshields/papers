/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CappedDiagrams
import SkewSchurReconstruction.GeneratorMonomials
import SkewSchurReconstruction.GeneratorProducts
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Radix separation of cofactor monomials

Formalizes “Weight collisions and coefficient cancellation” (`subsec:weight-scope`),
using the radix weight `eq:radix-weight` and the actual capped matrix `eq:capmatrix`.
The Leibniz expansion supplies the digit bound for every supported monomial of
`eq:cofactor`.  Base-numeral uniqueness then prevents cancellation in the
univariate specialization, with each original coefficient recovered exactly.
Zero and negative complete indices retain their unit and zero conventions.
Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

/-- The natural exponent of the radix specialization of a free-generator monomial. -/
noncomputable def radixExponent (B : ℕ) (e : ℕ+ →₀ ℕ) : ℕ :=
  e.sum fun j a => a * B ^ j.val

/-- Every individual exponent in a product is bounded by its number of factors. -/
theorem exponentVector_apply_le_length (l : List ℕ) (j : ℕ+) :
    exponentVector l j ≤ l.length := by
  rw [exponentVector_apply_count]
  simpa using Multiset.count_le_card j.val (l : Multiset ℕ)

private theorem complete_degreeOf_le_one (k : ℤ) (j : ℕ+) :
    (complete k).degreeOf j ≤ 1 := by
  classical
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [complete_of_neg hk]
  · simp
  · let p : ℕ+ := ⟨k.toNat, by omega⟩
    have hx : complete k = (MvPolynomial.X p : CompleteRing) := complete_of_pos hk
    rw [hx, MvPolynomial.degreeOf_X]
    split_ifs <;> omega

/-- Each Leibniz product contains at most one positive complete generator per row. -/
theorem complete_det_degreeOf_le {n : ℕ} (a : Fin n → Fin n → ℤ) (j : ℕ+) :
    (Matrix.of (fun i k => complete (a i k))).det.degreeOf j ≤ n := by
  classical
  rw [Matrix.det_apply']
  refine (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans ?_
  apply Finset.sup_le
  intro σ _
  refine (MvPolynomial.degreeOf_mul_le j _ _).trans ?_
  have hsign : MvPolynomial.degreeOf j
      (((Equiv.Perm.sign σ : ℤ) : CompleteRing)) = 0 := by
    rw [← map_intCast (MvPolynomial.C : ℤ →+* CompleteRing)]
    exact MvPolynomial.degreeOf_C _ _
  rw [hsign, zero_add]
  refine (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans ?_
  calc
    (∑ i : Fin n, (complete (a (σ i) i)).degreeOf j) ≤ ∑ _i : Fin n, 1 :=
      Finset.sum_le_sum fun i _ => complete_degreeOf_le_one (a (σ i) i) j
    _ = n := by simp

namespace Diagram

/-- The actual signed maximal cofactor has degree at most the row count in each generator. -/
theorem cofactor_degreeOf_le {n : ℕ} (X : Diagram n) (k : Fin (n + 1)) (j : ℕ+) :
    (X.cofactor k).degreeOf j ≤ n := by
  classical
  unfold cofactor signedMaximalCofactor
  refine (MvPolynomial.degreeOf_mul_le j _ _).trans ?_
  have hsign : ((-1 : CompleteRing) ^ k.val).degreeOf j = 0 := by
    have he : (-1 : CompleteRing) ^ k.val = MvPolynomial.C ((-1 : ℤ) ^ k.val) := by
      simp
    rw [he]
    exact MvPolynomial.degreeOf_C _ _
  rw [hsign, zero_add]
  have he : X.capMatrix.submatrix id k.succAbove =
      Matrix.of (fun i r => complete (X.capShift (k.succAbove r) - X.rowParam i)) := by
    ext i r
    rfl
  rw [he]
  exact complete_det_degreeOf_le _ j

/-- Every support exponent is bounded by `n`, without connectedness or a producer premise. -/
theorem cofactor_support_exponent_le {n : ℕ} (X : Diagram n) (k : Fin (n + 1))
    {e : ℕ+ →₀ ℕ} (he : e ∈ (X.cofactor k).support) (j : ℕ+) : e j ≤ n :=
  (MvPolynomial.monomial_le_degreeOf j he).trans (X.cofactor_degreeOf_le k j)

/-- The same digit bound holds for actual defect coordinates. -/
theorem cofactor_sub_support_exponent_le {n : ℕ} (X Y : Diagram n) (k : Fin (n + 1))
    {e : ℕ+ →₀ ℕ} (he : e ∈ (X.cofactor k - Y.cofactor k).support) (j : ℕ+) :
    e j ≤ n := by
  refine (MvPolynomial.monomial_le_degreeOf j he).trans ?_
  exact (MvPolynomial.degreeOf_sub_le j _ _).trans
    (max_le (X.cofactor_degreeOf_le k j) (Y.cofactor_degreeOf_le k j))

end Diagram

private theorem nat_radix_sum_eq_fin (B : ℕ) (e : ℕ →₀ ℕ) (N : ℕ)
    (hs : e.support ⊆ Finset.range N) :
    e.sum (fun j a => a * B ^ j) = ∑ j : Fin N, e j.val * B ^ j.val := by
  classical
  rw [Finsupp.sum_of_support_subset e hs _ (by intro j _; simp)]
  exact Finset.sum_range _

private theorem nat_radix_injective {B : ℕ} (hB : 1 < B)
    {e f : ℕ →₀ ℕ} (he : ∀ j, e j < B) (hf : ∀ j, f j < B)
    (h : e.sum (fun j a => a * B ^ j) = f.sum (fun j a => a * B ^ j)) : e = f := by
  classical
  let N := (e.support ∪ f.support).sup id + 1
  have hs : ∀ g ∈ ({e, f} : Finset (ℕ →₀ ℕ)), g.support ⊆ Finset.range N := by
    intro g hg j hj
    have hgj : j ∈ e.support ∪ f.support := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact Finset.mem_union_left _ hj
      · exact Finset.mem_union_right _ hj
    have hjN := Finset.le_sup (f := id) hgj
    change j ≤ (e.support ∪ f.support).sup id at hjN
    exact Finset.mem_range.mpr (by dsimp [N]; omega)
  have hse := hs e (by simp)
  have hsf := hs f (by simp)
  have hd : List.ofFn (fun j : Fin N => e j.val) =
      List.ofFn (fun j : Fin N => f j.val) := by
    apply Nat.ofDigits_inj_of_len_eq hB (by simp)
    · intro a ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      exact he j.val
    · intro a ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      exact hf j.val
    · rw [nat_radix_sum_eq_fin B e N hse, nat_radix_sum_eq_fin B f N hsf] at h
      simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn,
        List.length_ofFn, Fin.val_cast, List.sum_ofFn] using h
  have hv := congrFun (List.ofFn_inj.mp hd)
  ext j
  by_cases hj : j < N
  · exact hv ⟨j, hj⟩
  · have hje : j ∉ e.support := fun hj' => hj (Finset.mem_range.mp (hse hj'))
    have hjf : j ∉ f.support := fun hj' => hj (Finset.mem_range.mp (hsf hj'))
    simp [Finsupp.notMem_support_iff.mp hje, Finsupp.notMem_support_iff.mp hjf]

private theorem radix_mapDomain_sum (B : ℕ) (e : ℕ+ →₀ ℕ) :
    (e.mapDomain PNat.val).sum (fun j a => a * B ^ j) = radixExponent B e := by
  exact Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ _ _ => by simp [add_mul])

private theorem radix_mapDomain_digit_lt {B : ℕ} (e : ℕ+ →₀ ℕ)
    (hB : 0 < B) (he : ∀ j, e j < B) (k : ℕ) : (e.mapDomain PNat.val) k < B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Finsupp.mapDomain_of_notMem_range e 0]
    · exact hB
    · rintro ⟨j, hj⟩
      have := j.pos
      omega
  · let j : ℕ+ := ⟨k, hk⟩
    have hinj : Function.Injective PNat.val := fun _ _ h => Subtype.ext h
    change (e.mapDomain PNat.val) j.val < B
    rw [Finsupp.mapDomain_apply_of_injective hinj]
    exact he j

/-- Arbitrary-base numeral uniqueness for all finitely supported digit vectors below the base. -/
theorem radixExponent_injective {B : ℕ} (hB : 1 < B) {e f : ℕ+ →₀ ℕ}
    (he : ∀ j, e j < B) (hf : ∀ j, f j < B)
    (h : radixExponent B e = radixExponent B f) : e = f := by
  have hinj : Function.Injective PNat.val := fun _ _ h => Subtype.ext h
  apply Finsupp.mapDomain_injective hinj
  apply nat_radix_injective hB
  · exact radix_mapDomain_digit_lt e (by omega) he
  · exact radix_mapDomain_digit_lt f (by omega) hf
  · simpa only [radix_mapDomain_sum] using h

/-- The real admissible weight is exactly the cast of the natural numeral exponent. -/
theorem radix_weight_eq_cast (B : ℕ) (hB : 3 ≤ B) (e : ℕ+ →₀ ℕ) :
    Finsupp.weight (radixWeight B hB).generatorWeight e = (radixExponent B e : ℝ) := by
  classical
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, radixExponent, ConvexWeight.generatorWeight, radixWeight,
    radixValue, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val ≠ 0 := ne_of_gt j.pos
  simp [hj, nsmul_eq_mul]

/-- Actual substitution `h_j ↦ X^(B^j)` into integral univariate polynomials. -/
noncomputable def radixCollapse (B : ℕ) : CompleteRing →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => Polynomial.X ^ (B ^ j.val))

theorem radixCollapse_complete (B : ℕ) (j : ℕ+) :
    radixCollapse B (complete (j.val : ℤ)) = Polynomial.X ^ (B ^ j.val) := by
  rw [complete_nat]
  exact MvPolynomial.eval₂_X _ _ _

/-- A monomial specializes to one univariate monomial, with its coefficient unchanged. -/
theorem radixCollapse_monomial (B : ℕ) (e : ℕ+ →₀ ℕ) (a : ℤ) :
    radixCollapse B (MvPolynomial.monomial e a) =
      Polynomial.monomial (radixExponent B e) a := by
  classical
  rw [radixCollapse, MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have he : (∑ j ∈ e.support, B ^ j.val * e j) = radixExponent B e := by
    simp only [radixExponent, Finsupp.sum, mul_comm]
  rw [he, Polynomial.C_mul_X_pow_eq_monomial]

private theorem radixCollapse_eq_sum (B : ℕ) (p : CompleteRing) :
    radixCollapse B p = ∑ e ∈ p.support,
      Polynomial.monomial (radixExponent B e) (p.coeff e) := by
  conv_lhs => rw [MvPolynomial.as_sum p, map_sum]
  simp only [radixCollapse_monomial]

/-- Coefficient recovery for an arbitrary polynomial whose support digits are bounded by `n`. -/
theorem radixCollapse_coeff {B n : ℕ} (hB : 1 < B) (hn : n < B) (p : CompleteRing)
    (hp : ∀ e ∈ p.support, ∀ j, e j ≤ n) (e : ℕ+ →₀ ℕ) (he : ∀ j, e j ≤ n) :
    (radixCollapse B p).coeff (radixExponent B e) = p.coeff e := by
  classical
  rw [radixCollapse_eq_sum]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    have hne : radixExponent B f ≠ radixExponent B e := by
      intro h
      apply hfe
      exact radixExponent_injective hB (fun j => lt_of_le_of_lt (hp f hf j) hn)
        (fun j => lt_of_le_of_lt (he j) hn) h
    simp [hne]
  · intro hne
    simp [MvPolynomial.notMem_support_iff.mp hne]

/-- Radix collapse cannot erase a nonzero polynomial in the bounded-digit class. -/
theorem radixCollapse_ne_zero {B n : ℕ} (hB : 1 < B) (hn : n < B)
    (p : CompleteRing) (hp : ∀ e ∈ p.support, ∀ j, e j ≤ n) (hp0 : p ≠ 0) :
    radixCollapse B p ≠ 0 := by
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hp0
  have hc : p.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
  intro hz
  have h := radixCollapse_coeff hB hn p hp e (hp e he)
  rw [hz, Polynomial.coeff_zero] at h
  exact hc h.symm

namespace Diagram

/-- Distinct supported monomials of the actual cofactor never collide at radix weight. -/
theorem cofactor_radixExponent_injective {n B : ℕ} (X : Diagram n) (k : Fin (n + 1))
    (hB : 3 ≤ B) (hn : n < B) : Set.InjOn (radixExponent B) (X.cofactor k).support := by
  intro e he f hf h
  exact radixExponent_injective (by omega)
    (fun j => lt_of_le_of_lt (X.cofactor_support_exponent_le k he j) hn)
    (fun j => lt_of_le_of_lt (X.cofactor_support_exponent_le k hf j) hn) h

/-- The real-weight and natural-exponent versions separate exactly the same monomials. -/
theorem cofactor_radixWeight_injective {n B : ℕ} (X : Diagram n) (k : Fin (n + 1))
    (hB : 3 ≤ B) (hn : n < B) :
    Set.InjOn (fun e : ℕ+ →₀ ℕ => Finsupp.weight (radixWeight B hB).generatorWeight e)
      ((X.cofactor k).support : Set (ℕ+ →₀ ℕ)) := by
  intro e he f hf h
  apply X.cofactor_radixExponent_injective k hB hn he hf
  change Finsupp.weight (radixWeight B hB).generatorWeight e =
    Finsupp.weight (radixWeight B hB).generatorWeight f at h
  rw [radix_weight_eq_cast, radix_weight_eq_cast] at h
  exact_mod_cast h

/-- Every surviving actual cofactor term has its original coefficient after radix collapse. -/
theorem cofactor_radixCollapse_coeff {n B : ℕ} (X : Diagram n) (k : Fin (n + 1))
    (hB : 3 ≤ B) (hn : n < B) {e : ℕ+ →₀ ℕ} (he : e ∈ (X.cofactor k).support) :
    (radixCollapse B (X.cofactor k)).coeff (radixExponent B e) = (X.cofactor k).coeff e :=
  radixCollapse_coeff (by omega) hn (X.cofactor k)
    (fun _ hf j => X.cofactor_support_exponent_le k hf j) e
    (X.cofactor_support_exponent_le k he)

/-- Radix substitution erases an actual cofactor precisely when that cofactor was already zero. -/
theorem cofactor_radixCollapse_eq_zero_iff {n B : ℕ} (X : Diagram n) (k : Fin (n + 1))
    (hB : 3 ≤ B) (hn : n < B) :
    radixCollapse B (X.cofactor k) = 0 ↔ X.cofactor k = 0 := by
  constructor
  · intro h
    by_contra hne
    exact radixCollapse_ne_zero (by omega) hn (X.cofactor k)
      (fun _ he j => X.cofactor_support_exponent_le k he j) hne h
  · intro h
    rw [h, map_zero]

/-- Coefficient preservation applies to actual differences as well as to individual cofactors. -/
theorem cofactor_sub_radixCollapse_coeff {n B : ℕ} (X Y : Diagram n) (k : Fin (n + 1))
    (hB : 3 ≤ B) (hn : n < B) {e : ℕ+ →₀ ℕ}
    (he : e ∈ (X.cofactor k - Y.cofactor k).support) :
    (radixCollapse B (X.cofactor k - Y.cofactor k)).coeff (radixExponent B e) =
      (X.cofactor k - Y.cofactor k).coeff e :=
  radixCollapse_coeff (by omega) hn _
    (fun _ hf j => X.cofactor_sub_support_exponent_le Y k hf j) e
    (X.cofactor_sub_support_exponent_le Y k he)

/-- Radix substitution cannot introduce an equality between actual cofactor coordinates. -/
theorem cofactor_radixCollapse_eq_iff {n B : ℕ} (X Y : Diagram n) (k : Fin (n + 1))
    (hB : 3 ≤ B) (hn : n < B) :
    radixCollapse B (X.cofactor k) = radixCollapse B (Y.cofactor k) ↔
      X.cofactor k = Y.cofactor k := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    by_contra hne
    apply radixCollapse_ne_zero (by omega) hn (X.cofactor k - Y.cofactor k)
      (fun _ he j => X.cofactor_sub_support_exponent_le Y k he j) hne
    rw [map_sub, h, sub_self]
  · intro h
    rw [h]

end Diagram
end SkewSchurReconstruction
