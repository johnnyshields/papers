/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/LowOrder.lean
import SkewRibbonCoarsenings.TriangleIdentity

/-!
# Low-order balance

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:balance` (`lem:low-order`,
`eq:FE`).

"Through three blocks" means: over all partitions `λ` of `n` into at most three positive parts
(`LowPartition`).  `NoLowDiscrepancy` says that no such `λ` has an ordinary coefficient
discrepancy `Δm(λ) = m_β(λ) - m_γ(λ)` of magnitude one or two, and `EqThroughThree` says that
`Δm(λ) = 0` for all of them.  The proof follows the paper: a nonzero two-block difference has
magnitude at most two; for a labeled triple the three-block difference of `eq:three-difference` is
at most two in absolute value, so by `lem:labels` a nonzero value gives a discrepancy of magnitude
one or two; and `eq:three-difference` with `a₃ = -a₁ - a₂` is `eq:FE`.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-- A partition of `n` into at most three positive parts, as a multiset. -/
def LowPartition (n : ℕ) (lam : Multiset ℕ) : Prop :=
  (∀ p ∈ lam, 0 < p) ∧ lam.sum = n ∧ lam.card ≤ 3

/-- No ordinary coefficient discrepancy of magnitude one or two through three blocks. -/
def NoLowDiscrepancy (n : ℕ) (S S' : Finset ℕ) : Prop :=
  ∀ lam : Multiset ℕ, LowPartition n lam →
    ((mult n S lam : ℤ) - mult n S' lam) ∉ ({-2, -1, 1, 2} : Set ℤ)

/-- Equality of the ordinary coefficients through three blocks. -/
def EqThroughThree (n : ℕ) (S S' : Finset ℕ) : Prop :=
  ∀ lam : Multiset ℕ, LowPartition n lam → mult n S lam = mult n S' lam

section Prelim

variable {n : ℕ} {S S' : Finset ℕ}

theorem mult_single (hS : IsCutSet n S) : mult n S {n} = 1 := by
  have hS' : S ⊆ Finset.Ioo 0 n := hS
  unfold mult
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
  constructor
  · rintro ⟨hTS, hg⟩
    have hc := card_gaps (hTS.trans hS')
    rw [hg] at hc
    have : T.card = 0 := by simpa using hc.symm
    exact Finset.card_eq_zero.mp this
  · rintro rfl
    refine ⟨Finset.empty_subset _, ?_⟩
    unfold gaps
    simp

theorem mult_two_le (hS : IsCutSet n S) {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = n) :
    mult n S {p, q} ≤ 2 := by
  rw [mult_two hS hp hq hpq]
  split_ifs <;> omega

theorem tern_bound : ∀ u1 ∈ ({-1, 0, 1} : Finset ℤ), ∀ v1 ∈ ({-1, 0, 1} : Finset ℤ),
    ∀ u2 ∈ ({-1, 0, 1} : Finset ℤ), ∀ v2 ∈ ({-1, 0, 1} : Finset ℤ),
    ∀ u3 ∈ ({-1, 0, 1} : Finset ℤ), ∀ v3 ∈ ({-1, 0, 1} : Finset ℤ),
    u1 * v1 = 0 → u2 * v2 = 0 → u3 * v3 = 0 →
    |u1 * v2 + v1 * u2 + (u1 * v3 + v1 * u3) + (u2 * v3 + v2 * u3)| ≤ 2 := by
  decide

/-- For three positions with disjoint ternary pairs `(u_i, v_i)`, the cross sum of
`eq:three-difference` has absolute value at most two. -/
theorem triangleSum_abs_le {u v : ZMod n → ℤ} (hu : ∀ x, u x ∈ ({-1, 0, 1} : Set ℤ))
    (hv : ∀ x, v x ∈ ({-1, 0, 1} : Set ℤ)) (huv : ∀ x, u x * v x = 0) (x y z : ZMod n) :
    |triangleSum u v x y z| ≤ 2 := by
  have f : ∀ w : ℤ, w ∈ ({-1, 0, 1} : Set ℤ) → w ∈ ({-1, 0, 1} : Finset ℤ) := by
    intro w hw; simpa using hw
  exact tern_bound _ (f _ (hu x)) _ (f _ (hv x)) _ (f _ (hu y)) _ (f _ (hv y)) _ (f _ (hu z)) _
    (f _ (hv z)) (huv x) (huv y) (huv z)


theorem lowPartition_sortParts {r : ℕ} (hr : r ≤ 3) {a : Fin r → ℕ} (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = n) : LowPartition n (sortParts a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hp
    exact ha i
  · unfold sortParts
    rw [← hsum]; rfl
  · simp [sortParts, hr]

theorem sortParts_triple (x y z : ℕ) : sortParts ![x, y, z] = {x, y, z} := by
  simp [sortParts, Fin.univ_val_map]
  rfl

theorem sortParts_pair (x y : ℕ) : sortParts ![x, y] = {x, y} := by
  simp [sortParts, Fin.univ_val_map]
  rfl

/-- A cast `ℕ → ℤ/n` of a list of three positive integers summing to `n` is a triangle:
`c = -(a + b)` in `ℤ/n`. -/
theorem cast_third {a b c : ℕ} (h : a + b + c = n) :
    ((c : ℕ) : ZMod n) = -((a : ZMod n) + (b : ZMod n)) := by
  have : ((a + b + c : ℕ) : ZMod n) = 0 := by rw [h]; exact ZMod.natCast_self n
  push_cast at this
  linear_combination this

theorem triangleSum_neg_sum {u v : ZMod n → ℤ} (hu : IsOdd u) (hv : IsOdd v) (x y : ZMod n) :
    triangleSum u v x y (-(x + y)) =
      (u x * v y + v x * u y) - (u (x + y) * (v x + v y) + v (x + y) * (u x + u y)) := by
  unfold triangleSum
  rw [hu, hv]
  ring

theorem fe_iff_triangle {u v : ZMod n → ℤ} (hu : IsOdd u) (hv : IsOdd v) :
    FEq u v ↔ ∀ x y, triangleSum u v x y (-(x + y)) = 0 := by
  unfold FEq
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [triangleSum_neg_sum hu hv]
  constructor <;> intro h <;> linarith

end Prelim

section Main

variable {n : ℕ} {S S' : Finset ℕ}

/-- Under no low discrepancy, the triangle sum vanishes on every positive triple summing to `n`.
This is the step "a nonzero value supplies the stated ordinary certificate" of the proof of
`lem:low-order`. -/
theorem triangle_zero_of_noLow (hn : 0 < n) (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (hno : NoLowDiscrepancy n S S') (htau : ∀ x : ZMod n, tauFun n S x = tauFun n S' x)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = n) :
    triangleSum (uFun n S S') (vFun n S S') (a : ZMod n) (b : ZMod n) (c : ZMod n) = 0 := by
  have hlist : ∀ i, 0 < (![a, b, c] : Fin 3 → ℕ) i := by
    intro i; fin_cases i <;> simpa
  have hsum : ∑ i, (![a, b, c] : Fin 3 → ℕ) i = n := by
    rw [Fin.sum_univ_three]; simpa using habc
  have h3 := three_difference hS hS' htau hlist hsum
  have hlab : ∀ i, lab n ![a, b, c] i = ((![a, b, c] : Fin 3 → ℕ) i : ZMod n) := fun i => rfl
  rw [hlab 0, hlab 1, hlab 2] at h3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h3
  by_contra hne
  have hD0 : (K S ![a, b, c] : ℤ) - K S' ![a, b, c] ≠ 0 := by
    rw [h3]; exact neg_ne_zero.mpr hne
  have hD2 : |(K S ![a, b, c] : ℤ) - K S' ![a, b, c]| ≤ 2 := by
    rw [h3, abs_neg]
    exact triangleSum_abs_le (fun x => uFun_ternary S S' x) (fun x => vFun_ternary S S' x)
      (uFun_mul_vFun (fun x => htau x)) _ _ _
  obtain ⟨hm, _⟩ := labeled_diff_small hn hS hS' ![a, b, c] hlist hsum hD0 hD2
  exact hno _ (lowPartition_sortParts (le_refl 3) hlist hsum) hm

theorem triangleSum_neg {u v : ZMod n → ℤ} (hu : IsOdd u) (hv : IsOdd v) (x y z : ZMod n) :
    triangleSum u v (-x) (-y) (-z) = triangleSum u v x y z := by
  unfold triangleSum
  rw [hu, hu, hu, hv, hv, hv]
  ring

theorem odd_zero {f : ZMod n → ℤ} (hf : IsOdd f) : f 0 = 0 := by
  have := hf 0
  rw [neg_zero] at this
  omega

theorem triangleSum_degenerate {u v : ZMod n → ℤ} (hu : IsOdd u) (hv : IsOdd v)
    (huv : ∀ x, u x * v x = 0) (y : ZMod n) :
    triangleSum u v 0 y (-(0 + y)) = 0 := by
  unfold triangleSum
  rw [zero_add, odd_zero hu, odd_zero hv, hu, hv]
  have := huv y
  linear_combination (-2 : ℤ) * this

/-- `eq:FE` from the vanishing of the triangle sum on positive triples. -/
theorem fe_of_triangle_zero {u v : ZMod n → ℤ} (hu : IsOdd u) (hv : IsOdd v)
    (huv : ∀ x, u x * v x = 0) (hn : 0 < n)
    (h : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b + c = n →
      triangleSum u v (a : ZMod n) (b : ZMod n) (c : ZMod n) = 0) : FEq u v := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [fe_iff_triangle hu hv]
  -- symmetric reduction: the statement for `x, y` with `x.val + y.val ≤ n`
  have key : ∀ x y : ZMod n, x.val + y.val ≤ n → triangleSum u v x y (-(x + y)) = 0 := by
    intro x y hxy
    by_cases hx : x.val = 0
    · have : x = 0 := (ZMod.val_eq_zero x).mp hx
      subst this; exact triangleSum_degenerate hu hv huv y
    by_cases hy : y.val = 0
    · have : y = 0 := (ZMod.val_eq_zero y).mp hy
      subst this
      -- `triangleSum x 0 (-x)` equals the degenerate sum after permuting arguments
      unfold triangleSum
      rw [add_zero, odd_zero hu, odd_zero hv, hu, hv]
      have := huv x
      linear_combination (-2 : ℤ) * this
    by_cases hxy' : x.val + y.val = n
    · have hsum : x + y = 0 := by
        have : ((x.val + y.val : ℕ) : ZMod n) = 0 := by rw [hxy']; exact ZMod.natCast_self n
        push_cast at this
        rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
      rw [hsum, neg_zero]
      unfold triangleSum
      have hyx : y = -x := by linear_combination hsum
      rw [hyx, odd_zero hu, odd_zero hv, hu, hv]
      have := huv x
      linear_combination (-2 : ℤ) * this
    · have hc := h x.val y.val (n - x.val - y.val) (by omega) (by omega) (by omega) (by omega)
      have hcast := cast_third (n := n) (a := x.val) (b := y.val) (c := n - x.val - y.val) (by omega)
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hcast] at hc
      exact hc
  intro x y
  by_cases hxy : x.val + y.val ≤ n
  · exact key x y hxy
  · have hx : x ≠ 0 := fun h => by simp [h] at hxy; have := ZMod.val_lt y; omega
    have hy : y ≠ 0 := fun h => by simp [h] at hxy; have := ZMod.val_lt x; omega
    have : NeZero x := ⟨hx⟩
    have : NeZero y := ⟨hy⟩
    have h1 : (-x).val = n - x.val := ZMod.val_neg_of_ne_zero x
    have h2 : (-y).val = n - y.val := ZMod.val_neg_of_ne_zero y
    have k := key (-x) (-y) (by omega)
    have e : -(-x + -y) = x + y := by ring
    rw [e] at k
    have t := triangleSum_neg hu hv x y (-(x + y))
    rw [neg_neg] at t
    rw [← t]; exact k

/-- `lem:low-order`, `eq:uv` part: if there is no ordinary coefficient discrepancy of magnitude one
or two through three blocks, the two-block data agree. -/
theorem twoBlockEq_of_noLow (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (hno : NoLowDiscrepancy n S S') : TwoBlockEq n S S' := by
  intro p q hp hq hpq
  by_contra hne
  apply hno {p, q} ⟨?_, ?_, ?_⟩
  · have h1 := mult_two_le hS hp hq hpq
    have h2 := mult_two_le hS' hp hq hpq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · intro r hr; simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hr
    omega
  · simpa using hpq
  · simp

/-- `lem:low-order` (forward direction, with `eq:FE`): if there is no ordinary coefficient
discrepancy of magnitude one or two through three blocks, then the two-block data agree
(`TwoBlockEq`, which gives `eq:uv`: `τ_b = τ_c` and `u, v` odd, ternary, disjointly supported) and
`eq:FE` holds on `ℤ/n`.  "Through three blocks" is `LowPartition`: all partitions of `n` into at
most three positive parts, the blocks used in the proof (two-block coefficients for `eq:uv`, and
labeled triples for `eq:three-difference`). -/
theorem low_order (hn : 0 < n) (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (hno : NoLowDiscrepancy n S S') :
    TwoBlockEq n S S' ∧ FEq (uFun n S S') (vFun n S S') := by
  have h2 := twoBlockEq_of_noLow hS hS' hno
  have htau := tau_eq_of_twoBlockEq hn hS hS' h2
  refine ⟨h2, ?_⟩
  have htau' : ∀ x : ZMod n, cutInd n S x + cutInd n S (-x) =
      cutInd n S' x + cutInd n S' (-x) := htau
  refine fe_of_triangle_zero (uFun_odd htau') (vFun_odd htau') (uFun_mul_vFun htau') hn ?_
  intro a b c ha hb hc habc
  exact triangle_zero_of_noLow hn hS hS' hno htau ha hb hc habc

/-- `lem:low-order` (converse, first half): after two-block equality, `eq:FE` gives equality of
the ordinary coefficients through three blocks. -/
theorem eqThroughThree_of_fe (hn : 0 < n) (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (h2 : TwoBlockEq n S S') (hfe : FEq (uFun n S S') (vFun n S S')) :
    EqThroughThree n S S' := by
  have htau := tau_eq_of_twoBlockEq hn hS hS' h2
  have htau' : ∀ x : ZMod n, cutInd n S x + cutInd n S (-x) =
      cutInd n S' x + cutInd n S' (-x) := htau
  intro lam ⟨hpos, hsum, hcard⟩
  have hcases : lam.card = 0 ∨ lam.card = 1 ∨ lam.card = 2 ∨ lam.card = 3 := by omega
  rcases hcases with h0 | h1 | h2c | h3
  · rw [Multiset.card_eq_zero] at h0
    subst h0
    simp at hsum; omega
  · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp h1
    simp only [Multiset.sum_singleton] at hsum
    subst hsum
    rw [mult_single hS, mult_single hS']
  · obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp h2c
    have hx := hpos x (by simp)
    have hy := hpos y (by simp)
    exact h2 x y hx hy (by simpa using hsum)
  · obtain ⟨x, y, z, rfl⟩ := Multiset.card_eq_three.mp h3
    have hx := hpos x (by simp)
    have hy := hpos y (by simp)
    have hz := hpos z (by simp)
    have hsum' : x + y + z = n := by simp [add_assoc] at hsum; omega
    have hlist : ∀ i, 0 < (![x, y, z] : Fin 3 → ℕ) i := by
      intro i; fin_cases i <;> simpa
    have hsum3 : ∑ i, (![x, y, z] : Fin 3 → ℕ) i = n := by
      rw [Fin.sum_univ_three]; simpa using hsum'
    have h3d := three_difference hS hS' htau' hlist hsum3
    have hlab : ∀ i, lab n ![x, y, z] i = ((![x, y, z] : Fin 3 → ℕ) i : ZMod n) := fun i => rfl
    rw [hlab 0, hlab 1, hlab 2] at h3d
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h3d
    have htri : triangleSum (uFun n S S') (vFun n S S') (x : ZMod n) (y : ZMod n) (z : ZMod n)
        = 0 := by
      have hcz := cast_third (n := n) (a := x) (b := y) (c := z) hsum'
      rw [hcz]
      exact (fe_iff_triangle (uFun_odd htau') (vFun_odd htau')).mp hfe _ _
    rw [htri, neg_zero] at h3d
    have hd := labeled_diff_eq hn hS hS' ![x, y, z] hlist hsum3
    rw [h3d, sortParts_triple] at hd
    have hk := kappa_pos ({x, y, z} : Multiset ℕ)
    have : ((mult n S {x, y, z} : ℤ) - mult n S' {x, y, z}) = 0 := by
      have hk' : (0 : ℤ) < kappa {x, y, z} := by exact_mod_cast hk
      rcases mul_eq_zero.mp hd.symm with h | h
      · omega
      · exact h
    omega

/-- `lem:low-order` (converse): after two-block equality, equality of the ordinary coefficients
through three blocks is equivalent to `eq:FE`. -/
theorem eqThroughThree_iff_fe (hn : 0 < n) (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (h2 : TwoBlockEq n S S') :
    EqThroughThree n S S' ↔ FEq (uFun n S S') (vFun n S S') := by
  refine ⟨fun h => ?_, eqThroughThree_of_fe hn hS hS' h2⟩
  have hno : NoLowDiscrepancy n S S' := by
    intro lam hl hm
    have := h lam hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    omega
  exact (low_order hn hS hS' hno).2

end Main

end SkewRibbonCoarsenings
