/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FourRowHessenberg
import SkewJacobiNegative.StaircaseFiveFamilies

/-!
# Five-row constant-gap classes

The four-minimum branch of `lem:staircase-thick-classification` in
`shields-2026-skew-jacobi-negative.tex`.  Independent homogenized generators
permit faithful minimum subtraction.  All interval coarsenings are retained,
including their multiplicities and coincident numerical labels.
-/

namespace SkewJacobiNegative.ConstantGapFiveClassification

open Gluing StaircaseFiveFamilies FourRowHessenberg
open scoped BigOperators

/-- A product indexed by an actual finite word. -/
noncomputable def wordProduct {k : ℕ} (v : Fin k → ℤ) : CompleteRing :=
  ∏ i, complete (v i)

/-- The exponent of a positive word's generator monomial. -/
noncomputable def wordExponent {k : ℕ} (v : Fin k → ℤ) : ℕ+ →₀ ℕ :=
  ∑ i, hExp (v i).toNat

/-- Positive words contain no unit factor. -/
theorem wordProduct_monomial {k : ℕ} (v : Fin k → ℤ)
    (hv : ∀ i, 0 < v i) :
    wordProduct v = MvPolynomial.monomial (wordExponent v) 1 := by
  simp only [wordProduct, complete_eq_hh]
  rw [Gluing.prod_hh_eq, if_pos (fun i => (hv i).le)]
  rfl

/-- Equality of positive monomial sums recovers the full multiset, not just support. -/
theorem monomial_sum_multiset {n : ℕ} (T U : Fin n → (ℕ+ →₀ ℕ))
    (he : (∑ i, (MvPolynomial.monomial (T i) 1 : CompleteRing)) =
      ∑ i, MvPolynomial.monomial (U i) 1) :
    Finset.univ.val.map T = Finset.univ.val.map U := by
  classical
  apply Multiset.ext.mpr
  intro m
  have hh := congrArg (fun p : CompleteRing => p.coeff m) he
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hh
  have hc (V : Fin n → (ℕ+ →₀ ℕ)) :
      (Finset.univ.val.map V).count m =
        ∑ i : Fin n, if V i = m then (1 : ℕ) else 0 := by
    rw [Multiset.count_map, Finset.sum_boole]
    change (Finset.univ.val.filter (fun i => m = V i)).card =
      (Finset.univ.filter (fun i => V i = m)).card
    simp only [← Finset.filter_val]
    congr 1
    ext i
    simp [eq_comm]
  rw [hc T, hc U]
  exact_mod_cast hh

theorem sum_wordProduct_monomial {n k : ℕ} (T : Fin n → Fin k → ℤ)
    (hT : ∀ i j, 0 < T i j) :
    (∑ i, wordProduct (T i)) =
      ∑ i, (MvPolynomial.monomial (wordExponent (T i)) 1 : CompleteRing) := by
  apply Finset.sum_congr rfl
  intro i _
  exact wordProduct_monomial (T i) (hT i)

/-- A complete coarsening inventory is read with numerical multiplicities. -/
theorem sum_word_reading {n k : ℕ} (T U : Fin n → Fin k → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (he : (∑ i, wordProduct (T i)) = ∑ i, wordProduct (U i)) :
    Finset.univ.val.map (fun i => wordExponent (T i)) =
      Finset.univ.val.map (fun i => wordExponent (U i)) := by
  apply monomial_sum_multiset
  rw [← sum_wordProduct_monomial T hT, ← sum_wordProduct_monomial U hU]
  exact he

/-- Every interval coarsening with four parts: all four placements are present. -/
def fourCoarsenings (a b c d e : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![a+b,c,d,e], ![a,b+c,d,e], ![a,b,c+d,e], ![a,b,c,d+e]]

/-- Every three-part interval coarsening, including the disjoint-merge placements. -/
def threeCoarsenings (a b c d e : ℤ) : Fin 6 → Fin 3 → ℤ :=
  ![![a+b+c,d,e], ![a+b,c+d,e], ![a+b,c,d+e],
    ![a,b+c+d,e], ![a,b+c,d+e], ![a,b,c+d+e]]

/-- All four two-part coarsenings, with no endpoint placement discarded. -/
def twoCoarsenings (a b c d e : ℤ) : Fin 4 → Fin 2 → ℤ :=
  ![![a+b+c+d,e], ![a+b+c,d+e], ![a+b,c+d+e], ![a,b+c+d+e]]

/-- The five singleton parts and all coarser interval partitions. -/
noncomputable def ribbon (a b c d e : ℤ) : CompleteRing :=
  interval complete a b c d e 0 0 0 0

/-- Ordinary homogeneous degree of a positive word counts its parts. -/
theorem wordProduct_homogeneous {k : ℕ} (v : Fin k → ℤ) (hv : ∀ i, 0 < v i) :
    (wordProduct v).IsHomogeneous k := by
  have hh (i : Fin k) : (complete (v i)).IsHomogeneous 1 := by
    rw [complete_of_pos (hv i)]
    exact MvPolynomial.isHomogeneous_X _ _
  simpa only [wordProduct, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] using
    MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => complete (v i))
      (fun _ => 1) (fun i _ => hh i)

/-- A projection preserves precisely the coarsenings of its own length. -/
theorem project_word (m : ℕ) {k : ℕ} (v : Fin k → ℤ) (hv : ∀ i, 0 < v i) :
    MvPolynomial.homogeneousComponent m (wordProduct v) =
      if m = k then wordProduct v else 0 :=
  MvPolynomial.homogeneousComponent_of_mem (wordProduct_homogeneous v hv)

/-- Expansion grouped by the number of interval parts, retaining every coefficient. -/
theorem ribbon_coarsening_expansion (a b c d e : ℤ) :
    ribbon a b c d e = wordProduct ![a,b,c,d,e]
      - (∑ i, wordProduct (fourCoarsenings a b c d e i))
      + (∑ i, wordProduct (threeCoarsenings a b c d e i))
      - (∑ i, wordProduct (twoCoarsenings a b c d e i))
      + complete (a+b+c+d+e) := by
  simp [ribbon, interval, wordProduct, fourCoarsenings, threeCoarsenings,
    twoCoarsenings, Fin.sum_univ_succ, Fin.prod_univ_succ, complete_zero]
  ring

/-- The actual polynomial yields all homogeneous readings simultaneously. -/
theorem ribbon_polynomial_readings (a b c d e A B C D E : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hs : ribbon a b c d e = ribbon A B C D E) :
    wordProduct ![a,b,c,d,e] = wordProduct ![A,B,C,D,E] ∧
    (∑ i, wordProduct (fourCoarsenings a b c d e i)) =
      (∑ i, wordProduct (fourCoarsenings A B C D E i)) ∧
    (∑ i, wordProduct (threeCoarsenings a b c d e i)) =
      (∑ i, wordProduct (threeCoarsenings A B C D E i)) ∧
    (∑ i, wordProduct (twoCoarsenings a b c d e i)) =
      (∑ i, wordProduct (twoCoarsenings A B C D E i)) := by
  have hp : ∀ j : Fin 5, 0 < ![a,b,c,d,e] j := by
    intro j; fin_cases j <;> simp <;> omega
  have hq : ∀ j : Fin 5, 0 < ![A,B,C,D,E] j := by
    intro j; fin_cases j <;> simp <;> omega
  have hp4 : ∀ i j, 0 < fourCoarsenings a b c d e i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [fourCoarsenings] <;> omega
  have hq4 : ∀ i j, 0 < fourCoarsenings A B C D E i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [fourCoarsenings] <;> omega
  have hp3 : ∀ i j, 0 < threeCoarsenings a b c d e i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [threeCoarsenings] <;> omega
  have hq3 : ∀ i j, 0 < threeCoarsenings A B C D E i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [threeCoarsenings] <;> omega
  have hp2 : ∀ i j, 0 < twoCoarsenings a b c d e i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [twoCoarsenings] <;> omega
  have hq2 : ∀ i j, 0 < twoCoarsenings A B C D E i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [twoCoarsenings] <;> omega
  have hsum : 0 < a+b+c+d+e := by omega
  have hSUM : 0 < A+B+C+D+E := by omega
  rw [ribbon_coarsening_expansion, ribbon_coarsening_expansion] at hs
  have h5 := congrArg (MvPolynomial.homogeneousComponent (σ := ℕ+) (R := ℚ) 5) hs
  have h4 := congrArg (MvPolynomial.homogeneousComponent (σ := ℕ+) (R := ℚ) 4) hs
  have h3 := congrArg (MvPolynomial.homogeneousComponent (σ := ℕ+) (R := ℚ) 3) hs
  have h2 := congrArg (MvPolynomial.homogeneousComponent (σ := ℕ+) (R := ℚ) 2) hs
  have hlast (m : ℕ) (x : ℤ) (hx : 0 < x) :
      MvPolynomial.homogeneousComponent m (complete x) =
        if m = 1 then complete x else 0 := by
    rw [complete_of_pos hx]
    exact MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_X _ _)
  simp only [map_sub, map_add, map_sum, project_word _ _ hp, project_word _ _ hq,
    project_word _ _ (hp4 _), project_word _ _ (hq4 _),
    project_word _ _ (hp3 _), project_word _ _ (hq3 _),
    project_word _ _ (hp2 _), project_word _ _ (hq2 _),
    hlast _ _ hsum, hlast _ _ hSUM] at h5 h4 h3 h2
  norm_num at h5 h4 h3 h2
  exact ⟨h5,h4,h3,h2⟩

/-- The full four-placement inventory, with numerical collisions counted exactly. -/
theorem ribbon_quartet_reading (a b c d e A B C D E : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hs : ribbon a b c d e = ribbon A B C D E) :
    Finset.univ.val.map (fun i => wordExponent (fourCoarsenings a b c d e i)) =
      Finset.univ.val.map (fun i => wordExponent (fourCoarsenings A B C D E i)) := by
  apply sum_word_reading
  · intro i j; fin_cases i <;> fin_cases j <;> simp [fourCoarsenings] <;> omega
  · intro i j; fin_cases i <;> fin_cases j <;> simp [fourCoarsenings] <;> omega
  · exact (ribbon_polynomial_readings a b c d e A B C D E
      ha hb hc hd he hA hB hC hD hE hs).2.1


/-- All structural permutations of the five singleton generators. -/
def fiveMatch (a b c d e A B C D E : ℤ) : Prop :=
  (a = A ∧ fourMatch b c d e B C D E) ∨
  (a = B ∧ fourMatch b c d e A C D E) ∨
  (a = C ∧ fourMatch b c d e A B D E) ∨
  (a = D ∧ fourMatch b c d e A B C E) ∨
  (a = E ∧ fourMatch b c d e A B C D)

/-- Five positive factors recover every row position permutation, uniformly in the parts. -/
theorem five_product_reading {a b c d e A B C D E : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hs : wordProduct ![a,b,c,d,e] = wordProduct ![A,B,C,D,E]) :
    fiveMatch a b c d e A B C D E := by
  have hp : complete a * complete b * complete c * complete d * complete e =
      complete A * complete B * complete C * complete D * complete E := by
    simpa [wordProduct, Fin.prod_univ_succ, mul_assoc] using hs
  have hi : Base.complete a * Base.complete b * Base.complete c *
      Base.complete d * Base.complete e =
      Base.complete A * Base.complete B * Base.complete C *
      Base.complete D * Base.complete E := by
    apply integerLift_injective
    simpa only [map_mul, complete] using hp
  have hcast : ∀ x : ℤ, 0 < x → (x.toNat : ℤ) = x := fun x hx => by omega
  have hm : (([a.toNat,b.toNat,c.toNat,d.toNat,e.toNat] : List ℕ) : Multiset ℕ) =
      (([A.toNat,B.toNat,C.toNat,D.toNat,E.toNat] : List ℕ) : Multiset ℕ) := by
    apply (Base.prod_complete_eq_iff_of_pos _ _ (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega)).mp
    simpa [hcast a ha, hcast b hb, hcast c hc, hcast d hd, hcast e he,
      hcast A hA, hcast B hB, hcast C hC, hcast D hD, hcast E hE, mul_assoc] using hi
  have hmem : a.toNat = A.toNat ∨ a.toNat = B.toNat ∨ a.toNat = C.toNat ∨
      a.toNat = D.toNat ∨ a.toNat = E.toNat := by
    have hh : a.toNat ∈
        (([a.toNat,b.toNat,c.toNat,d.toNat,e.toNat] : List ℕ) : Multiset ℕ) := by simp
    rw [hm] at hh
    simpa using hh
  have hcancel {w x y z : ℤ} (hw : 0 < w) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
      (hh : complete a * complete b * complete c * complete d * complete e =
        complete a * complete w * complete x * complete y * complete z) :
      fourMatch b c d e w x y z := by
    apply four_product_reading hb hc hd he hw hx hy hz
    apply mul_left_cancel₀ ((complete_ne_zero_iff a).mpr ha.le)
    simpa only [mul_assoc] using hh
  rcases hmem with h₁ | h₁ | h₁ | h₁ | h₁
  · have h₁ : a = A := by omega
    subst A
    exact Or.inl ⟨rfl, hcancel hB hC hD hE hp⟩
  · have h₁ : a = B := by omega
    subst B
    exact Or.inr (Or.inl ⟨rfl, hcancel hA hC hD hE
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hp)⟩)
  · have h₁ : a = C := by omega
    subst C
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hcancel hA hB hD hE
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hp)⟩))
  · have h₁ : a = D := by omega
    subst D
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hcancel hA hB hC hE
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hp)⟩)))
  · have h₁ : a = E := by omega
    subst E
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hcancel hA hB hC hD
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hp)⟩)))

/-- Three factors are read by the already constructed three-monomial inventory theorem. -/
theorem triple_word_reading (v w : Fin 3 → ℤ)
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (he : wordProduct v = wordProduct w) :
    tripleMatch (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) := by
  have h : threeMatches (fun _ : Fin 3 => v) (fun _ : Fin 3 => w) := by
    apply three_sum_reading
    · exact fun _ i => hv i
    · exact fun _ i => hw i
    · have hp : complete (v 0) * complete (v 1) * complete (v 2) =
          complete (w 0) * complete (w 1) * complete (w 2) := by
        simpa [wordProduct, Fin.prod_univ_succ, mul_assoc] using he
      change (complete (v 0) * complete (v 1) * complete (v 2)) +
          (complete (v 0) * complete (v 1) * complete (v 2)) +
          (complete (v 0) * complete (v 1) * complete (v 2)) =
        (complete (w 0) * complete (w 1) * complete (w 2)) +
          (complete (w 0) * complete (w 1) * complete (w 2)) +
          (complete (w 0) * complete (w 1) * complete (w 2))
      rw [hp]
  simpa only [threeMatches, or_self, and_self] using h

/-- A four-part product retains all structural positional permutations. -/
theorem four_word_reading (v w : Fin 4 → ℤ)
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (he : wordProduct v = wordProduct w) :
    fourMatch (v 0) (v 1) (v 2) (v 3) (w 0) (w 1) (w 2) (w 3) := by
  apply four_product_reading (hv 0) (hv 1) (hv 2) (hv 3)
    (hw 0) (hw 1) (hw 2) (hw 3)
  simpa [wordProduct, Fin.prod_univ_succ, mul_assoc] using he

/-- A two-part product is read without assuming different parts. -/
theorem two_word_reading (v w : Fin 2 → ℤ)
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (he : wordProduct v = wordProduct w) :
    (v 0 = w 0 ∧ v 1 = w 1) ∨ (v 0 = w 1 ∧ v 1 = w 0) := by
  apply complete_two_product_reading (hv 0) (hv 1) (hw 0) (hw 1)
  simpa [wordProduct, Fin.prod_univ_succ] using he

/-- The six bijective matches of a three-entry inventory. -/
def tripleRelations (R : Fin 3 → Fin 3 → Prop) : Prop :=
  (R 0 0 ∧ R 1 1 ∧ R 2 2) ∨ (R 0 0 ∧ R 1 2 ∧ R 2 1) ∨
  (R 0 1 ∧ R 1 0 ∧ R 2 2) ∨ (R 0 1 ∧ R 1 2 ∧ R 2 0) ∨
  (R 0 2 ∧ R 1 0 ∧ R 2 1) ∨ (R 0 2 ∧ R 1 1 ∧ R 2 0)

/-- All twenty-four bijective matches of the four actual seam placements. -/
def quartetRelations (R : Fin 4 → Fin 4 → Prop) : Prop :=
  (R 0 0 ∧ tripleRelations (fun i j => R i.succ j.succ)) ∨
  (R 0 1 ∧ tripleRelations (fun i j => R i.succ (![0,2,3] j))) ∨
  (R 0 2 ∧ tripleRelations (fun i j => R i.succ (![0,1,3] j))) ∨
  (R 0 3 ∧ tripleRelations (fun i j => R i.succ j.castSucc))

private theorem two_monomial_matching (a b A B : ℕ+ →₀ ℕ)
    (h : (MvPolynomial.monomial a 1 : CompleteRing) + MvPolynomial.monomial b 1 =
      MvPolynomial.monomial A 1 + MvPolynomial.monomial B 1) :
    (a = A ∧ b = B) ∨ (a = B ∧ b = A) := by
  classical
  have hinj := MvPolynomial.monomial_left_injective (σ := ℕ+)
    (show (1 : ℚ) ≠ 0 by norm_num)
  by_cases ha : a = A
  · subst A
    exact Or.inl ⟨rfl, hinj (add_left_cancel h)⟩
  · have hb : a = B := by
      by_contra hb
      have hh := congrArg (fun p : CompleteRing => p.coeff a) h
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial] at hh
      simp only [ite_true, ite_eq_right (Ne.symm ha), ite_eq_right (Ne.symm hb)] at hh
      split_ifs at hh <;> norm_num at hh
    subst B
    refine Or.inr ⟨rfl, hinj ?_⟩
    linear_combination h

private theorem three_monomial_matching (T U : Fin 3 → (ℕ+ →₀ ℕ))
    (h : (MvPolynomial.monomial (T 0) 1 : CompleteRing) +
        MvPolynomial.monomial (T 1) 1 + MvPolynomial.monomial (T 2) 1 =
      MvPolynomial.monomial (U 0) 1 + MvPolynomial.monomial (U 1) 1 +
        MvPolynomial.monomial (U 2) 1) :
    tripleRelations (fun i j => T i = U j) := by
  classical
  have h0 : T 0 = U 0 ∨ T 0 = U 1 ∨ T 0 = U 2 := by
    by_contra hn
    push_neg at hn
    have hh := congrArg (fun p : CompleteRing => p.coeff (T 0)) h
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial] at hh
    simp only [ite_true, ite_eq_right (Ne.symm hn.1),
      ite_eq_right (Ne.symm hn.2.1), ite_eq_right (Ne.symm hn.2.2)] at hh
    split_ifs at hh <;> norm_num at hh
  rcases h0 with h0 | h0 | h0
  · have hr : (MvPolynomial.monomial (T 1) 1 : CompleteRing) +
        MvPolynomial.monomial (T 2) 1 =
      MvPolynomial.monomial (U 1) 1 + MvPolynomial.monomial (U 2) 1 := by
      rw [h0] at h
      linear_combination h
    have hm := two_monomial_matching _ _ _ _ hr
    unfold tripleRelations
    rcases hm with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨h0,h1,h2⟩
    · exact Or.inr (Or.inl ⟨h0,h1,h2⟩)
  · have hr : (MvPolynomial.monomial (T 1) 1 : CompleteRing) +
        MvPolynomial.monomial (T 2) 1 =
      MvPolynomial.monomial (U 0) 1 + MvPolynomial.monomial (U 2) 1 := by
      rw [h0] at h
      linear_combination h
    have hm := two_monomial_matching _ _ _ _ hr
    unfold tripleRelations
    rcases hm with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h0,h1,h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h0,h1,h2⟩)))
  · have hr : (MvPolynomial.monomial (T 1) 1 : CompleteRing) +
        MvPolynomial.monomial (T 2) 1 =
      MvPolynomial.monomial (U 0) 1 + MvPolynomial.monomial (U 1) 1 := by
      rw [h0] at h
      linear_combination h
    have hm := two_monomial_matching _ _ _ _ hr
    unfold tripleRelations
    rcases hm with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0,h1,h2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0,h1,h2⟩))))

private theorem four_monomial_matching (T U : Fin 4 → (ℕ+ →₀ ℕ))
    (h : (∑ i, (MvPolynomial.monomial (T i) 1 : CompleteRing)) =
      ∑ i, MvPolynomial.monomial (U i) 1) :
    quartetRelations (fun i j => T i = U j) := by
  have hm := monomial_sum_multiset T U h
  have hi : T 0 ∈ Finset.univ.val.map T := by
    exact Multiset.mem_map.mpr ⟨0,by simp,rfl⟩
  rw [hm] at hi
  obtain ⟨j,_,hj⟩ := Multiset.mem_map.mp hi
  have h0 := hj.symm
  simp [Fin.sum_univ_succ] at h
  fin_cases j
  · left
    refine ⟨h0, ?_⟩
    apply three_monomial_matching
    change T 0 = U 0 at h0
    change (MvPolynomial.monomial (T 1) 1 : CompleteRing) +
      MvPolynomial.monomial (T 2) 1 + MvPolynomial.monomial (T 3) 1 =
      MvPolynomial.monomial (U 1) 1 + MvPolynomial.monomial (U 2) 1 +
      MvPolynomial.monomial (U 3) 1
    rw [h0] at h
    linear_combination h
  · right; left
    refine ⟨h0, ?_⟩
    apply three_monomial_matching
    change T 0 = U 1 at h0
    change (MvPolynomial.monomial (T 1) 1 : CompleteRing) +
      MvPolynomial.monomial (T 2) 1 + MvPolynomial.monomial (T 3) 1 =
      MvPolynomial.monomial (U 0) 1 + MvPolynomial.monomial (U 2) 1 +
      MvPolynomial.monomial (U 3) 1
    rw [h0] at h
    linear_combination h
  · right; right; left
    refine ⟨h0, ?_⟩
    apply three_monomial_matching
    change T 0 = U 2 at h0
    change (MvPolynomial.monomial (T 1) 1 : CompleteRing) +
      MvPolynomial.monomial (T 2) 1 + MvPolynomial.monomial (T 3) 1 =
      MvPolynomial.monomial (U 0) 1 + MvPolynomial.monomial (U 1) 1 +
      MvPolynomial.monomial (U 3) 1
    rw [h0] at h
    linear_combination h
  · right; right; right
    refine ⟨h0, ?_⟩
    apply three_monomial_matching
    change T 0 = U 3 at h0
    change (MvPolynomial.monomial (T 1) 1 : CompleteRing) +
      MvPolynomial.monomial (T 2) 1 + MvPolynomial.monomial (T 3) 1 =
      MvPolynomial.monomial (U 0) 1 + MvPolynomial.monomial (U 1) 1 +
      MvPolynomial.monomial (U 2) 1
    rw [h0] at h
    linear_combination h

private theorem quartetRelations_mono (R S : Fin 4 → Fin 4 → Prop)
    (h : ∀ i j, R i j → S i j) (hR : quartetRelations R) : quartetRelations S := by
  unfold quartetRelations tripleRelations at *
  aesop

/-- Bijective quartet matching before expanding permutations of the factors. -/
theorem four_inventory_word_reading {k : ℕ} (T U : Fin 4 → Fin k → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (he : (∑ i, wordProduct (T i)) = ∑ i, wordProduct (U i)) :
    quartetRelations (fun i j => wordProduct (T i) = wordProduct (U j)) := by
  have hh : (∑ i, (MvPolynomial.monomial (wordExponent (T i)) 1 : CompleteRing)) =
      ∑ i, MvPolynomial.monomial (wordExponent (U i)) 1 := by
    rw [← sum_wordProduct_monomial T hT, ← sum_wordProduct_monomial U hU]
    exact he
  apply quartetRelations_mono _ _ _ (four_monomial_matching _ _ hh)
  intro i j hij
  rw [wordProduct_monomial _ (hT i), wordProduct_monomial _ (hU j), hij]

/-- Exact bijective matching of the four coarsenings, including repeated monomials. -/
theorem four_inventory_reading (T U : Fin 4 → Fin 4 → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (he : (∑ i, wordProduct (T i)) = ∑ i, wordProduct (U i)) :
    quartetRelations (fun i j =>
      fourMatch (T i 0) (T i 1) (T i 2) (T i 3)
        (U j 0) (U j 1) (U j 2) (U j 3)) := by
  apply quartetRelations_mono _ _ _ (four_inventory_word_reading T U hT hU he)
  intro i j hij
  exact four_word_reading _ _ (hT i) (hU j) hij

/-- The two rows incident to each of the four actual seams. -/
def adjacentRows (a b c d e : ℤ) : Fin 4 → Fin 2 → ℤ :=
  ![![a,b], ![b,c], ![c,d], ![d,e]]

/-- A merge monomial and its two removed factors recover the complete row
product.  This identity uses the actual placement of the merge. -/
theorem merge_product_identity (a b c d e : ℤ) (i : Fin 4) :
    wordProduct ![a,b,c,d,e] *
        complete (adjacentRows a b c d e i 0 + adjacentRows a b c d e i 1) =
      wordProduct (fourCoarsenings a b c d e i) *
        complete (adjacentRows a b c d e i 0) *
        complete (adjacentRows a b c d e i 1) := by
  fin_cases i <;>
    simp [wordProduct, adjacentRows, fourCoarsenings, Fin.prod_univ_succ] <;> ring

/-- A positive sum is larger than both summands.  Consequently this
three-factor equality reads the two summands, not six unrelated positions. -/
theorem merged_pair_reading (p q P Q : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hP : 0 < P) (hQ : 0 < Q)
    (he : complete p * complete q * complete (P+Q) =
      complete P * complete Q * complete (p+q)) :
    (p = P ∧ q = Q) ∨ (p = Q ∧ q = P) := by
  have ht := triple_word_reading ![p,q,P+Q] ![P,Q,p+q]
    (by intro k; fin_cases k <;> simp <;> omega)
    (by intro k; fin_cases k <;> simp <;> omega)
    (by simpa [wordProduct, Fin.prod_univ_succ, mul_assoc] using he)
  simp only [tripleMatch, Matrix.cons_val] at ht
  omega

/-- Full row-product equality converts a matched coarsening into its actual
unordered incident pair.  Cancellation is justified by positive generators. -/
theorem coarsening_edge_reading (a b c d e A B C D E : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hrow : wordProduct ![a,b,c,d,e] = wordProduct ![A,B,C,D,E])
    (i j : Fin 4)
    (hcoarse : wordProduct (fourCoarsenings a b c d e i) =
      wordProduct (fourCoarsenings A B C D E j)) :
    (adjacentRows a b c d e i 0 = adjacentRows A B C D E j 0 ∧
     adjacentRows a b c d e i 1 = adjacentRows A B C D E j 1) ∨
    (adjacentRows a b c d e i 0 = adjacentRows A B C D E j 1 ∧
     adjacentRows a b c d e i 1 = adjacentRows A B C D E j 0) := by
  let p := adjacentRows a b c d e i 0
  let q := adjacentRows a b c d e i 1
  let P := adjacentRows A B C D E j 0
  let Q := adjacentRows A B C D E j 1
  let W := wordProduct ![a,b,c,d,e]
  let K := wordProduct (fourCoarsenings a b c d e i)
  have hK : K ≠ 0 := by
    unfold K wordProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    apply (complete_ne_zero_iff _).mpr
    fin_cases i <;> fin_cases k <;> simp [fourCoarsenings] <;> omega
  have hpq : ∀ k, 0 < adjacentRows a b c d e i k := by
    intro k; fin_cases i <;> fin_cases k <;> simp [adjacentRows] <;> omega
  have hPQ : ∀ k, 0 < adjacentRows A B C D E j k := by
    intro k; fin_cases j <;> fin_cases k <;> simp [adjacentRows] <;> omega
  have hl : W * complete (p+q) = K * complete p * complete q :=
    merge_product_identity a b c d e i
  have hr : W * complete (P+Q) = K * complete P * complete Q := by
    change wordProduct ![a,b,c,d,e] * complete (P+Q) =
      wordProduct (fourCoarsenings a b c d e i) * complete P * complete Q
    rw [hrow,hcoarse]
    exact merge_product_identity A B C D E j
  have hcross :
      K * (complete p * complete q * complete (P+Q)) =
        K * (complete P * complete Q * complete (p+q)) := by
    calc
      K * (complete p * complete q * complete (P+Q)) =
          (K * complete p * complete q) * complete (P+Q) := by ring
      _ = (W * complete (p+q)) * complete (P+Q) := by rw [hl]
      _ = (W * complete (P+Q)) * complete (p+q) := by ring
      _ = (K * complete P * complete Q) * complete (p+q) := by rw [hr]
      _ = K * (complete P * complete Q * complete (p+q)) := by ring
  exact merged_pair_reading p q P Q (hpq 0) (hpq 1) (hPQ 0) (hPQ 1)
    (mul_left_cancel₀ hK hcross)

/-- Nonrotation alternatives written as literal five-part words.  The two
orientations of the inner factor give the entire four-element class. -/
def ribbonExceptional (a b c d e A B C D E : ℤ) : Prop :=
  (c = a ∧ e = b ∧ d = a+b ∧
    ((A = a ∧ B = a+b ∧ C = b ∧ D = a ∧ E = b) ∨
     (A = b ∧ B = a ∧ C = b ∧ D = a+b ∧ E = a))) ∨
  (d = a ∧ e = c ∧ b = a+c ∧
    ((A = a ∧ B = c ∧ C = a ∧ D = a+c ∧ E = c) ∨
     (A = c ∧ B = a+c ∧ C = a ∧ D = c ∧ E = a)))

/-- The five-part conclusion in scalar coordinates. -/
def ribbonClass (a b c d e A B C D E : ℤ) : Prop :=
  (a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E) ∨
  (a = E ∧ b = D ∧ c = C ∧ d = B ∧ e = A) ∨
  ribbonExceptional a b c d e A B C D E

/-- The actual four incident-pair inventory, with both orientations retained. -/
def edgeReading (a b c d e A B C D E : ℤ) : Prop :=
  quartetRelations (fun i j =>
    (adjacentRows a b c d e i 0 = adjacentRows A B C D E j 0 ∧
     adjacentRows a b c d e i 1 = adjacentRows A B C D E j 1) ∨
    (adjacentRows a b c d e i 0 = adjacentRows A B C D E j 1 ∧
     adjacentRows a b c d e i 1 = adjacentRows A B C D E j 0))

/-- A bijective quartet preserves sums without choosing any orientations. -/
theorem quartetRelations_sum {G : Type*} [AddCommMonoid G] (T U : Fin 4 → G)
    (h : quartetRelations (fun i j => T i = U j)) :
    T 0 + T 1 + T 2 + T 3 = U 0 + U 1 + U 2 + U 3 := by
  unfold quartetRelations tripleRelations at h
  rcases h with ⟨h0,ht⟩ | ⟨h0,ht⟩ | ⟨h0,ht⟩ | ⟨h0,ht⟩
  all_goals rcases ht with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ |
    ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
  all_goals dsimp at h0 h1 h2 h3
  all_goals rw [h0,h1,h2,h3]
  all_goals abel

/-- An unordered pair retains both orientations, including repeated labels. -/
def pairMatches (a b A B : ℤ) : Prop := (a = A ∧ b = B) ∨ (a = B ∧ b = A)

/-- Exact matching of two coefficient-one pair monomials. -/
def doubleMatches (T U : Fin 2 → Fin 2 → ℤ) : Prop :=
  (pairMatches (T 0 0) (T 0 1) (U 0 0) (U 0 1) ∧
   pairMatches (T 1 0) (T 1 1) (U 1 0) (U 1 1)) ∨
  (pairMatches (T 0 0) (T 0 1) (U 1 0) (U 1 1) ∧
   pairMatches (T 1 0) (T 1 1) (U 0 0) (U 0 1))

theorem double_product_reading (T U : Fin 2 → Fin 2 → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (he : wordProduct (T 0) + wordProduct (T 1) =
      wordProduct (U 0) + wordProduct (U 1)) : doubleMatches T U := by
  have hm := two_monomial_matching (wordExponent (T 0)) (wordExponent (T 1))
    (wordExponent (U 0)) (wordExponent (U 1)) (by
      rw [← wordProduct_monomial _ (hT 0), ← wordProduct_monomial _ (hT 1),
        ← wordProduct_monomial _ (hU 0), ← wordProduct_monomial _ (hU 1)]
      exact he)
  have hR (i j : Fin 2) (hij : wordExponent (T i) = wordExponent (U j)) :
      pairMatches (T i 0) (T i 1) (U j 0) (U j 1) := by
    apply two_word_reading _ _ (hT i) (hU j)
    rw [wordProduct_monomial _ (hT i), wordProduct_monomial _ (hU j), hij]
  rcases hm with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact Or.inl ⟨hR 0 0 h0,hR 1 1 h1⟩
  · exact Or.inr ⟨hR 0 1 h0,hR 1 0 h1⟩

private theorem tripleRelations_mono (R S : Fin 3 → Fin 3 → Prop)
    (h : ∀ i j, R i j → S i j) (hR : tripleRelations R) : tripleRelations S := by
  unfold tripleRelations at *
  aesop

theorem triple_product_sum_reading (T U : Fin 3 → Fin 2 → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (he : wordProduct (T 0) + wordProduct (T 1) + wordProduct (T 2) =
      wordProduct (U 0) + wordProduct (U 1) + wordProduct (U 2)) :
    tripleRelations (fun i j => pairMatches (T i 0) (T i 1) (U j 0) (U j 1)) := by
  have hm := three_monomial_matching (fun i => wordExponent (T i))
    (fun i => wordExponent (U i)) (by
      rw [← wordProduct_monomial _ (hT 0), ← wordProduct_monomial _ (hT 1),
        ← wordProduct_monomial _ (hT 2), ← wordProduct_monomial _ (hU 0),
        ← wordProduct_monomial _ (hU 1), ← wordProduct_monomial _ (hU 2)]
      exact he)
  apply tripleRelations_mono _ _ _ hm
  intro i j hij
  apply two_word_reading _ _ (hT i) (hU j)
  rw [wordProduct_monomial _ (hT i), wordProduct_monomial _ (hU j), hij]

private theorem triple_match_sum (f : ℤ → ℤ) {a b c A B C : ℤ}
    (h : tripleMatch a b c A B C) : f a + f b + f c = f A + f B + f C := by
  unfold tripleMatch at h
  rcases h with ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ |
    ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ <;> rw [h0,h1,h2] <;> ring

private theorem four_match_sum (f : ℤ → ℤ) {a b c d A B C D : ℤ}
    (h : fourMatch a b c d A B C D) :
    f a + f b + f c + f d = f A + f B + f C + f D := by
  unfold fourMatch at h
  rcases h with ⟨h0,ht⟩ | ⟨h0,ht⟩ | ⟨h0,ht⟩ | ⟨h0,ht⟩
  all_goals have hs := triple_match_sum f ht
  all_goals rw [h0]
  all_goals linear_combination hs

theorem five_match_sum (f : ℤ → ℤ) {a b c d e A B C D E : ℤ}
    (h : fiveMatch a b c d e A B C D E) :
    f a + f b + f c + f d + f e = f A + f B + f C + f D + f E := by
  unfold fiveMatch at h
  rcases h with ⟨h0,ht⟩ | ⟨h0,ht⟩ | ⟨h0,ht⟩ | ⟨h0,ht⟩ | ⟨h0,ht⟩
  all_goals have hs := four_match_sum f ht
  all_goals rw [h0]
  all_goals linear_combination hs

/-- Incidence counts each interior row twice and each endpoint once. -/
theorem edge_incidence_moment (f : ℤ → ℤ) {a b c d e A B C D E : ℤ}
    (h : edgeReading a b c d e A B C D E) :
    (f a+f b)+(f b+f c)+(f c+f d)+(f d+f e) =
      (f A+f B)+(f B+f C)+(f C+f D)+(f D+f E) := by
  have hq : quartetRelations (fun i j =>
      f (adjacentRows a b c d e i 0) + f (adjacentRows a b c d e i 1) =
      f (adjacentRows A B C D E j 0) + f (adjacentRows A B C D E j 1)) := by
    apply quartetRelations_mono _ _ _ h
    intro i j hij
    rcases hij with ⟨h0,h1⟩ | ⟨h0,h1⟩
    all_goals rw [h0,h1]
    all_goals ring
  have hs := quartetRelations_sum
    (fun i => f (adjacentRows a b c d e i 0) + f (adjacentRows a b c d e i 1))
    (fun i => f (adjacentRows A B C D E i 0) + f (adjacentRows A B C D E i 1)) hq
  simpa only [adjacentRows, Matrix.cons_val] using hs

/-- Row and edge inventories recover the unordered endpoint pair, with no
distinctness assumptions and no search through row permutations. -/
theorem endpoint_reading {a b c d e A B C D E : ℤ}
    (hr : fiveMatch a b c d e A B C D E)
    (he : edgeReading a b c d e A B C D E) : pairMatches a e A E := by
  have hrow := five_match_sum (fun x => x) hr
  have hedge := edge_incidence_moment (fun x => x) he
  have hs : a+e = A+E := by linear_combination 2*hrow-hedge
  have hrow2 := five_match_sum (fun x => x^2) hr
  have hedge2 := edge_incidence_moment (fun x => x^2) he
  have hq : a^2+e^2 = A^2+E^2 := by linear_combination 2*hrow2-hedge2
  have he' : e = A+E-a := by omega
  rw [he'] at hq
  have hf : (a-A)*(a-E) = 0 := by nlinarith [hq]
  rcases mul_eq_zero.mp hf with h | h
  · left; constructor <;> omega
  · right; constructor <;> omega

/-- Sum of the four unordered adjacent-pair monomials. -/
noncomputable def edgePolynomial (a b c d e : ℤ) : CompleteRing :=
  complete a*complete b + complete b*complete c +
    complete c*complete d + complete d*complete e

theorem edge_polynomial_of_reading {a b c d e A B C D E : ℤ}
    (h : edgeReading a b c d e A B C D E) :
    edgePolynomial a b c d e = edgePolynomial A B C D E := by
  have hq : quartetRelations (fun i j =>
      complete (adjacentRows a b c d e i 0) * complete (adjacentRows a b c d e i 1) =
      complete (adjacentRows A B C D E j 0) * complete (adjacentRows A B C D E j 1)) := by
    apply quartetRelations_mono _ _ _ h
    intro i j hij
    rcases hij with ⟨h0,h1⟩ | ⟨h0,h1⟩
    all_goals rw [h0,h1]
    all_goals ring
  have hs := quartetRelations_sum
    (fun i => complete (adjacentRows a b c d e i 0) *
      complete (adjacentRows a b c d e i 1))
    (fun i => complete (adjacentRows A B C D E i 0) *
      complete (adjacentRows A B C D E i 1)) hq
  simpa only [edgePolynomial, adjacentRows, Matrix.cons_val] using hs

/-- Only the two middle cuts remain after common endpoints are canceled. -/
noncomputable def middleCuts (a b c d e : ℤ) : CompleteRing :=
  complete (a+b+c)*complete (d+e) + complete (a+b)*complete (c+d+e)

theorem middle_cut_sum {a b c d e B C D : ℤ}
    (hTotal : b+c+d = B+C+D)
    (he : (∑ i, wordProduct (twoCoarsenings a b c d e i)) =
      ∑ i, wordProduct (twoCoarsenings a B C D e i)) :
    middleCuts a b c d e = middleCuts a B C D e := by
  have h0 : a+b+c+d = a+B+C+D := by omega
  have h1 : b+c+d+e = B+C+D+e := by omega
  simp [twoCoarsenings, wordProduct, Fin.sum_univ_succ, Fin.prod_univ_succ] at he
  rw [h0,h1] at he
  unfold middleCuts
  linear_combination he

/-- A two-edge switch has only the two ordinary shared-vertex mechanisms. -/
theorem edge_switch {A B C D : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (he : complete A*complete C + complete B*complete D =
      complete A*complete B + complete C*complete D) : B = C ∨ A = D := by
  have hm := double_product_reading ![![A,C],![B,D]] ![![A,B],![C,D]]
    (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> omega)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> omega)
    (by simpa [wordProduct, Fin.prod_univ_succ] using he)
  simp only [doubleMatches, pairMatches, Matrix.cons_val] at hm
  omega

theorem ribbonClass_symm {a b c d e A B C D E : ℤ}
    (h : ribbonClass a b c d e A B C D E) : ribbonClass A B C D E a b c d e := by
  unfold ribbonClass at h
  rcases h with ⟨h0,h1,h2,h3,h4⟩ | ⟨h0,h1,h2,h3,h4⟩ | h
  · left
    exact ⟨by omega,by omega,by omega,by omega,by omega⟩
  · right; left
    exact ⟨by omega,by omega,by omega,by omega,by omega⟩
  · unfold ribbonExceptional at h
    rcases h with ⟨hc,he,hd,hq⟩ | ⟨hd,he,hb,hq⟩
    · rcases hq with ⟨q0,q1,q2,q3,q4⟩ | ⟨q0,q1,q2,q3,q4⟩
      · right; right; right
        exact ⟨by omega,by omega,by omega,
          Or.inl ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
      · right; right; left
        exact ⟨by omega,by omega,by omega,
          Or.inr ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
    · rcases hq with ⟨q0,q1,q2,q3,q4⟩ | ⟨q0,q1,q2,q3,q4⟩
      · right; right; left
        exact ⟨by omega,by omega,by omega,
          Or.inl ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
      · right; right; right
        exact ⟨by omega,by omega,by omega,
          Or.inr ⟨by omega,by omega,by omega,by omega,by omega⟩⟩

theorem ribbonClass_reverse_right {a b c d e A B C D E : ℤ}
    (h : ribbonClass a b c d e E D C B A) : ribbonClass a b c d e A B C D E := by
  unfold ribbonClass at h
  rcases h with ⟨h0,h1,h2,h3,h4⟩ | ⟨h0,h1,h2,h3,h4⟩ | h
  · right; left
    exact ⟨by omega,by omega,by omega,by omega,by omega⟩
  · left
    exact ⟨by omega,by omega,by omega,by omega,by omega⟩
  · unfold ribbonExceptional at h
    rcases h with ⟨hc,he,hd,hq⟩ | ⟨hd,he,hb,hq⟩
    · rcases hq with ⟨q0,q1,q2,q3,q4⟩ | ⟨q0,q1,q2,q3,q4⟩
      · right; right; left
        exact ⟨hc,he,hd,Or.inr ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
      · right; right; left
        exact ⟨hc,he,hd,Or.inl ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
    · rcases hq with ⟨q0,q1,q2,q3,q4⟩ | ⟨q0,q1,q2,q3,q4⟩
      · right; right; right
        exact ⟨hd,he,hb,Or.inr ⟨by omega,by omega,by omega,by omega,by omega⟩⟩
      · right; right; right
        exact ⟨hd,he,hb,Or.inl ⟨by omega,by omega,by omega,by omega,by omega⟩⟩

private theorem aligned_swap_front (A B C D E : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hg : edgePolynomial A C B D E = edgePolynomial A B C D E)
    (hk : middleCuts A C B D E = middleCuts A B C D E) :
    ribbonClass A C B D E A B C D E := by
  have hs := edge_switch hA hB hC hD (by
    unfold edgePolynomial at hg
    linear_combination hg)
  have hi : A+C+B = A+B+C := by omega
  unfold middleCuts at hk
  rw [hi] at hk
  have hp := add_left_cancel hk
  have hm := two_word_reading ![A+C,B+D+E] ![A+B,C+D+E]
    (by intro i; fin_cases i <;> simp <;> omega)
    (by intro i; fin_cases i <;> simp <;> omega)
    (by simpa [wordProduct, Fin.prod_univ_succ] using hp)
  simp only [Matrix.cons_val] at hm
  clear hg hk hp
  have hBC : B=C := by
    rcases hs with hs | hs
    · exact hs
    · rcases hm with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> omega
  exact Or.inl ⟨rfl,hBC.symm,hBC,rfl,rfl⟩

private theorem aligned_swap_back (A B C D E : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hg : edgePolynomial A B D C E = edgePolynomial A B C D E)
    (hk : middleCuts A B D C E = middleCuts A B C D E) :
    ribbonClass A B D C E A B C D E := by
  have hs := edge_switch hB hC hD hE (by
    unfold edgePolynomial at hg
    linear_combination hg)
  have hi : D+C+E = C+D+E := by omega
  unfold middleCuts at hk
  rw [hi] at hk
  have hp := add_right_cancel hk
  have hm := two_word_reading ![A+B+D,C+E] ![A+B+C,D+E]
    (by intro i; fin_cases i <;> simp <;> omega)
    (by intro i; fin_cases i <;> simp <;> omega)
    (by simpa [wordProduct, Fin.prod_univ_succ] using hp)
  simp only [Matrix.cons_val] at hm
  clear hg hk hp
  have hCD : C=D := by
    rcases hs with hs | hs
    · exact hs
    · rcases hm with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> omega
  exact Or.inl ⟨rfl,rfl,hCD.symm,hCD,rfl⟩

private theorem aligned_reverse_middle (A B C D E : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hg : edgePolynomial A D C B E = edgePolynomial A B C D E) :
    ribbonClass A D C B E A B C D E := by
  have hs := edge_switch hA hB hD hE (by
    unfold edgePolynomial at hg
    linear_combination hg)
  clear hg
  rcases hs with hBD | hAE
  · exact Or.inl ⟨rfl,hBD.symm,rfl,hBD,rfl⟩
  · exact Or.inr (Or.inl ⟨hAE,rfl,rfl,rfl,hAE.symm⟩)

/-- The six literal mechanisms of the three-edge residual in a middle cycle. -/
def cycleGraph (A B C D E : ℤ) : Prop :=
  (B=C ∧ B=D) ∨ (A=B ∧ B=D) ∨ (B=C ∧ B=E) ∨
  (A=B ∧ B=E) ∨ (A=D ∧ C=E) ∨ (A=E ∧ C=D)

theorem cycle_graph_mechanisms (A B C D E : ℤ)
    (h : tripleRelations (fun i j =>
      pairMatches (![![A,C],![B,D],![B,E]] i 0) (![![A,C],![B,D],![B,E]] i 1)
        (![![A,B],![B,C],![D,E]] j 0) (![![A,B],![B,C],![D,E]] j 1))) :
    cycleGraph A B C D E := by
  simp only [tripleRelations, Matrix.cons_val] at h
  rcases h with ⟨g0,g1,g2⟩ | ⟨g0,g1,g2⟩ | ⟨g0,g1,g2⟩ |
    ⟨g0,g1,g2⟩ | ⟨g0,g1,g2⟩ | ⟨g0,g1,g2⟩
  all_goals unfold pairMatches at g0 g1 g2
  all_goals rcases g0 with ⟨_,_⟩ | ⟨_,_⟩
  all_goals rcases g1 with ⟨_,_⟩ | ⟨_,_⟩
  all_goals rcases g2 with ⟨_,_⟩ | ⟨_,_⟩
  all_goals unfold cycleGraph
  all_goals omega

private theorem cycle_cut_classification (A B C D E : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hg : cycleGraph A B C D E)
    (hk : doubleMatches ![![A+C+D,B+E],![A+C,D+B+E]]
      ![![A+B+C,D+E],![A+B,C+D+E]]) :
    ribbonClass A C D B E A B C D E := by
  unfold cycleGraph at hg
  simp only [doubleMatches,pairMatches,Matrix.cons_val] at hk
  rcases hg with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ |
    ⟨h0,h1⟩ | ⟨h0,h1⟩
  · left
    exact ⟨rfl,by omega,by omega,by omega,rfl⟩
  · have hBC : B=C := by omega
    left
    exact ⟨rfl,hBC.symm,by omega,by omega,rfl⟩
  · have hBD : B=D := by omega
    left
    exact ⟨rfl,by omega,by omega,hBD,rfl⟩
  · have hCD : C=D := by omega
    right; left
    exact ⟨by omega,hCD,hCD.symm,rfl,by omega⟩
  · have hs : B=A+C ∨ A=C := by omega
    rcases hs with hs | hs
    · right; right; left
      exact ⟨by omega,by omega,hs,
        Or.inl ⟨rfl,hs,rfl,by omega,by omega⟩⟩
    · right; left
      exact ⟨by omega,by omega,by omega,rfl,by omega⟩
  · right; left
    exact ⟨h0,h1,h1.symm,rfl,h0.symm⟩

private theorem aligned_cycle (A B C D E : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hg : edgePolynomial A C D B E = edgePolynomial A B C D E)
    (hk : middleCuts A C D B E = middleCuts A B C D E) :
    ribbonClass A C D B E A B C D E := by
  have hp : complete A*complete C + complete B*complete D + complete B*complete E =
      complete A*complete B + complete B*complete C + complete D*complete E := by
    unfold edgePolynomial at hg
    linear_combination hg
  have hm := triple_product_sum_reading ![![A,C],![B,D],![B,E]]
    ![![A,B],![B,C],![D,E]]
    (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> omega)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> omega)
    (by simpa [wordProduct, Fin.prod_univ_succ] using hp)
  have hgraph := cycle_graph_mechanisms A B C D E hm
  have hcuts := double_product_reading ![![A+C+D,B+E],![A+C,D+B+E]]
    ![![A+B+C,D+E],![A+B,C+D+E]]
    (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> omega)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> omega)
    (by simpa [wordProduct, middleCuts, Fin.prod_univ_succ] using hk)
  exact cycle_cut_classification A B C D E hA hB hC hD hE hgraph hcuts

/-- All needed inventories are produced from actual ribbon equality. -/
theorem ribbon_invariants (a b c d e A B C D E : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hs : ribbon a b c d e = ribbon A B C D E) :
    fiveMatch a b c d e A B C D E ∧ edgeReading a b c d e A B C D E ∧
    wordProduct ![a,b,c,d,e] = wordProduct ![A,B,C,D,E] ∧
    (∑ i, wordProduct (twoCoarsenings a b c d e i)) =
      (∑ i, wordProduct (twoCoarsenings A B C D E i)) := by
  obtain ⟨hr,h4,_,h2⟩ := ribbon_polynomial_readings a b c d e A B C D E
    ha hb hc hd he hA hB hC hD hE hs
  have hrow := five_product_reading ha hb hc hd he hA hB hC hD hE hr
  have hp4 : ∀ i j, 0 < fourCoarsenings a b c d e i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [fourCoarsenings] <;> omega
  have hq4 : ∀ i j, 0 < fourCoarsenings A B C D E i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [fourCoarsenings] <;> omega
  have hq := four_inventory_word_reading _ _ hp4 hq4 h4
  have hedge : edgeReading a b c d e A B C D E :=
    quartetRelations_mono _ _ (fun i j hij =>
      coarsening_edge_reading a b c d e A B C D E ha hb hc hd he
        hA hB hC hD hE hr i j hij) hq
  exact ⟨hrow,hedge,hr,h2⟩

theorem aligned_ribbon_classification (a b c d e A B C D E : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hs : ribbon a b c d e = ribbon A B C D E) (h0 : a=A) (h4 : e=E) :
    ribbonClass a b c d e A B C D E := by
  subst a
  subst e
  obtain ⟨_,hedges,hr,hcuts⟩ := ribbon_invariants A b c d E A B C D E
    ha hb hc hd he hA hB hC hD hE hs
  have hp : complete A*(complete b*complete c*complete d)*complete E =
      complete A*(complete B*complete C*complete D)*complete E := by
    simpa [wordProduct, Fin.prod_univ_succ, mul_assoc] using hr
  have hmidprod := mul_left_cancel₀ ((complete_ne_zero_iff A).mpr hA.le)
    (mul_right_cancel₀ ((complete_ne_zero_iff E).mpr hE.le) hp)
  have hmid := triple_word_reading ![b,c,d] ![B,C,D]
    (by intro i; fin_cases i <;> simp <;> omega)
    (by intro i; fin_cases i <;> simp <;> omega)
    (by simpa [wordProduct, Fin.prod_univ_succ, mul_assoc] using hmidprod)
  have hTotal : b+c+d = B+C+D := triple_match_sum (fun x => x) hmid
  have hk := middle_cut_sum hTotal hcuts
  have hg := edge_polynomial_of_reading hedges
  clear hr hp hmidprod hedges hcuts hs
  simp only [tripleMatch, Matrix.cons_val] at hmid
  rcases hmid with ⟨_,_,_⟩ | ⟨_,_,_⟩ | ⟨_,_,_⟩ |
    ⟨_,_,_⟩ | ⟨_,_,_⟩ | ⟨_,_,_⟩
  all_goals subst_vars
  · exact Or.inl ⟨rfl,rfl,rfl,rfl,rfl⟩
  · apply aligned_swap_back <;> assumption
  · apply aligned_swap_front <;> assumption
  · apply aligned_cycle <;> assumption
  · apply ribbonClass_symm
    exact aligned_cycle A D B C E hA hD hB hC hE hg.symm hk.symm
  · apply aligned_reverse_middle <;> assumption

theorem ribbon_reverse (a b c d e : ℤ) : ribbon e d c b a = ribbon a b c d e := by
  simp only [ribbon, interval, sub_zero, complete_zero, mul_one]
  simp only [
    show complete (e+d) = complete (d+e) from congrArg complete (by omega),
    show complete (d+c) = complete (c+d) from congrArg complete (by omega),
    show complete (c+b) = complete (b+c) from congrArg complete (by omega),
    show complete (b+a) = complete (a+b) from congrArg complete (by omega),
    show complete (e+d+c) = complete (c+d+e) from congrArg complete (by omega),
    show complete (d+c+b) = complete (b+c+d) from congrArg complete (by omega),
    show complete (c+b+a) = complete (a+b+c) from congrArg complete (by omega),
    show complete (e+d+c+b) = complete (b+c+d+e) from congrArg complete (by omega),
    show complete (d+c+b+a) = complete (a+b+c+d) from congrArg complete (by omega),
    show complete (e+d+c+b+a) = complete (a+b+c+d+e) from congrArg complete (by omega)]
  ring

/-- The complete five-row composition statement follows from endpoint
recovery and the six middle permutations, with exact cut multiplicities. -/
theorem ribbon_five_classification (a b c d e A B C D E : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hs : ribbon a b c d e = ribbon A B C D E) :
    (a = A ∧ b = B ∧ c = C ∧ d = D ∧ e = E) ∨
      (a = E ∧ b = D ∧ c = C ∧ d = B ∧ e = A) ∨
      ribbonExceptional a b c d e A B C D E := by
  obtain ⟨hrow,hedge,_,_⟩ := ribbon_invariants a b c d e A B C D E
    ha hb hc hd he hA hB hC hD hE hs
  rcases endpoint_reading hrow hedge with ⟨h0,h4⟩ | ⟨h0,h4⟩
  · exact aligned_ribbon_classification a b c d e A B C D E
      ha hb hc hd he hA hB hC hD hE hs h0 h4
  · apply ribbonClass_reverse_right
    exact aligned_ribbon_classification a b c d e E D C B A
      ha hb hc hd he hE hD hC hB hA (hs.trans (ribbon_reverse A B C D E).symm) h0 h4

/-- Faithful restoration of the sixteen homogeneous five-row terms. -/
theorem restore_uniform_interval (z : ℕ) (a b c d e : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    restoreIndices z (interval hTilde a b c d e 0 0 0 0) =
      interval hTilde (a+z) (b+z) (c+z) (d+z) (e+z) z z z z := by
  simp only [interval, map_sub, map_add, map_mul, sub_zero, add_zero, zero_add,
    restore_hTilde z a ha.le, restore_hTilde z b hb.le, restore_hTilde z c hc.le,
    restore_hTilde z d hd.le, restore_hTilde z e he.le,
    restore_hTilde z 0 (by omega),
    restore_hTilde z (a+b) (by omega), restore_hTilde z (b+c) (by omega),
    restore_hTilde z (c+d) (by omega), restore_hTilde z (d+e) (by omega),
    restore_hTilde z (a+b+c) (by omega), restore_hTilde z (b+c+d) (by omega),
    restore_hTilde z (c+d+e) (by omega), restore_hTilde z (a+b+c+d) (by omega),
    restore_hTilde z (b+c+d+e) (by omega),
    restore_hTilde z (a+b+c+d+e) (by omega)]
  simp only [
    show (a+(z:ℤ))+(b+z)-z = a+b+z by omega,
    show (b+(z:ℤ))+(c+z)-z = b+c+z by omega,
    show (c+(z:ℤ))+(d+z)-z = c+d+z by omega,
    show (d+(z:ℤ))+(e+z)-z = d+e+z by omega,
    show (a+(z:ℤ))+(b+z)+(c+z)-z-z = a+b+c+z by omega,
    show (b+(z:ℤ))+(c+z)+(d+z)-z-z = b+c+d+z by omega,
    show (c+(z:ℤ))+(d+z)+(e+z)-z-z = c+d+e+z by omega,
    show (a+(z:ℤ))+(b+z)+(c+z)+(d+z)-z-z-z = a+b+c+d+z by omega,
    show (b+(z:ℤ))+(c+z)+(d+z)+(e+z)-z-z-z = b+c+d+e+z by omega,
    show (a+(z:ℤ))+(b+z)+(c+z)+(d+z)+(e+z)-z-z-z-z = a+b+c+d+e+z by omega]

/-- Minimum subtraction is injective even at numerical generator collisions. -/
theorem uniform_interval_eq_iff (z : ℕ) (a b c d e A B C D E : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E) :
    interval hTilde (a+z) (b+z) (c+z) (d+z) (e+z) z z z z =
      interval hTilde (A+z) (B+z) (C+z) (D+z) (E+z) z z z z ↔
    interval hTilde a b c d e 0 0 0 0 =
      interval hTilde A B C D E 0 0 0 0 := by
  rw [← restore_uniform_interval z a b c d e ha hb hc hd he,
    ← restore_uniform_interval z A B C D E hA hB hC hD hE]
  exact (restoreIndices_injective z).eq_iff

/-- The actual independent-H0 determinant, with no assumed expansion certificate. -/
theorem schurHom_interval (P : Profile 4) (hP : P.Hessenberg) :
    P.schurHom = interval hTilde (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
      (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
  have hneg (k : ℤ) (hk : k < 0) : hTilde k = 0 := by simp [hTilde, hk]
  have hm : (Matrix.of fun i j : Fin 5 => hTilde (P.xi i - P.zeta j)) =
      upperMatrix hTilde (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.r 4)
        (P.g 0) (P.g 1) (P.g 2) (P.g 3) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.of_apply]
    all_goals simp only [upperMatrix, Matrix.cons_val]
    all_goals first
      | exact hneg _ (hP _ _ (by decide))
      | (congr 1; simp [Profile.xi, Profile.zeta, Fin.sum_univ_succ] <;> ring)
  rw [Profile.schurHom, hm, det_upperMatrix]

/-- Shortened rows are positive by the actual endpoint overlap inequalities. -/
theorem shortened_rows_positive (P : Profile 4) (z : ℕ)
    (hg : ∀ j, P.g j = z) : ∀ i : Fin 5, 0 < (P.r i : ℤ) - z := by
  intro i
  have h0 := P.g_lt_castSucc 0
  have h1 := P.g_lt_castSucc 1
  have h2 := P.g_lt_castSucc 2
  have h3 := P.g_lt_castSucc 3
  have h4 := P.g_lt_succ 3
  simp only [hg] at h0 h1 h2 h3 h4
  fin_cases i <;> norm_num at h0 h1 h2 h3 h4 ⊢ <;> omega

/-- Actual Schur equality produces the full shortened ribbon equality. -/
theorem constant_gap_ribbon_equality (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z : ℕ)
    (hPg : ∀ j, P.g j = z) (hQg : ∀ j, Q.g j = z)
    (he : P.schur = Q.schur) :
    ribbon ((P.r 0 : ℤ)-z) ((P.r 1 : ℤ)-z) ((P.r 2 : ℤ)-z)
      ((P.r 3 : ℤ)-z) ((P.r 4 : ℤ)-z) =
    ribbon ((Q.r 0 : ℤ)-z) ((Q.r 1 : ℤ)-z) ((Q.r 2 : ℤ)-z)
      ((Q.r 3 : ℤ)-z) ((Q.r 4 : ℤ)-z) := by
  have hp := shortened_rows_positive P z hPg
  have hq := shortened_rows_positive Q z hQg
  have hh := (Profile.schur_eq_iff_schurHom_eq P Q).mp he
  rw [schurHom_interval P hP.hessenberg, schurHom_interval Q hQ.hessenberg] at hh
  simp only [hPg, hQg] at hh
  have hshort := (uniform_interval_eq_iff z
    ((P.r 0 : ℤ)-z) ((P.r 1 : ℤ)-z) ((P.r 2 : ℤ)-z)
    ((P.r 3 : ℤ)-z) ((P.r 4 : ℤ)-z)
    ((Q.r 0 : ℤ)-z) ((Q.r 1 : ℤ)-z) ((Q.r 2 : ℤ)-z)
    ((Q.r 3 : ℤ)-z) ((Q.r 4 : ℤ)-z)
    (hp 0) (hp 1) (hp 2) (hp 3) (hp 4)
    (hq 0) (hq 1) (hq 2) (hq 3) (hq 4)).mp (by simpa only [sub_add_cancel] using hh)
  have hd := congrArg dehom hshort
  simpa only [ribbon, interval, map_sub, map_add, map_mul, dehom_hTilde,
    ← complete_eq_hh] using hd

/-- The literal integer row word of an actual profile. -/
def rows (P : Profile 4) : Fin 5 → ℤ := fun i => P.r i

/-- Five canonical coordinate equations determine the actual row function. -/
theorem rows_eq_iff (P : Profile 4) (v : Fin 5 → ℤ) :
    rows P = v ↔
      (P.r 0 : ℤ) = v 0 ∧ (P.r 1 : ℤ) = v 1 ∧
      (P.r 2 : ℤ) = v 2 ∧ (P.r 3 : ℤ) = v 3 ∧ (P.r 4 : ℤ) = v 4 := by
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2,congrFun h 3,congrFun h 4⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩
    funext i
    fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

/-- The four constant-gap B profiles, written in their actual coordinates. -/
def BMember (P : Profile 4) (p m : ℤ) (z : ℕ) : Prop :=
  (∀ j, P.g j = z) ∧
    (rows P = ![p,m,p,p+m-z,m] ∨
     rows P = ![p,p+m-z,m,p,m] ∨
     rows P = ![m,p+m-z,p,m,p] ∨
     rows P = ![m,p,m,p+m-z,p])

/-- Complete actual same-gap classification, including identity and rotation. -/
def ClassifiedAt (z : ℕ) (P Q : Profile 4) : Prop :=
  P = Q ∨ P = Q.rotate ∨
    ∃ p m : ℤ, 2*(z : ℤ) < p ∧ 2*(z : ℤ) < m ∧ p ≠ m ∧
      BMember P p m z ∧ BMember Q p m z

private theorem equal_rows_profile (P Q : Profile 4)
    (hr : rows P = rows Q) (hg : P.g = Q.g) : P = Q := by
  apply Profile.ext
  · funext i
    have hi := congrFun hr i
    simp only [rows] at hi
    exact_mod_cast hi
  · exact hg

/-- The B words satisfy the standing geometry; there is no extra domain certificate. -/
theorem b_member_thick (P : Profile 4) (p m : ℤ) (z : ℕ)
    (hp : 2*(z : ℤ) < p) (hm : 2*(z : ℤ) < m)
    (h : BMember P p m z) : Staircase.Thick P := by
  obtain ⟨hg, hr⟩ := h
  rcases hr with hr | hr | hr | hr
  all_goals rcases (rows_eq_iff P _).mp hr with ⟨h0,h1,h2,h3,h4⟩
  all_goals simp only [Matrix.cons_val] at h0 h1 h2 h3 h4
  all_goals intro j k hjk
  all_goals rw [hg j,hg k]
  all_goals fin_cases j <;> fin_cases k <;> norm_num at hjk
  all_goals first
    | change z+z < P.r 1
    | change z+z < P.r 2
    | change z+z < P.r 3
  all_goals omega

private theorem direct_b_schur (P : Profile 4) (p m : ℤ) (z : ℕ)
    (hp : 2*(z : ℤ) < p) (hm : 2*(z : ℤ) < m)
    (hg : ∀ j, P.g j = z)
    (hr : rows P = ![p,m,p,p+m-z,m] ∨ rows P = ![p,p+m-z,m,p,m]) :
    P.schur = interval hh p m p (p+m-z) m z z z z := by
  have hmem : BMember P p m z := ⟨hg, hr.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  rw [schur_interval P (b_member_thick P p m z hp hm hmem).hessenberg]
  simp only [hg]
  rcases hr with hr | hr
  · simpa only [rows, Matrix.cons_val] using
      (congrArg (fun v : Fin 5 → ℤ => interval hh (v 0) (v 1) (v 2) (v 3) (v 4)
        z z z z) hr)
  · have hi := congrArg (fun v : Fin 5 → ℤ =>
        interval hh (v 0) (v 1) (v 2) (v 3) (v 4) z z z z) hr
    simp only [rows, Matrix.cons_val] at hi
    exact hi.trans (b_identity hh p m z z).symm

/-- Reversal keeps the whole quartet, not just the displayed F/H pair. -/
theorem b_member_rotate (P : Profile 4) (p m : ℤ) (z : ℕ)
    (h : BMember P p m z) : BMember P.rotate p m z := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨?_, ?_⟩
  · intro j
    simp only [Profile.rotate]
    exact hg _
  · rcases hr with hr | hr | hr | hr
    · right; right; left
      funext i
      have hi := congrFun hr (Fin.rev i)
      fin_cases i <;> simpa [rows, Profile.rotate] using hi
    · right; right; right
      funext i
      have hi := congrFun hr (Fin.rev i)
      fin_cases i <;> simpa [rows, Profile.rotate] using hi
    · left
      funext i
      have hi := congrFun hr (Fin.rev i)
      fin_cases i <;> simpa [rows, Profile.rotate] using hi
    · right; left
      funext i
      have hi := congrFun hr (Fin.rev i)
      fin_cases i <;> simpa [rows, Profile.rotate] using hi

/-- Every member of the quartet has the same full actual polynomial. -/
theorem b_member_schur (P : Profile 4) (p m : ℤ) (z : ℕ)
    (hp : 2*(z : ℤ) < p) (hm : 2*(z : ℤ) < m) (h : BMember P p m z) :
    P.schur = interval hh p m p (p+m-z) m z z z z := by
  rcases h.2 with hr | hr | hr | hr
  · exact direct_b_schur P p m z hp hm h.1 (Or.inl hr)
  · exact direct_b_schur P p m z hp hm h.1 (Or.inr hr)
  · rw [← Profile.schur_rotate P]
    apply direct_b_schur P.rotate p m z hp hm (b_member_rotate P p m z h).1
    left
    funext i
    have hi := congrFun hr (Fin.rev i)
    fin_cases i <;> simpa [rows, Profile.rotate] using hi
  · rw [← Profile.schur_rotate P]
    apply direct_b_schur P.rotate p m z hp hm (b_member_rotate P p m z h).1
    right
    funext i
    have hi := congrFun hr (Fin.rev i)
    fin_cases i <;> simpa [rows, Profile.rotate] using hi

/-- Sufficiency is an equality of complete actual Schur polynomials. -/
theorem classified_schur_eq (z : ℕ) (P Q : Profile 4)
    (h : ClassifiedAt z P Q) : P.schur = Q.schur := by
  rcases h with h | h | ⟨p,m,hp,hm,_,hP,hQ⟩
  · rw [h]
  · rw [h, Profile.schur_rotate]
  · exact (b_member_schur P p m z hp hm hP).trans
      (b_member_schur Q p m z hp hm hQ).symm

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Necessity for actual thick five-row profiles with four equal positive gaps. -/
theorem constant_gap_classification (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z : ℕ) (hz : 0 < z)
    (hPg : ∀ j, P.g j = z) (hQg : ∀ j, Q.g j = z)
    (he : P.schur = Q.schur) : ClassifiedAt z P Q := by
  have hp := shortened_rows_positive P z hPg
  have hq := shortened_rows_positive Q z hQg
  have hr := ribbon_five_classification
    ((P.r 0 : ℤ)-z) ((P.r 1 : ℤ)-z) ((P.r 2 : ℤ)-z)
    ((P.r 3 : ℤ)-z) ((P.r 4 : ℤ)-z)
    ((Q.r 0 : ℤ)-z) ((Q.r 1 : ℤ)-z) ((Q.r 2 : ℤ)-z)
    ((Q.r 3 : ℤ)-z) ((Q.r 4 : ℤ)-z)
    (hp 0) (hp 1) (hp 2) (hp 3) (hp 4)
    (hq 0) (hq 1) (hq 2) (hq 3) (hq 4)
    (constant_gap_ribbon_equality P Q hP hQ z hPg hQg he)
  have hg : P.g = Q.g := by funext j; rw [hPg, hQg]
  have hgr : P.g = Q.rotate.g := by
    funext j
    simp only [Profile.rotate]
    rw [hPg, hQg]
  rcases hr with hr | hr | hr
  · left
    apply equal_rows_profile P Q _ hg
    apply (rows_eq_iff P _).mpr
    simp only [rows]
    omega
  · right; left
    apply equal_rows_profile P Q.rotate _ hgr
    apply (rows_eq_iff P _).mpr
    simp [rows,Profile.rotate]
    omega
  · have ht1 := hP 0 1 (by decide)
    have ht2 := hP 1 2 (by decide)
    have ht3 := hP 2 3 (by decide)
    simp only [hPg] at ht1 ht2 ht3
    norm_num at ht1 ht2 ht3
    unfold ribbonExceptional at hr
    rcases hr with ⟨hc,he,hd,hr⟩ | ⟨hd,he,hb,hr⟩
    · have hpm : 2*(z : ℤ) < (P.r 0 : ℤ) := by omega
      have hmp : 2*(z : ℤ) < (P.r 1 : ℤ) := by omega
      by_cases hne : (P.r 0 : ℤ) = (P.r 1 : ℤ)
      · rcases hr with hr | hr
        · right; left
          apply equal_rows_profile P Q.rotate _ hgr
          apply (rows_eq_iff P _).mpr
          simp [rows,Profile.rotate]
          omega
        · left
          apply equal_rows_profile P Q _ hg
          apply (rows_eq_iff P _).mpr
          simp only [rows]
          omega
      · have hc' : (P.r 2 : ℤ) = P.r 0 := by omega
        have he' : (P.r 4 : ℤ) = P.r 1 := by omega
        have hd' : (P.r 3 : ℤ) = (P.r 0 : ℤ)+P.r 1-z := by omega
        have hPr : rows P = ![(P.r 0 : ℤ),(P.r 1 : ℤ),(P.r 0 : ℤ),
            (P.r 0 : ℤ)+P.r 1-z,(P.r 1 : ℤ)] :=
          (rows_eq_iff P _).mpr ⟨rfl,rfl,hc',hd',he'⟩
        right; right
        refine ⟨(P.r 0 : ℤ),(P.r 1 : ℤ),hpm,hmp,hne,
          ⟨hPg,Or.inl hPr⟩,⟨hQg,?_⟩⟩
        · rcases hr with hr | hr
          · right; left
            apply (rows_eq_iff Q _).mpr
            simp only [Matrix.cons_val]
            omega
          · right; right; right
            apply (rows_eq_iff Q _).mpr
            simp only [Matrix.cons_val]
            omega
    · have hpm : 2*(z : ℤ) < (P.r 0 : ℤ) := by omega
      have hmp : 2*(z : ℤ) < (P.r 2 : ℤ) := by omega
      by_cases hne : (P.r 0 : ℤ) = (P.r 2 : ℤ)
      · rcases hr with hr | hr
        · right; left
          apply equal_rows_profile P Q.rotate _ hgr
          apply (rows_eq_iff P _).mpr
          simp [rows,Profile.rotate]
          omega
        · left
          apply equal_rows_profile P Q _ hg
          apply (rows_eq_iff P _).mpr
          simp only [rows]
          omega
      · have hd' : (P.r 3 : ℤ) = P.r 0 := by omega
        have he' : (P.r 4 : ℤ) = P.r 2 := by omega
        have hb' : (P.r 1 : ℤ) = (P.r 0 : ℤ)+P.r 2-z := by omega
        have hPr : rows P = ![(P.r 0 : ℤ),(P.r 0 : ℤ)+P.r 2-z,
            (P.r 2 : ℤ),(P.r 0 : ℤ),(P.r 2 : ℤ)] :=
          (rows_eq_iff P _).mpr ⟨rfl,hb',rfl,hd',he'⟩
        right; right
        refine ⟨(P.r 0 : ℤ),(P.r 2 : ℤ),hpm,hmp,hne,
          ⟨hPg,Or.inr (Or.inl hPr)⟩,⟨hQg,?_⟩⟩
        · rcases hr with hr | hr
          · left
            apply (rows_eq_iff Q _).mpr
            simp only [Matrix.cons_val]
            omega
          · right; right; left
            apply (rows_eq_iff Q _).mpr
            simp only [Matrix.cons_val]
            omega

/-- Uniform necessary and sufficient classification at every positive common
gap, with all numerical collisions and the complete quartet retained. -/
theorem constant_gap_schur_eq_iff (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z : ℕ) (hz : 0 < z)
    (hPg : ∀ j, P.g j = z) (hQg : ∀ j, Q.g j = z) :
    P.schur = Q.schur ↔ ClassifiedAt z P Q :=
  ⟨constant_gap_classification P Q hP hQ z hz hPg hQg,
    classified_schur_eq z P Q⟩

/-- The common gap on the mate is produced by the actual overlap invariant. -/
theorem mate_constant_gaps (P Q : Profile 4) (z : ℕ)
    (hPg : ∀ j, P.g j = z) (he : P.schur = Q.schur) :
    ∀ j, Q.g j = z := by
  have hg := Profile.gaps_eq_of_schur_eq he
  intro j
  have hj : Q.g j ∈ Q.gapMultiset :=
    Multiset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
  rw [← hg] at hj
  obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp hj
  rw [hPg k] at hk
  exact hk.symm

/-- Full constant-gap class against every actual thick five-row mate.  The
mate's gap word is a conclusion, not an additional standing assumption. -/
theorem constant_gap_full_class (P Q : Profile 4)
    (hP : Staircase.Thick P) (hQ : Staircase.Thick Q) (z : ℕ) (hz : 0 < z)
    (hPg : ∀ j, P.g j = z) :
    P.schur = Q.schur ↔ ClassifiedAt z P Q := by
  constructor
  · intro he
    exact constant_gap_classification P Q hP hQ z hz hPg
      (mate_constant_gaps P Q z hPg he) he
  · exact classified_schur_eq z P Q

end SkewJacobiNegative.ConstantGapFiveClassification
