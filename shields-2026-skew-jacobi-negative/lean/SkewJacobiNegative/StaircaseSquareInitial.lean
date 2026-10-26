/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseResidualAlgebra

/-!
# Square-initial readings after generator erasure

The surviving-diagonal step in `thm:staircase-residual-matching`.
These readings hold in every order without a prescribed interval contact.
-/

namespace SkewJacobiNegative.Staircase
open Gluing HessenbergExpansion

private theorem erase_eq_rename_kill (q : ℕ+) (p : CompleteRing) :
    eraseGenerator q p =
      MvPolynomial.rename (Subtype.val : {i : ℕ+ // i ≠ q} → ℕ+)
        (MvPolynomial.killCompl Subtype.val_injective p) := by
  classical
  let S := {i : ℕ+ // i ≠ q}
  let f : S → ℕ+ := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  change eraseGenerator q p = MvPolynomial.rename f (MvPolynomial.killCompl hf p)
  induction p using MvPolynomial.induction_on with
  | C a => simp [eraseGenerator, MvPolynomial.killCompl]
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    by_cases hi : i = q
    · subst i
      have hn : q ∉ Set.range f := by
        rintro ⟨j,hj⟩
        exact j.2 hj
      have hk : MvPolynomial.killCompl hf (MvPolynomial.X q : CompleteRing) = 0 := by
        simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dite_eq_right hn]
      simp [eraseGenerator, hk]
    · have hx : (MvPolynomial.X i : CompleteRing) =
          MvPolynomial.rename f (MvPolynomial.X (⟨i,hi⟩ : S)) := by simp [f]
      rw [hx, MvPolynomial.killCompl_rename_app]
      simp [eraseGenerator, f, hi]

private theorem erase_coeff (q : ℕ+) (p : CompleteRing) (d : ℕ+ →₀ ℕ) :
    (eraseGenerator q p).coeff d = if d q = 0 then p.coeff d else 0 := by
  classical
  let S := {i : ℕ+ // i ≠ q}
  let f : S → ℕ+ := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hn : q ∉ Set.range f := by
    rintro ⟨j,hj⟩
    exact j.2 hj
  rw [erase_eq_rename_kill]
  change (MvPolynomial.rename f (MvPolynomial.killCompl hf p)).coeff d = _
  by_cases hd : d q = 0
  · have hs : (d.support : Set ℕ+) ⊆ Set.range f := by
      intro i hi
      refine ⟨⟨i,?_⟩,rfl⟩
      intro he
      subst i
      exact (Finsupp.mem_support_iff.mp hi) hd
    have hmap : (d.comapDomain f hf.injOn).mapDomain f = d :=
      d.mapDomain_comapDomain f hf hs
    rw [if_pos hd, ← hmap, MvPolynomial.coeff_rename_mapDomain f hf,
      MvPolynomial.coeff_killCompl, hmap]
  · rw [if_neg hd]
    apply MvPolynomial.coeff_rename_eq_zero
    intro e he
    have hzero := Finsupp.mapDomain_of_notMem_range e q hn
    rw [he] at hzero
    exact (hd hzero).elim

private theorem erase_weighted_component (q : ℕ+) (w : ℕ+ → ℝ)
    (a : ℝ) (p : CompleteRing) :
    eraseGenerator q (MvPolynomial.weightedHomogeneousComponent w a p) =
      MvPolynomial.weightedHomogeneousComponent w a (eraseGenerator q p) := by
  apply MvPolynomial.ext
  intro d
  simp only [erase_coeff, MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs <;> rfl

/-- Erasure retains a surviving entire lowest-weight component. -/
theorem initialForm_erase_of_fixed (q : ℕ+) (w : ℕ+ → ℝ) (p : CompleteRing)
    (hp : p ≠ 0) (hfix : eraseGenerator q (Base.initialForm w p) = Base.initialForm w p) :
    Base.initialForm w (eraseGenerator q p) = Base.initialForm w p := by
  have hbound : Base.WeightLowerBound w (eraseGenerator q p) (Base.leastWeight w p) := by
    intro d hd
    rw [erase_coeff] at hd
    split_ifs at hd with hzero
    · exact Base.leastWeight_lowerBound w p d hd
    · exact False.elim (hd rfl)
  have hcomp : MvPolynomial.weightedHomogeneousComponent w (Base.leastWeight w p)
      (eraseGenerator q p) = Base.initialForm w p := by
    rw [← erase_weighted_component]
    exact hfix
  have hleast := Base.leastWeight_eq_of_component hbound
    (hcomp ▸ Base.initialForm_ne_zero hp)
  rw [Base.initialForm, hleast, hcomp]

/-- A restriction with no erased diagonal entry keeps its unique
minimum-square diagonal monomial, even if another interval is erased. -/
theorem restriction_square_initial_no_row_contact {n : ℕ} (q : ℕ+) (P : Profile n)
    (hrows : ∀ i, P.r i ≠ q.val) :
    Base.initialForm Base.squareWeight.generatorWeight (restriction q P) =
      ∏ i, complete (P.r i) := by
  have hfix : eraseGenerator q
      (Base.initialForm Base.squareWeight.generatorWeight P.toBetaDiagram.schur) =
        Base.initialForm Base.squareWeight.generatorWeight P.toBetaDiagram.schur := by
    rw [P.toBetaDiagram.square_initialForm, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    change eraseGenerator q (complete (P.xi i - P.zeta i)) = complete (P.xi i - P.zeta i)
    rw [P.xi_sub_zeta i, eraseGenerator_complete, if_neg]
    exact_mod_cast hrows i
  rw [restriction, initialForm_erase_of_fixed q _ _ P.toBetaDiagram.schur_ne_zero hfix,
    P.toBetaDiagram.square_initialForm]
  apply Finset.prod_congr rfl
  intro i hi
  change complete (P.xi i - P.zeta i) = complete (P.r i)
  rw [P.xi_sub_zeta i]

/-- The surviving diagonal recovers the row multiset before any gap placement
or interval-contact classification is supplied. -/
theorem restriction_rows_eq_of_no_row_contact {n m : ℕ} (q : ℕ+)
    (P : Profile n) (Q : Profile m)
    (hP : ∀ i, P.r i ≠ q.val) (hQ : ∀ i, Q.r i ≠ q.val)
    (he : restriction q P = restriction q Q) :
    (List.ofFn P.r : Multiset ℕ) = (List.ofFn Q.r : Multiset ℕ) := by
  have hinit := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [restriction_square_initial_no_row_contact q P hP,
    restriction_square_initial_no_row_contact q Q hQ] at hinit
  apply (Base.prod_complete_eq_iff_of_pos (List.ofFn P.r) (List.ofFn Q.r)
    (by intro k hk; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk; exact P.r_pos i)
    (by intro k hk; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk; exact Q.r_pos i)).mp
  apply integerLift_injective
  simpa only [map_list_prod, List.map_map, Function.comp_def,
    List.map_ofFn, List.prod_ofFn, map_prod, SkewJacobiNegative.complete] using hinit

end SkewJacobiNegative.Staircase
