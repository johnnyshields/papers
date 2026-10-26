/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Unsigned

/-!
# Near-squaring is not linear on inventories

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:algebra` (`rem:nonlinear`).

`G_{(1,1,4)} + G_{(1,2,3)} - G_{(1,4,1)} - G_{(2,1,3)} = 0`, whereas the same combination of the
near-squares has coefficient one at `h₄ h₃² h₂`.  Coefficients are computed through
`coeff_G`: the coefficient of `h_λ` in `G_β` is the coarsening multiplicity `mult`.
Consequently no linear map on `Λ` (over `ℤ` or over `ℚ`) sends every weight-six `G_α` to
`G_{α^{⊙2}}`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset MvPolynomial

/-- The positive entries of a multiset, as a multiset of `ℕ+`. -/
def posParts (l : Multiset ℕ) : Multiset ℕ+ :=
  l.filterMap fun x => if h : 0 < x then some (Nat.toPNat x h) else none

lemma prod_hgen_eq (l : Multiset ℕ) :
    (l.map hgen).prod = ((posParts l).map MvPolynomial.X).prod := by
  induction l using Multiset.induction with
  | empty => simp [posParts]
  | cons a l ih =>
    by_cases ha : 0 < a
    · have h1 : posParts (a ::ₘ l) = Nat.toPNat a ha ::ₘ posParts l := by
        unfold posParts
        rw [Multiset.filterMap_cons_some (b := Nat.toPNat a ha) _ _ _ (by simp [ha])]
      rw [h1, Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ih]
      simp only [hgen, ha, dite_true]
      rfl
    · have h0 : a = 0 := by omega
      subst h0
      have h1 : posParts (0 ::ₘ l) = posParts l := by
        unfold posParts
        rw [Multiset.filterMap_cons_none _ _ (by simp)]
      rw [h1, Multiset.map_cons, Multiset.prod_cons, ih]
      simp [hgen]

lemma prod_X_eq_monomial (m : Multiset ℕ+) :
    (m.map (MvPolynomial.X : ℕ+ → Lam)).prod = monomial (Multiset.toFinsupp m) (1 : ℤ) := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add,
      Multiset.toFinsupp_singleton, MvPolynomial.X, monomial_mul_monomial]
    simp

lemma posParts_cons_pos {a : ℕ} (ha : 0 < a) (l : Multiset ℕ) :
    posParts (a ::ₘ l) = Nat.toPNat a ha ::ₘ posParts l := by
  unfold posParts
  rw [Multiset.filterMap_cons_some (b := Nat.toPNat a ha) _ _ _ (by simp [ha])]

lemma map_val_posParts {l : Multiset ℕ} (hl : ∀ x ∈ l, 0 < x) :
    (posParts l).map (fun x : ℕ+ => (x : ℕ)) = l := by
  induction l using Multiset.induction with
  | empty => simp [posParts]
  | cons a l ih =>
    have ha : 0 < a := hl a (Multiset.mem_cons_self _ _)
    rw [posParts_cons_pos ha, Multiset.map_cons,
      ih (fun x hx => hl x (Multiset.mem_cons_of_mem hx))]
    simp [Nat.toPNat]

/-- The block lengths of a coarsening are positive. -/
lemma gaps_pos {n : ℕ} (hn : 0 < n) {T : Finset ℕ} (hT : IsCutSet n T) :
    ∀ x ∈ gaps n T, 0 < x := by
  intro x hx
  unfold gaps at hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  have hy' : y ∈ insert n T := hy
  have hy0 : 0 < y := by
    rcases Finset.mem_insert.mp hy' with rfl | h
    · exact hn
    · exact (Finset.mem_Ioo.mp (hT h)).1
  have : (T.filter (· < y)).sup id < y := by
    rw [Finset.sup_lt_iff hy0]
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  omega

/-- The coefficient of `h_λ` in `G_β` is the coarsening multiplicity `m_β(λ)` (`eq:introG`). -/
theorem coeff_G {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) (lam : Multiset ℕ)
    (hlam : ∀ x ∈ lam, 0 < x) :
    (G n S).coeff (Multiset.toFinsupp (posParts lam)) = (mult n S lam : ℤ) := by
  unfold G mult
  rw [MvPolynomial.coeff_sum, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hT) hx)
  rw [prod_hgen_eq, prod_X_eq_monomial, MvPolynomial.coeff_monomial]
  have hiff : Multiset.toFinsupp (posParts (gaps n T)) = Multiset.toFinsupp (posParts lam) ↔
      gaps n T = lam := by
    constructor
    · intro h
      have h1 := Multiset.toFinsupp.injective h
      rw [← map_val_posParts (gaps_pos hn hT'), h1, map_val_posParts hlam]
    · intro h; rw [h]
  by_cases h : gaps n T = lam
  · simp [h]
  · have : ¬ Multiset.toFinsupp (posParts (gaps n T)) = Multiset.toFinsupp (posParts lam) :=
      fun hh => h (hiff.mp hh)
    simp [this, h]

lemma G_eq_sum (n : ℕ) (S : Finset ℕ) :
    G n S = ((S.powerset.val.map (gaps n)).map fun l => (l.map hgen).prod).sum := by
  unfold G
  rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
  rfl

/-- `rem:nonlinear`, first identity.  The four weight-six inventories satisfy
`G_{(1,1,4)} + G_{(1,2,3)} - G_{(1,4,1)} - G_{(2,1,3)} = 0`. -/
theorem nonlinear_G_combination :
    G 6 {1, 2} + G 6 {1, 3} - G 6 {1, 5} - G 6 {2, 3} = 0 := by
  have e1 : (({1, 2} : Finset ℕ).powerset.val.map (gaps 6))
      = {{6}, {1, 5}, {2, 4}, {1, 1, 4}} := by decide
  have e2 : (({1, 3} : Finset ℕ).powerset.val.map (gaps 6))
      = {{6}, {1, 5}, {3, 3}, {1, 2, 3}} := by decide
  have e3 : (({1, 5} : Finset ℕ).powerset.val.map (gaps 6))
      = {{6}, {1, 5}, {5, 1}, {1, 4, 1}} := by decide
  have e4 : (({2, 3} : Finset ℕ).powerset.val.map (gaps 6))
      = {{6}, {2, 4}, {3, 3}, {2, 1, 3}} := by decide
  rw [G_eq_sum, G_eq_sum, G_eq_sum, G_eq_sum, e1, e2, e3, e4]
  simp
  ring

lemma coeff_add' (m : ℕ+ →₀ ℕ) (p q : Lam) : (p + q).coeff m = p.coeff m + q.coeff m :=
  (MvPolynomial.coeffAddMonoidHom m).map_add p q

/-- `rem:nonlinear`, second assertion.  The near-squares `α ⊙ α` (weight `12`, cut set
`S ∪ (S + 6)`) of the four compositions `(1,1,4)`, `(1,2,3)`, `(1,4,1)`, `(2,1,3)` combine, with
the same signs, to a polynomial with coefficient one at `h₄ h₃² h₂`. -/
theorem nonlinear_nearSquare_coeff :
    (G 12 (nearCuts 6 {1, 2} {1, 2}) + G 12 (nearCuts 6 {1, 3} {1, 3})
        - G 12 (nearCuts 6 {1, 5} {1, 5}) - G 12 (nearCuts 6 {2, 3} {2, 3})).coeff
      (Multiset.toFinsupp (posParts {4, 3, 3, 2})) = 1 := by
  have hc : ∀ S : Finset ℕ, IsCutSet 6 S → IsCutSet 12 (nearCuts 6 S S) := by
    intro S hS x hx
    simp only [nearCuts, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with h | ⟨y, hy, rfl⟩
    · have := Finset.mem_Ioo.mp (hS h); exact Finset.mem_Ioo.mpr ⟨this.1, by omega⟩
    · have := Finset.mem_Ioo.mp (hS hy); exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
  have hcs12 : IsCutSet 6 {1, 2} := by simp [IsCutSet, Finset.subset_iff]
  have hcs13 : IsCutSet 6 {1, 3} := by simp [IsCutSet, Finset.subset_iff]
  have hcs15 : IsCutSet 6 {1, 5} := by simp [IsCutSet, Finset.subset_iff]
  have hcs23 : IsCutSet 6 {2, 3} := by simp [IsCutSet, Finset.subset_iff]
  have hpos : ∀ x ∈ ({4, 3, 3, 2} : Multiset ℕ), 0 < x := by decide
  have c1 := coeff_G (n := 12) (by norm_num) (hc {1, 2} hcs12) _ hpos
  have c2 := coeff_G (n := 12) (by norm_num) (hc {1, 3} hcs13) _ hpos
  have c3 := coeff_G (n := 12) (by norm_num) (hc {1, 5} hcs15) _ hpos
  have c4 := coeff_G (n := 12) (by norm_num) (hc {2, 3} hcs23) _ hpos
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, coeff_add', c1, c2, c3, c4]
  have m1 : mult 12 (nearCuts 6 {1, 2} {1, 2}) {4, 3, 3, 2} = 0 := by decide
  have m2 : mult 12 (nearCuts 6 {1, 3} {1, 3}) {4, 3, 3, 2} = 1 := by decide
  have m3 : mult 12 (nearCuts 6 {1, 5} {1, 5}) {4, 3, 3, 2} = 0 := by decide
  have m4 : mult 12 (nearCuts 6 {2, 3} {2, 3}) {4, 3, 3, 2} = 0 := by decide
  rw [m1, m2, m3, m4]
  norm_num

/-- `rem:nonlinear`, conclusion.  No additive (in particular no `ℚ`-linear after clearing
denominators) map `L : Λ → Λ` sends each of the four weight-six `G_α` to the inventory
`G_{α ⊙ α}` of its near-square. -/
theorem no_linear_nearSquare (L : Lam →+ Lam)
    (h1 : L (G 6 {1, 2}) = G 12 (nearCuts 6 {1, 2} {1, 2}))
    (h2 : L (G 6 {1, 3}) = G 12 (nearCuts 6 {1, 3} {1, 3}))
    (h3 : L (G 6 {1, 5}) = G 12 (nearCuts 6 {1, 5} {1, 5}))
    (h4 : L (G 6 {2, 3}) = G 12 (nearCuts 6 {2, 3} {2, 3})) : False := by
  have h0 : L (G 6 {1, 2} + G 6 {1, 3} - G 6 {1, 5} - G 6 {2, 3}) = 0 := by
    rw [nonlinear_G_combination, map_zero]
  rw [map_sub, map_sub, map_add, h1, h2, h3, h4] at h0
  have := nonlinear_nearSquare_coeff
  rw [h0] at this
  simp at this

end SkewRibbonCoarsenings
