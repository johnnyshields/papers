/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonCoarseningFormula

/-!
# Ribbon equality and unsigned coarsening data

The coarsening input to the ribbon classification used in
`lem:overlap-power-rigidity` and `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  The unsigned polynomial records
actual coarsening multiplicities.  Generator-sign reversal relates it
to the signed ribbon formula without assuming classification.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- Reverse the sign of every positive complete generator, retaining rational coefficients. -/
noncomputable def generatorSign : CompleteRing →+* CompleteRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j : ℕ+ => -MvPolynomial.X j)

/-- Generator-sign reversal is a genuine involution. -/
theorem generatorSign_comp_self : generatorSign.comp generatorSign = RingHom.id CompleteRing := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [generatorSign]
  · intro j
    simp [generatorSign]

/-- No information is lost by generator-sign reversal. -/
theorem generatorSign_injective : Function.Injective generatorSign := by
  intro p q he
  have hh := congrArg generatorSign he
  change (generatorSign.comp generatorSign) p = (generatorSign.comp generatorSign) q at hh
  simpa only [generatorSign_comp_self, RingHom.id_apply] using hh

/-- A positive complete generator changes sign.  The unit index is deliberately excluded. -/
theorem generatorSign_complete (a : ℕ) (ha : 0 < a) :
    generatorSign (complete a) = -complete a := by
  let j : ℕ+ := ⟨a, ha⟩
  have hc : complete (a : ℤ) = MvPolynomial.X j := complete_nat j
  rw [hc, generatorSign, MvPolynomial.eval₂Hom_X']

/-- Sign reversal records the exact number of positive factors in an actual coarsening word. -/
theorem generatorSign_product (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    generatorSign ((w.map (fun a : ℕ => complete a)).prod) =
      (-1 : CompleteRing) ^ w.length * (w.map (fun a : ℕ => complete a)).prod := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := hw a List.mem_cons_self
    have ht : ∀ b ∈ w, 0 < b := fun b hb => hw b (List.mem_cons_of_mem _ hb)
    rw [List.map_cons, List.prod_cons, map_mul, generatorSign_complete a ha, ih ht]
    simp only [List.length_cons, pow_succ]
    ring

/-- The unsigned sum counts every actual adjacent-boundary decision with its multiplicity. -/
noncomputable def unsignedCoarseningPolynomial {n : ℕ} (r : Fin (n + 1) → ℕ) : CompleteRing :=
  ∑ S : Fin n → Bool, ((coarsenRows r S).map (fun a : ℕ => complete a)).prod

/-- The classical signed ribbon formula is the unsigned data under a reversible sign change. -/
theorem generatorSign_ribbon {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    generatorSign (ribbonWord (List.ofFn r)) =
      (-1 : CompleteRing) ^ (n + 1) * unsignedCoarseningPolynomial r := by
  rw [ribbon_coarsening_expansion r hr, map_sum, unsignedCoarseningPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_mul, map_pow, map_neg, map_one,
    generatorSign_product _ (coarsenRows_pos r hr S)]
  rw [← mul_assoc, ← pow_add]
  have he : selectedSeams S + (coarsenRows r S).length = n + 1 := by
    have hh := coarsenRows_length r S
    omega
  rw [he]

/-- Send every positive complete generator to one. -/
noncomputable def generatorsOne : CompleteRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun _ : ℕ+ => 1)

/-- The constant-coefficient convention also sends the original unit to one. -/
theorem generatorsOne_complete (a : ℕ) : generatorsOne (complete a) = 1 := by
  by_cases ha : a = 0
  · subst a
    rw [Nat.cast_zero, complete_zero, map_one]
  · let j : ℕ+ := ⟨a, by omega⟩
    have hc : complete (a : ℤ) = MvPolynomial.X j := complete_nat j
    rw [hc, generatorsOne, MvPolynomial.eval₂Hom_X']

/-- Each actual coarsening contributes one to the unsigned count. -/
theorem generatorsOne_product (w : List ℕ) :
    generatorsOne ((w.map (fun a : ℕ => complete a)).prod) = 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, map_mul, generatorsOne_complete, ih, one_mul]

/-- The unsigned data retains the exact number of cut decisions and hence the original row count. -/
theorem generatorsOne_unsignedCoarsening {n : ℕ} (r : Fin (n + 1) → ℕ) :
    generatorsOne (unsignedCoarseningPolynomial r) = (2 : ℚ) ^ n := by
  rw [unsignedCoarseningPolynomial, map_sum]
  simp only [generatorsOne_product, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]

/-- Equality of the unsigned coarsening data produces equality of the original row counts. -/
theorem unsignedCoarsening_eq_row_count {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (he : unsignedCoarseningPolynomial r = unsignedCoarseningPolynomial s) : n = m := by
  have hh := congrArg generatorsOne he
  rw [generatorsOne_unsignedCoarsening, generatorsOne_unsignedCoarsening] at hh
  exact (pow_right_strictMono₀ (by norm_num : (1 : ℚ) < 2)).injective hh

private theorem ribbon_ofFn_eq_row_count {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (he : ribbonWord (List.ofFn r) = ribbonWord (List.ofFn s)) : n = m := by
  let P : Profile n :=
    { r := r, g := fun _ => 0, r_pos := hr,
      g_lt_castSucc := fun j => hr j.castSucc, g_lt_succ := fun j => hr j.succ }
  let Q : Profile m :=
    { r := s, g := fun _ => 0, r_pos := hs,
      g_lt_castSucc := fun j => hs j.castSucc, g_lt_succ := fun j => hs j.succ }
  have hp := zero_gaps_ribbon_polynomial P (fun _ => rfl)
  have hq := zero_gaps_ribbon_polynomial Q (fun _ => rfl)
  have hh : P.toBetaDiagram.schur = Q.toBetaDiagram.schur := hp.trans (he.trans hq.symm)
  exact Nat.succ.inj (P.toBetaDiagram.row_count_of_schur_eq Q.toBetaDiagram hh)

/-- Ribbon equality is exactly equality of its actual unsigned coarsening polynomial. -/
theorem ribbon_eq_iff_unsignedCoarsening {n m : ℕ}
    (r : Fin (n + 1) → ℕ) (s : Fin (m + 1) → ℕ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) :
    ribbonWord (List.ofFn r) = ribbonWord (List.ofFn s) ↔
      unsignedCoarseningPolynomial r = unsignedCoarseningPolynomial s := by
  constructor
  · intro he
    have hn := ribbon_ofFn_eq_row_count r s hr hs he
    subst m
    have hh := congrArg generatorSign he
    rw [generatorSign_ribbon r hr, generatorSign_ribbon s hs] at hh
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : CompleteRing) ≠ 0)) hh
  · intro he
    have hn := unsignedCoarsening_eq_row_count r s he
    subst m
    apply generatorSign_injective
    rw [generatorSign_ribbon r hr, generatorSign_ribbon s hs, he]

end SkewClassInflation
