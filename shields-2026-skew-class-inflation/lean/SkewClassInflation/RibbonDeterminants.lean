/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonPolynomials
import SkewClassInflation.ProfileMergeReadings

/-!
# Ribbon recursion agrees with the actual Jacobi--Trudi determinant

Identifies the independent-generator ribbon polynomial in
`eq:thin-substitution` of `shields-2026-skew-class-inflation.tex`
with the actual full determinant of a zero-gap ribbon profile.
The bridge uses the same complete generators and retains the empty
cofactor convention.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

/-- A zero-gap profile is automatically Hessenberg because all of its rows are positive. -/
theorem zero_gaps_thick {n : ℕ} (P : Profile n) (hg : ∀ j, P.g j = 0) :
    Staircase.Thick P := by
  intro j k _
  rw [hg j, hg k, zero_add]
  exact P.r_pos _

/-- Contracting the first zero gap merges the first two rows and leaves every later row in place. -/
theorem contract_first_row_word {n : ℕ} (P : Profile (n + 1)) (hg : P.g 0 = 0) :
    List.ofFn (contract P 0).r = (P.r 0 + P.r (0 : Fin (n + 1)).succ) ::
      List.ofFn (fun i : Fin n => P.r i.succ.succ) := by
  rw [List.ofFn_succ]
  congr 1
  · have he := contract_joined_row P 0
    rw [hg, Nat.cast_zero, sub_zero] at he
    exact_mod_cast he
  · apply congrArg List.ofFn
    funext i
    rw [contract_row_of_ne P 0 i.succ (by simp),
      Fin.succAbove_of_le_castSucc _ _ (by change 1 ≤ i.val + 1; omega)]

/-- The recursive ribbon polynomial is exactly the full determinant on every zero-gap profile. -/
theorem zero_gaps_ribbon_polynomial {n : ℕ} (P : Profile n) (hg : ∀ j, P.g j = 0) :
    P.toBetaDiagram.schur = ribbonWord (List.ofFn P.r) := by
  induction n with
  | zero =>
    rw [BetaDiagram.schur, Matrix.det_fin_one, List.ofFn_succ, List.ofFn_zero,
      ribbonWord, ribbonTail]
    change complete (P.xi 0 - P.zeta 0) = complete (P.r 0)
    rw [P.xi_sub_zeta]
  | succ n ih =>
    let R : Profile n := rightOfSeam P (0 : Fin (n + 1))
    have hR : ∀ j, R.g j = 0 := fun j => hg _
    have hC : ∀ j, (contract P 0).g j = 0 := by intro j; rw [contract_gap, hg]
    have hrows : List.ofFn R.r = List.ofFn (fun i : Fin (n + 1) => P.r i.succ) := by
      apply congrArg List.ofFn
      funext i
      change P.r (sliceEmbedding 1 n (by omega) i) = P.r i.succ
      congr 1
      apply Fin.ext
      change 1 + i.val = i.val + 1
      omega
    have hleft : (leftOfSeam P (0 : Fin (n + 1))).toBetaDiagram.schur = complete (P.r 0) := by
      let L : Profile 0 := leftOfSeam P (0 : Fin (n + 1))
      change L.toBetaDiagram.schur = complete (P.r 0)
      rw [BetaDiagram.schur, Matrix.det_fin_one]
      change complete (L.xi 0 - L.zeta 0) = complete (P.r 0)
      rw [L.xi_sub_zeta]
      rfl
    have he := schur_join_formula P (zero_gaps_thick P hg) 0
    rw [hleft, hg 0, Nat.cast_zero, complete_zero, one_mul] at he
    change P.toBetaDiagram.schur =
      complete (P.r 0) * R.toBetaDiagram.schur - (contract P 0).toBetaDiagram.schur at he
    rw [ih R hR, ih (contract P 0) hC, hrows, contract_first_row_word P (hg 0)] at he
    rw [List.ofFn_succ (f := fun i : Fin (n + 1) => P.r i.succ)] at he
    rw [List.ofFn_succ, List.ofFn_succ]
    simpa only [ribbonWord, ribbonTail] using he

/-- The actual ribbon profile of a nonempty positive row word. -/
def ribbonRows (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    Profile l.length where
  r i := (a :: l).get ⟨i.val, by have := i.isLt; simp only [List.length_cons]; omega⟩
  g _ := 0
  r_pos i := by
    have hmem := List.get_mem (a :: l)
      (⟨i.val, by have := i.isLt; simp only [List.length_cons]; omega⟩ :
        Fin (a :: l).length)
    rcases List.mem_cons.mp hmem with he | he
    · rw [he]; exact ha
    · exact hl _ he
  g_lt_castSucc j := by
    have hmem := List.get_mem (a :: l)
      (⟨j.castSucc.val, by have := j.castSucc.isLt; simp only [List.length_cons]; omega⟩ :
        Fin (a :: l).length)
    rcases List.mem_cons.mp hmem with he | he
    · rw [he]; exact ha
    · exact hl _ he
  g_lt_succ j := by
    have hmem := List.get_mem (a :: l)
      (⟨j.succ.val, by have := j.succ.isLt; simp only [List.length_cons]; omega⟩ :
        Fin (a :: l).length)
    rcases List.mem_cons.mp hmem with he | he
    · rw [he]; exact ha
    · exact hl _ he

/-- Every nonempty positive word is represented with precisely its actual ordered rows. -/
theorem ribbonRows_word (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    List.ofFn (ribbonRows a ha l hl).r = a :: l := by
  exact List.ofFn_get (a :: l)

/-- The polynomial of a composition word is the actual Schur determinant of its ribbon. -/
theorem ribbonRows_schur (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    (ribbonRows a ha l hl).toBetaDiagram.schur = ribbonWord (a :: l) := by
  rw [zero_gaps_ribbon_polynomial _ (fun _ => rfl), ribbonRows_word]

/-- Equality of actual ribbon functions recovers their full row counts. -/
theorem ribbonWord_eq_length {M N : ℕ} (α : Composition M) (β : Composition N)
    (hM : 0 < M) (hN : 0 < N) (he : ribbonWord α.blocks = ribbonWord β.blocks) :
    α.length = β.length := by
  cases ha : α.blocks with
  | nil =>
    have hs := α.blocks_sum
    rw [ha] at hs
    simp only [List.sum_nil] at hs
    omega
  | cons a l =>
    cases hb : β.blocks with
    | nil =>
      have hs := β.blocks_sum
      rw [hb] at hs
      simp only [List.sum_nil] at hs
      omega
    | cons b r =>
      have ha0 := α.blocks_pos (by rw [ha]; exact List.mem_cons_self)
      have hb0 := β.blocks_pos (by rw [hb]; exact List.mem_cons_self)
      have hl : ∀ k ∈ l, 0 < k := fun k hk =>
        α.blocks_pos (by rw [ha]; exact List.mem_cons_of_mem _ hk)
      have hr : ∀ k ∈ r, 0 < k := fun k hk =>
        β.blocks_pos (by rw [hb]; exact List.mem_cons_of_mem _ hk)
      have hs : (ribbonRows a ha0 l hl).toBetaDiagram.schur =
          (ribbonRows b hb0 r hr).toBetaDiagram.schur := by
        rw [ribbonRows_schur, ribbonRows_schur]
        simpa only [ha, hb] using he
      have hn := (ribbonRows a ha0 l hl).toBetaDiagram.row_count_of_schur_eq
        (ribbonRows b hb0 r hr).toBetaDiagram hs
      simpa only [Composition.length, ha, hb, List.length_cons] using hn

end SkewClassInflation
