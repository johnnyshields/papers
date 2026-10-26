/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.HessenbergMembership

/-!
# General separated constant-gap repeated powers

The complete standing domain `eq:saturation-domain` and the actual
row word `A_m` in `eq:repeated-blocks` of
`shields-2026-skew-class-inflation.tex`.  The interior word is arbitrary;
endpoints may agree, repeat inside the word, or coincide with a merger
length.  No Schur-rigidity assumption is included.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Exactly the separated constant-gap inner parameters, with arbitrary positive inner order. -/
structure SaturationInner where
  /-- The number of gaps in the original inner, one fewer than its row count. -/
  k : ℕ
  k_pos : 0 < k
  /-- The original positive inner row lengths, in their actual order. -/
  r : Fin (k + 1) → ℕ
  /-- The constant gap inside each inner copy. -/
  c : ℕ
  /-- The larger distinguished overlap between consecutive copies. -/
  d : ℕ
  c_lt_d : c < d
  first_bound : c + d < r 0
  last_bound : c + d < r (Fin.last k)
  interior_bound : ∀ i, 0 < i.val → i.val < k → max (2 * c) d < r i

namespace SaturationInner

variable (A : SaturationInner)

/-- The literal row created by identifying adjacent end marks. -/
def merger : ℕ := A.r 0 + A.r (Fin.last A.k) - A.d

/-- A merger is strictly larger than both internal overlap strips and the marked seam. -/
theorem merger_bound : max (2 * A.c) A.d < A.merger := by
  have ha := A.first_bound
  have hb := A.last_bound
  unfold merger
  omega

/-- Every original row exceeds its internal constant gap. -/
theorem row_above_gap (i : Fin (A.k + 1)) : A.c < A.r i := by
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    rw [he]
    have := A.first_bound
    omega
  · by_cases hl : i.val = A.k
    · have he : i = Fin.last A.k := Fin.ext hl
      rw [he]
      have := A.last_bound
      omega
    · have hh := A.interior_bound i (by omega) (by have := i.isLt; omega)
      omega

/-- The original connected constant-gap inner in `eq:saturation-domain`. -/
def profile : Profile A.k where
  r := A.r
  g _ := A.c
  r_pos i := by have := A.row_above_gap i; omega
  g_lt_castSucc j := A.row_above_gap j.castSucc
  g_lt_succ j := A.row_above_gap j.succ

/-- The repeated-power row word, with each interior merger at its actual position. -/
def powerRows (m : ℕ) (i : Fin (m * A.k + 1)) : ℕ :=
  if i.val = 0 then A.r 0 else
  if i.val = m * A.k then A.r (Fin.last A.k) else
  if i.val % A.k = 0 then A.merger else
    A.r ⟨i.val % A.k, by have := Nat.mod_lt i.val A.k_pos; omega⟩

/-- Each actual repeated-power row is strictly above the constant internal gap. -/
theorem powerRows_above_gap (m : ℕ) (i : Fin (m * A.k + 1)) :
    A.c < A.powerRows m i := by
  unfold powerRows
  split_ifs
  · exact A.row_above_gap 0
  · exact A.row_above_gap (Fin.last A.k)
  · have := A.merger_bound
    omega
  · exact A.row_above_gap _

/-- The literal repeated power on the manuscript's positive-copy domain. -/
def power (m : ℕ) (_hm : 0 < m) : Profile (m * A.k) where
  r := A.powerRows m
  g _ := A.c
  r_pos i := by have := A.powerRows_above_gap m i; omega
  g_lt_castSucc j := A.powerRows_above_gap m j.castSucc
  g_lt_succ j := A.powerRows_above_gap m j.succ

/-- Every nonexterior repeated-power row separates the two incident internal overlap strips. -/
theorem power_interior_bound (m : ℕ) (hm : 0 < m) (i : Fin (m * A.k + 1))
    (hi : 0 < i.val) (hl : i.val < m * A.k) :
    max (2 * A.c) A.d < (A.power m hm).r i := by
  change max (2 * A.c) A.d < A.powerRows m i
  rw [powerRows, ite_eq_right (by omega), ite_eq_right (by omega)]
  split_ifs with hmod
  · exact A.merger_bound
  · exact A.interior_bound _ (by change 0 < i.val % A.k; omega) (Nat.mod_lt _ A.k_pos)

/-- Every actual positive repeated power is Hessenberg, without any rigidity premise. -/
theorem power_thick (m : ℕ) (hm : 0 < m) : Staircase.Thick (A.power m hm) := by
  intro j l hjl
  have he := congrArg Fin.val hjl
  simp only [Fin.val_succ, Fin.val_castSucc] at he
  have hbound := A.power_interior_bound m hm j.succ (by simp)
    (by have := l.isLt; simp only [Fin.val_succ]; omega)
  change A.c + A.c < (A.power m hm).r j.succ
  omega

/-- The first row of every positive power is the original first endpoint. -/
theorem power_first (m : ℕ) (hm : 0 < m) : (A.power m hm).r 0 = A.r 0 := rfl

/-- The last row of every positive power is the original last endpoint. -/
theorem power_last (m : ℕ) (hm : 0 < m) :
    (A.power m hm).r (Fin.last (m * A.k)) = A.r (Fin.last A.k) := by
  have hmk : 0 < m * A.k := Nat.mul_pos hm A.k_pos
  simp only [power, powerRows, Fin.val_last, ite_eq_right (ne_of_gt hmk), ite_true]

/-- Every source row exceeds the larger joining seam, even when the inner gap is zero. -/
theorem power_rows_above_seam (m : ℕ) (hm : 0 < m) (i : Fin (m * A.k + 1)) :
    A.d < (A.power m hm).r i := by
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    rw [he, A.power_first]
    have := A.first_bound
    omega
  · by_cases hl : i.val = m * A.k
    · have he : i = Fin.last (m * A.k) := Fin.ext hl
      rw [he, A.power_last]
      have := A.last_bound
      omega
    · have hh := A.power_interior_bound m hm i (by omega) (by have := i.isLt; omega)
      omega

/-- The full maximal cofactor is exactly the constant-gap power, including `c = 0`. -/
theorem power_cofactor (m : ℕ) (hm : 0 < m) :
    (A.power m hm).toBetaDiagram.cornerPolynomial = complete A.c ^ (m * A.k) := by
  rw [Staircase.cornerPolynomial_eq_gapMonomial (A.power_thick m hm)]
  simp only [Staircase.gapMonomial, power, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The literal one-copy power recovers every original row without a rigidity assumption. -/
theorem power_one_rows (i : Fin (A.k + 1)) :
    A.powerRows 1 ⟨i.val, by have := i.isLt; omega⟩ = A.r i := by
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    rfl
  · by_cases hl : i.val = A.k
    · have he : i = Fin.last A.k := Fin.ext hl
      subst i
      simp only [powerRows, Nat.one_mul, Fin.val_last, ite_eq_right (ne_of_gt A.k_pos),
        ite_true]
    · have hlt : i.val < A.k := by have := i.isLt; omega
      simp only [powerRows, Nat.one_mul, hi, hl, ite_false, Nat.mod_eq_of_lt hlt]

/-- The complete actual one-copy row word is the original inner row word. -/
theorem power_one_word :
    List.ofFn (A.power 1 (by decide)).r = List.ofFn A.r := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, Nat.one_mul]
  · intro i hi hj
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact A.power_one_rows ⟨i, by simpa only [List.length_ofFn] using hj⟩

/-- One-copy deflation is exactly subtraction from every original inner row. -/
theorem power_one_deflated_word :
    List.ofFn (fun i => (A.power 1 (by decide)).r i - A.c) =
      List.ofFn (fun i => A.r i - A.c) := by
  have hh := congrArg (List.map (fun x : ℕ => x - A.c)) A.power_one_word
  simpa only [List.map_ofFn, Function.comp_def] using hh

end SaturationInner
end SkewClassInflation
