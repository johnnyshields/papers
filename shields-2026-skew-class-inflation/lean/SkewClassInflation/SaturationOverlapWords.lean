/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.OverlapWords
import SkewClassInflation.SaturationPowerMerge
import SkewClassInflation.SaturationRibbonReduction

/-!
# The actual deflated power is the literal overlap word

The word bridge in `lem:merged-block-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Deflating each row by the
original constant gap changes the endpoint overlap to the positive
difference between the large and small seams.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

private theorem ofFn_replace_zero {k : ℕ} (hk : 0 < k) (r : Fin k → ℕ) (b : ℕ) :
    List.ofFn (fun i => if i.val = 0 then b else r i) = b :: (List.ofFn r).tail := by
  cases k with
  | zero => omega
  | succ k =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [Fin.val_zero, ite_true, List.tail_cons]
    congr 1

private theorem append_value {n m : ℕ} (u : Fin n → ℕ) (v : Fin m → ℕ)
    (i : Fin (n + m)) :
    Fin.append u v i = if h : i.val < n then u ⟨i.val, h⟩
      else v ⟨i.val - n, by have := i.isLt; omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, Fin.val_castAdd, dite_eq_left j.isLt]
  · rw [Fin.append_right, dite_eq_right (by simp only [Fin.val_natAdd]; omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.val_natAdd, Nat.add_sub_cancel_left]

namespace SaturationInner

variable (A : SaturationInner)

/-- The actual one-copy deflated prefix, excluding only the last endpoint. -/
def ribbonFirstBlock (i : Fin A.k) : ℕ := A.r i.castSucc - A.c

/-- A further overlapped copy replaces exactly the first endpoint in that prefix. -/
def ribbonRepeatBlock (i : Fin A.k) : ℕ :=
  if i.val = 0 then A.merger - A.c else A.ribbonFirstBlock i

/-- The original first endpoint followed by the actual interior row word. -/
theorem ribbonFirstBlock_word :
    List.ofFn A.ribbonFirstBlock =
      (A.r 0 - A.c) :: (List.ofFn A.ribbonFirstBlock).tail := by
  have hn : List.ofFn A.ribbonFirstBlock ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hh
    have := A.k_pos
    omega
  have hh := List.cons_head_tail hn
  rw [List.head_ofFn] at hh
  exact hh.symm

/-- Every displayed interior part remains positive after deflation. -/
theorem ribbon_middle_positive :
    ∀ a ∈ (List.ofFn A.ribbonFirstBlock).tail, 0 < a := by
  intro a ha
  have hm := List.mem_of_mem_tail ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  exact Nat.sub_pos_of_lt (A.row_above_gap i.castSucc)

/-- The paper's exact overlap word associated with an arbitrary admissible inner. -/
def overlapWord : OverlapWord where
  first := A.r 0 - A.c
  last := A.r (Fin.last A.k) - A.c
  middle := (List.ofFn A.ribbonFirstBlock).tail
  delta := A.d - A.c
  delta_pos := Nat.sub_pos_of_lt A.c_lt_d
  first_bound := by have := A.first_bound; have := A.c_lt_d; omega
  last_bound := by have := A.last_bound; have := A.c_lt_d; omega
  middle_pos := A.ribbon_middle_positive

/-- Deflation changes the old endpoint merger by exactly the same constant gap. -/
theorem overlapWord_merged : A.overlapWord.merged = A.merger - A.c := by
  have ha := A.first_bound
  have hb := A.last_bound
  have hc := A.c_lt_d
  dsimp only [OverlapWord.merged, overlapWord, merger]
  omega

/-- Each repeat block is the same original interior word with its actual merged endpoint. -/
theorem ribbonRepeatBlock_word : List.ofFn A.ribbonRepeatBlock =
    A.overlapWord.merged :: A.overlapWord.middle := by
  change List.ofFn (fun i => if i.val = 0 then A.merger - A.c else A.ribbonFirstBlock i) = _
  rw [ofFn_replace_zero A.k_pos, ← A.overlapWord_merged]
  rfl

/-- The actual deflated row vector splits into its first block, repeats, and last endpoint. -/
theorem power_deflated_blocks (m : ℕ) :
    List.ofFn (fun i => (A.power (m + 1) (by omega)).r i - A.c) =
      List.ofFn A.ribbonFirstBlock ++
        (List.replicate m (List.ofFn A.ribbonRepeatBlock)).flatten ++
          [A.r (Fin.last A.k) - A.c] := by
  let f : Fin (A.k + m * A.k + 1) → ℕ :=
    Fin.append (Fin.append A.ribbonFirstBlock (Fin.repeat m A.ribbonRepeatBlock))
      (fun _ : Fin 1 => A.r (Fin.last A.k) - A.c)
  have he : List.ofFn (fun i => (A.power (m + 1) (by omega)).r i - A.c) =
      List.ofFn f := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]
      ring
    · intro i hi hj
      rw [List.getElem_ofFn, List.getElem_ofFn]
      simp only [f, append_value]
      split_ifs with hlast hfirst
      · change A.powerRows (m + 1) ⟨i, _⟩ - A.c = A.ribbonFirstBlock _
        have hiK : i < A.k := hfirst
        have hiM : i ≠ (m + 1) * A.k := by nlinarith [A.k_pos]
        rw [powerRows, ite_eq_right hiM]
        by_cases hi0 : i = 0
        · subst i
          simp only [ite_true, ribbonFirstBlock]
          rfl
        · rw [ite_eq_right hi0, ite_eq_right (by
            rw [Nat.mod_eq_of_lt hiK]
            exact hi0)]
          simp only [ribbonFirstBlock, Nat.mod_eq_of_lt hiK]
          rfl
      · change A.powerRows (m + 1) ⟨i, _⟩ - A.c =
          A.ribbonRepeatBlock ⟨(i - A.k) % A.k, Nat.mod_lt _ A.k_pos⟩
        have hi0 : i ≠ 0 := by have := A.k_pos; omega
        have hiM : i ≠ (m + 1) * A.k := by nlinarith
        have hmod : (i - A.k) % A.k = i % A.k := by
          have hi : i = A.k + (i - A.k) := by omega
          conv_rhs => rw [hi]
          simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
        simp only [powerRows, ite_eq_right hi0, ite_eq_right hiM,
          ribbonRepeatBlock, hmod]
        split_ifs
        · rfl
        · simp only [ribbonFirstBlock]
          rfl
      · have hiLast : i = (m + 1) * A.k := by
          simp only [List.length_ofFn] at hi hj
          nlinarith
        subst i
        change A.powerRows (m + 1) ⟨(m + 1) * A.k, _⟩ - A.c = _
        rw [powerRows, ite_eq_right (by nlinarith [A.k_pos])]
        simp only [ite_true]
  rw [he]
  change List.ofFn (Fin.append
    (Fin.append A.ribbonFirstBlock (Fin.repeat m A.ribbonRepeatBlock))
      (fun _ : Fin 1 => A.r (Fin.last A.k) - A.c)) = _
  rw [List.ofFn_fin_append, List.ofFn_fin_append, List.ofFn_fin_repeat]
  rfl

/-- All rows of every actual positive power are the displayed endpoint-merging word. -/
theorem power_deflated_word (m : ℕ) :
    List.ofFn (fun i => (A.power (m + 1) (by omega)).r i - A.c) =
      (A.overlapWord.composition m).blocks := by
  rw [A.power_deflated_blocks, A.ribbonFirstBlock_word, A.ribbonRepeatBlock_word]
  rfl

/-- The actual deflated power, as a positive composition of its own full row weight. -/
def powerRibbonComposition (m : ℕ) (hm : 0 < m) :
    Composition (List.ofFn (fun i => (A.power m hm).r i - A.c)).sum where
  blocks := List.ofFn (fun i => (A.power m hm).r i - A.c)
  blocks_pos := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Nat.sub_pos_of_lt (A.powerRows_above_gap m i)
  blocks_sum := rfl

/-- The full composition and its weight, not only its Schur function, match the overlap word. -/
theorem powerRibbonComposition_eq_overlap (m : ℕ) :
    (⟨_, A.powerRibbonComposition (m + 1) (by omega)⟩ : (N : ℕ) × Composition N) =
      ⟨(m + 1) * A.overlapWord.period + A.overlapWord.delta,
        A.overlapWord.composition m⟩ := by
  apply Composition.sigma_eq_iff_blocks_eq.mpr
  exact A.power_deflated_word m

/-- Every actual deflated power of at least two copies excludes multipart cut-product factors. -/
theorem powerRibbonComposition_no_right_factor (m : ℕ) (hm : 2 ≤ m)
    {n q : ℕ} (γ : Composition n) (β : Composition q)
    (hγ : 2 ≤ n) (hβ : 2 ≤ β.length) :
    (⟨n * q, compositionProduct γ β⟩ : (N : ℕ) × Composition N) ≠
      ⟨_, A.powerRibbonComposition m (by omega)⟩ := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  rw [A.powerRibbonComposition_eq_overlap]
  exact A.overlapWord.no_right_factor a (by omega) γ β hγ hβ

/-- An arbitrary full power mate supplies actual ribbon equality to that same overlap word. -/
theorem power_mate_overlap_ribbon (m : ℕ) {n : ℕ} (Q : Profile n)
    (he : Q.toBetaDiagram.schur =
      (A.power (m + 1) (by omega)).toBetaDiagram.schur) :
    ribbonWord (List.ofFn (fun i => Q.r i - A.c)) =
      ribbonWord (A.overlapWord.composition m).blocks := by
  have hh := A.power_mate_ribbon (m + 1) (by omega) Q he
  rw [A.power_deflated_word] at hh
  exact hh

end SaturationInner
end SkewClassInflation
