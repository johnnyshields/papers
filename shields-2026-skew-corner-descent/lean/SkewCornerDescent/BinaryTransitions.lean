/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicWindows

/-!
# Binary cyclic curvature

Supports `shields-2026-skew-corner-descent.tex`, «From response functions to literal copies»
(`sec:one-active`, `thm:pure-primitive-first`). The binary transition counts are even,
and the coprime weighted difference cannot vanish for a nonconstant period word.
These are the combinatorial numerator facts, not a replacement for the actual
first-normal coefficient or literal connector reconstruction. Sorry-free.
-/

namespace SkewCornerDescent.BinaryTransitions

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The number of false-to-true edges, counting every cyclic start. -/
def upCount (f : G → Bool) (step : G) : ℕ :=
  ∑ i, if f i = false ∧ f (i + step) = true then 1 else 0

/-- The number of true-to-false edges, counting every cyclic start. -/
def downCount (f : G → Bool) (step : G) : ℕ :=
  ∑ i, if f i = true ∧ f (i + step) = false then 1 else 0

/-- Binary squared curvature is the count of edges whose two values differ. -/
def transitionCount (f : G → Bool) (step : G) : ℕ :=
  ∑ i, if f i ≠ f (i + step) then 1 else 0

/-- Every upward crossing on a cycle is balanced by a downward crossing. -/
theorem upCount_eq_downCount (f : G → Bool) (step : G) :
    upCount f step = downCount f step := by
  classical
  let χ : G → ℤ := fun i => if f i then 1 else 0
  have he : (∑ i, χ (i + step)) = ∑ i, χ i :=
    Equiv.sum_comp (Equiv.addRight step) χ
  have hs : ∑ i, (χ (i + step) - χ i) = 0 := by
    rw [Finset.sum_sub_distrib, he, sub_self]
  have hp (i : G) : χ (i + step) - χ i =
      (if f i = false ∧ f (i + step) = true then (1 : ℤ) else 0) -
        (if f i = true ∧ f (i + step) = false then (1 : ℤ) else 0) := by
    cases hf : f i <;> cases hg : f (i + step) <;> simp [χ, hf, hg]
  simp_rw [hp] at hs
  rw [Finset.sum_sub_distrib, sub_eq_zero] at hs
  exact_mod_cast hs

/-- Each changing edge has exactly one of the two orientations. -/
theorem transitionCount_eq_sum (f : G → Bool) (step : G) :
    transitionCount f step = upCount f step + downCount f step := by
  classical
  unfold transitionCount upCount downCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases f i <;> cases f (i + step) <;> simp

/-- Binary cyclic curvature is even, independently of the number of positions. -/
theorem transitionCount_even (f : G → Bool) (step : G) :
    Even (transitionCount f step) := by
  rw [transitionCount_eq_sum, ← upCount_eq_downCount]
  exact ⟨upCount f step, rfl⟩

/-- At most one transition is counted at each start. -/
theorem transitionCount_le_card (f : G → Bool) (step : G) :
    transitionCount f step ≤ Fintype.card G := by
  unfold transitionCount
  calc
    (∑ i, if f i ≠ f (i + step) then 1 else 0) ≤ ∑ _ : G, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      split <;> omega
    _ = Fintype.card G := by simp

/-- The coprime curvature obstruction used in the cleared first-normal numerator. -/
theorem weighted_transition_ne_zero {b d TP TQ : ℕ} (hcop : Nat.Coprime b d)
    (hTP : 0 < TP) (hle : TP ≤ d) (heP : Even TP) (heQ : Even TQ) :
    (b : ℤ) * TP - (d : ℤ) * TQ ≠ 0 := by
  intro hz
  have he : b * TP = d * TQ := by exact_mod_cast (sub_eq_zero.mp hz)
  have hd : d ∣ TP := hcop.symm.dvd_of_dvd_mul_left (he ▸ Nat.dvd_mul_right d TQ)
  have hTd : TP = d := Nat.eq_of_dvd_of_lt_two_mul (Nat.ne_of_gt hTP) hd (by omega)
  have hd0 : d ≠ 0 := by omega
  have hQb : TQ = b := by
    rw [hTd, mul_comm b d] at he
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) he).symm
  have hd2 : 2 ∣ d := by simpa [hTd] using even_iff_two_dvd.mp heP
  have hb2 : 2 ∣ b := by simpa [hQb] using even_iff_two_dvd.mp heQ
  have : 2 ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hb2 hd2
  omega

/-- Zero curvature on a genuine cycle forces the entire binary word to be constant. -/
theorem zmod_constant_of_transitionCount_eq_zero {n : ℕ} [NeZero n]
    (f : ZMod n → Bool) (hz : transitionCount f 1 = 0) :
    ∀ i, f i = f 0 := by
  classical
  have he : ∀ i, f i = f (i + 1) := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (i : ZMod n) (_ : i ∈ Finset.univ) => Nat.zero_le
        (if f i ≠ f (i + 1) then 1 else 0))).mp hz
    intro i
    have h := hs i (Finset.mem_univ i)
    by_contra hne
    split_ifs at h with hh
  have hnat (k : ℕ) : f (k : ZMod n) = f 0 := by
    induction k with
    | zero => simp only [Nat.cast_zero]
    | succ k ih =>
      rw [Nat.cast_succ, ← he, ih]
  intro i
  simpa only [ZMod.natCast_zmod_val] using hnat i.val

/-- The nonconstant binary period word has positive curvature. -/
theorem zmod_transitionCount_pos {n : ℕ} [NeZero n] (f : ZMod n → Bool)
    (h : ∃ i j, f i ≠ f j) : 0 < transitionCount f 1 := by
  by_contra hz
  have hc := zmod_constant_of_transitionCount_eq_zero f (by omega)
  obtain ⟨i, j, hij⟩ := h
  exact hij ((hc i).trans (hc j).symm)

/-- The pure binary curvature numerator cannot vanish on a nonconstant period word.
All count and parity premises are supplied from the actual two cyclic words. -/
theorem cyclic_curvature_ne_zero {b d : ℕ} [NeZero b] [NeZero d]
    (hcop : Nat.Coprime b d) (P : ZMod d → Bool) (Q : ZMod b → Bool)
    (hP : ∃ i j, P i ≠ P j) :
    (b : ℤ) * transitionCount P 1 - (d : ℤ) * transitionCount Q 1 ≠ 0 := by
  apply weighted_transition_ne_zero hcop (zmod_transitionCount_pos P hP)
  · simpa only [ZMod.card] using transitionCount_le_card P 1
  · exact transitionCount_even P 1
  · exact transitionCount_even Q 1

/-- A nonconstant completed word also excludes zero pure curvature when
the period word is constant; no prescribed endpoint bit is needed. -/
theorem cyclic_curvature_ne_zero_of_nonconstant_closure {b d : ℕ} [NeZero b] [NeZero d]
    (hcop : Nat.Coprime b d) (P : ZMod d → Bool) (Q : ZMod b → Bool)
    (hQ : ∃ i j, Q i ≠ Q j) :
    (b : ℤ) * transitionCount P 1 - (d : ℤ) * transitionCount Q 1 ≠ 0 := by
  classical
  by_cases hP : ∃ i j, P i ≠ P j
  · exact cyclic_curvature_ne_zero hcop P Q hP
  have hall (i : ZMod d) : P i = P 0 := by
    by_contra hn
    exact hP ⟨i, 0, hn⟩
  have hTP : transitionCount P 1 = 0 := by
    unfold transitionCount
    apply Finset.sum_eq_zero
    intro i _
    have he : P i = P (i+1) := (hall i).trans (hall (i+1)).symm
    exact ite_eq_right (fun hn => hn he)
  have hTQ := zmod_transitionCount_pos Q hQ
  rw [hTP, Nat.cast_zero, mul_zero, zero_sub, neg_ne_zero]
  apply mul_ne_zero
  · exact_mod_cast NeZero.ne d
  · exact_mod_cast ne_of_gt hTQ

end SkewCornerDescent.BinaryTransitions
