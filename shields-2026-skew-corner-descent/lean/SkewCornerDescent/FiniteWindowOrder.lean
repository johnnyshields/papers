/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Hom.Set

/-!
# Ranks in complete initial and final windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
An ordered end-window inventory has no missing ranks: its cardinality determines its
complete initial or final segment, including the empty-window boundary. Sorry-free.
-/

namespace SkewCornerDescent

/-- A complete final segment occupies precisely the last ranks, with multiplicity. -/
theorem fin_upper_window_ranks {B : ℕ} (p : Fin B → Prop) [DecidablePred p]
    (hup : ∀ i j, i ≤ j → p i → p j) (i : Fin B) :
    p i ↔ B - (Finset.univ.filter p).card ≤ i.val := by
  classical
  let S := Finset.univ.filter p
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    have ha : p a := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    have hmem (j : Fin B) : p j ↔ a ≤ j := by
      constructor
      · intro hj
        exact Finset.min'_le S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      · intro hj
        exact hup a j hj ha
    have hEq : S = Finset.Ici a := by
      ext j
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Ici, hmem]
    have hcard : S.card = B - a.val := by rw [hEq, Fin.card_Ici]
    rw [hmem]
    change a.val ≤ i.val ↔ B - S.card ≤ i.val
    rw [hcard]
    have := a.isLt
    omega
  · have hEq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hp : ¬ p i := by
      intro hi
      have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hEq] at hm
      exact Finset.notMem_empty _ hm
    change p i ↔ B - S.card ≤ i.val
    rw [hEq, Finset.card_empty, Nat.sub_zero]
    simp only [hp, false_iff]
    have := i.isLt
    omega

/-- A complete initial segment occupies precisely the first ranks. -/
theorem fin_lower_window_ranks {B : ℕ} (p : Fin B → Prop) [DecidablePred p]
    (hdown : ∀ i j, i ≤ j → p j → p i) (i : Fin B) :
    p i ↔ i.val < (Finset.univ.filter p).card := by
  classical
  let S := Finset.univ.filter p
  by_cases hS : S.Nonempty
  · let a := S.max' hS
    have ha : p a := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
    have hmem (j : Fin B) : p j ↔ j ≤ a := by
      constructor
      · intro hj
        exact Finset.le_max' S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      · intro hj
        exact hdown j a hj ha
    have hEq : S = Finset.Iic a := by
      ext j
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Iic, hmem]
    have hcard : S.card = a.val + 1 := by rw [hEq, Fin.card_Iic]
    rw [hmem]
    change i.val ≤ a.val ↔ i.val < S.card
    rw [hcard]
    omega
  · have hEq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hp : ¬ p i := by
      intro hi
      have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hEq] at hm
      exact Finset.notMem_empty _ hm
    change p i ↔ i.val < S.card
    rw [hEq, Finset.card_empty]
    simp only [hp, Nat.not_lt_zero, iff_self]

/-- An order isomorphism from a final window to an initial window is the exact rank
shift by the number of source occurrences outside the window. -/
theorem fin_end_windows_orderIso_rank {B : ℕ} (p q : Fin B → Prop)
    [DecidablePred p]
    (hup : ∀ i j, i ≤ j → p i → p j)
    (hdown : ∀ i j, i ≤ j → q j → q i)
    (e : {i // p i} ≃o {i // q i}) (b : {i // p i}) :
    (e b).val.val + (B - (Finset.univ.filter p).card) = b.val.val := by
  classical
  let C := (Finset.univ.filter p).card
  have hC : C ≤ B := (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ,
    Fintype.card_fin])
  have hcard : (Finset.univ.filter q).card = C := by
    have he := Fintype.card_congr e.toEquiv
    simpa only [Fintype.card_subtype, C] using he.symm
  have hp (i : Fin B) : p i ↔ B - C ≤ i.val := fin_upper_window_ranks p hup i
  have hq (i : Fin B) : q i ↔ i.val < C := by
    rw [fin_lower_window_ranks q hdown i, hcard]
  let f : {i // p i} ≃o {i // q i} :=
    { toFun := fun a => ⟨⟨a.val.val - (B - C), by
        have ha := (hp a.val).mp a.property
        have hb := a.val.isLt
        omega⟩, by
          apply (hq _).mpr
          have ha := (hp a.val).mp a.property
          have hb := a.val.isLt
          dsimp only
          omega⟩
      invFun := fun a => ⟨⟨a.val.val + (B - C), by
        have ha := (hq a.val).mp a.property
        omega⟩, by
          apply (hp _).mpr
          dsimp only
          omega⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Fin.ext
        have ha := (hp a.val).mp a.property
        dsimp only
        omega
      right_inv := by
        intro a
        apply Subtype.ext
        apply Fin.ext
        dsimp only
        omega
      map_rel_iff' := by
        intro a b
        change a.val.val - (B - C) ≤ b.val.val - (B - C) ↔ a.val.val ≤ b.val.val
        have ha := (hp a.val).mp a.property
        have hb := (hp b.val).mp b.property
        omega }
  have hef : e = f := Subsingleton.elim _ _
  rw [hef]
  change b.val.val - (B - C) + (B - C) = b.val.val
  exact Nat.sub_add_cancel ((hp b.val).mp b.property)

/-- An ordered enumeration of a complete initial window preserves every original rank. -/
theorem fin_initial_window_orderIso_rank {B C : ℕ} (p : Fin B → Prop)
    (hdown : ∀ i j, i ≤ j → p j → p i)
    (e : {i // p i} ≃o Fin C) (b : {i // p i}) : (e b).val = b.val.val := by
  classical
  have hcard : (Finset.univ.filter p).card = C := by
    have h := Fintype.card_congr e.toEquiv
    simpa only [Fintype.card_subtype, Fintype.card_fin] using h
  have hC : C ≤ B := by
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hp (i : Fin B) : p i ↔ i.val < C := by
    rw [fin_lower_window_ranks p hdown i, hcard]
  let f : {i // p i} ≃o Fin C :=
    { toFun := fun i => ⟨i.val.val, (hp i.val).mp i.property⟩
      invFun := fun i => ⟨⟨i.val, i.isLt.trans_le hC⟩, (hp _).mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hef : e = f := Subsingleton.elim _ _
  rw [hef]
  rfl

/-- An ordered enumeration of a complete final window removes exactly the omitted prefix. -/
theorem fin_final_window_orderIso_rank {B C : ℕ} (p : Fin B → Prop)
    (hup : ∀ i j, i ≤ j → p i → p j)
    (e : {i // p i} ≃o Fin C) (b : {i // p i}) :
    (e b).val + (B - C) = b.val.val := by
  classical
  have hcard : (Finset.univ.filter p).card = C := by
    have h := Fintype.card_congr e.toEquiv
    simpa only [Fintype.card_subtype, Fintype.card_fin] using h
  have hC : C ≤ B := by
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hp (i : Fin B) : p i ↔ B - C ≤ i.val := by
    rw [fin_upper_window_ranks p hup i, hcard]
  let f : {i // p i} ≃o Fin C :=
    { toFun := fun i => ⟨i.val.val - (B - C), by
        have hi := (hp i.val).mp i.property
        have hj := i.val.isLt
        omega⟩
      invFun := fun i => ⟨⟨i.val + (B - C), by omega⟩, by
        apply (hp _).mpr
        dsimp only
        omega⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        have hi := (hp i.val).mp i.property
        dsimp only
        omega
      right_inv := by
        intro i
        apply Fin.ext
        dsimp only
        omega
      map_rel_iff' := by
        intro i j
        change i.val.val - (B - C) ≤ j.val.val - (B - C) ↔ i.val.val ≤ j.val.val
        have hi := (hp i.val).mp i.property
        have hj := (hp j.val).mp j.property
        omega }
  have hef : e = f := Subsingleton.elim _ _
  rw [hef]
  change b.val.val - (B - C) + (B - C) = b.val.val
  exact Nat.sub_add_cancel ((hp b.val).mp b.property)

end SkewCornerDescent
