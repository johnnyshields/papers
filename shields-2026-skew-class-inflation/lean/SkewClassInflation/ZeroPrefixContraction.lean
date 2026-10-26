/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroContractionBoundaries
import SkewClassInflation.JoinBetaSets

/-!
# Total zero contraction behind a fixed zero-free prefix

The positional peeling mechanism used in `thm:two-row-thin-class` of
`shields-2026-skew-class-inflation.tex`.  Full beta cancellation commutes
with placing an unchanged zero-free prefix in front of the remaining
context, with the joining endpoints merged.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Staircase SkewJacobiNegative.GeneralHessenberg

/-- Every full row beta is positive and lies below the normalized full span. -/
theorem profile_rowSet_bounds {n : ℕ} (P : Profile n) {x : ℤ}
    (hx : x ∈ P.toBetaDiagram.rowSet) : 0 < x ∧ x ≤ P.xi 0 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨P.xi_pos i, P.xi_strictAnti.antitone (Fin.zero_le i)⟩

/-- Every full column beta lies between zero and strictly below that same span. -/
theorem profile_colSet_bounds {n : ℕ} (P : Profile n) {x : ℤ}
    (hx : x ∈ P.toBetaDiagram.colSet) : 0 ≤ x ∧ x < P.xi 0 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  change 0 ≤ P.zeta i ∧ P.zeta i < P.xi 0
  have h := P.zeta_strictAnti.antitone (Fin.zero_le i)
  have hr := P.xi_sub_zeta 0
  have hp := P.r_pos 0
  exact ⟨P.zeta_nonneg i, by omega⟩

/-- The normalized terminal zero is retained as an actual full column coordinate. -/
theorem profile_zero_mem_colSet {n : ℕ} (P : Profile n) : 0 ∈ P.toBetaDiagram.colSet := by
  exact Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, P.zeta_last⟩

/-- Exact full beta supports determine the actual determinant across arbitrary finite orders. -/
theorem schur_eq_of_full_sets {n m : ℕ} (D : BetaDiagram n) (E : BetaDiagram m)
    (hr : D.rowSet = E.rowSet) (hc : D.colSet = E.colSet) : D.schur = E.schur := by
  have hn := congrArg Finset.card hr
  rw [BetaDiagram.rowSet_card, BetaDiagram.rowSet_card] at hn
  subst m
  exact congrArg BetaDiagram.schur (BetaDiagram.ext_sets D E hr hc)

/-- Cancelling the one touching span point separates the two residual supports. -/
theorem touching_span_differences (AX AY RX RY : Finset ℤ) (s : ℤ)
    (hA : Disjoint AX AY) (hAX : ∀ x ∈ AX, s < x) (hAY : ∀ x ∈ AY, s ≤ x)
    (hRX : ∀ x ∈ RX, x ≤ s) (hRY : ∀ x ∈ RY, x < s)
    (hsA : s ∈ AY) (hsR : s ∈ RX) :
    (AX ∪ RX) \ (AY ∪ RY) = AX ∪ (RX \ RY).erase s ∧
      (AY ∪ RY) \ (AX ∪ RX) = AY.erase s ∪ (RY \ RX) := by
  classical
  constructor
  · ext x
    rcases lt_trichotomy x s with hx | he | hx
    · have hax : x ∉ AX := fun h => (not_lt_of_ge (hAX x h).le) hx
      have hay : x ∉ AY := fun h => (not_lt_of_ge (hAY x h)) hx
      simp [Finset.mem_sdiff, hax, hay, ne_of_lt hx]
    · subst x
      have hax : s ∉ AX := fun h => (lt_irrefl s) (hAX s h)
      simp [Finset.mem_sdiff, hax, hsA]
    · have hrx : x ∉ RX := fun h => (not_lt_of_ge (hRX x h)) hx
      have hry : x ∉ RY := fun h => (not_lt_of_ge (hRY x h).le) hx
      by_cases hax : x ∈ AX
      · have hay : x ∉ AY := Finset.disjoint_left.mp hA hax
        simp [Finset.mem_sdiff, hrx, hry, hax, hay]
      · simp [Finset.mem_sdiff, hrx, hry, hax]
  · ext x
    rcases lt_trichotomy x s with hx | he | hx
    · have hax : x ∉ AX := fun h => (not_lt_of_ge (hAX x h).le) hx
      have hay : x ∉ AY := fun h => (not_lt_of_ge (hAY x h)) hx
      simp [Finset.mem_sdiff, hax, hay]
    · subst x
      have hry : s ∉ RY := fun h => (lt_irrefl s) (hRY s h)
      simp [Finset.mem_sdiff, hsR, hry]
    · have hrx : x ∉ RX := fun h => (not_lt_of_ge (hRX x h)) hx
      have hry : x ∉ RY := fun h => (not_lt_of_ge (hRY x h).le) hx
      by_cases hay : x ∈ AY
      · have hax : x ∉ AX := Finset.disjoint_left.mp hA.symm hay
        simp [Finset.mem_sdiff, hrx, hry, hay, hax, ne_of_gt hx]
      · simp [Finset.mem_sdiff, hrx, hry, hay]

/-- A zero merger erases precisely the touching upper span coordinate. -/
theorem zero_merge_rowSet {n m : ℕ} (A : Profile n) (R : Profile m) :
    (Profile.merge A R 0 (A.r_pos _) (R.r_pos _)).toBetaDiagram.rowSet =
      (A.toBetaDiagram.rowSet.image (fun x => x + R.xi 0) ∪
        R.toBetaDiagram.rowSet).erase (R.xi 0) := by
  have hdel : (Profile.zeroJoin A R).xi (⟨n, by omega⟩ : Fin (n + m + 1)).succ = R.xi 0 := by
    change (Profile.join A R 0 (A.r_pos _) (R.r_pos _)).xi ⟨n + 1, by omega⟩ = R.xi 0
    simpa only [Fin.val_zero, Nat.add_zero] using
      Profile.join_xi_right A R 0 (A.r_pos _) (R.r_pos _) (0 : Fin (m + 1))
  unfold Profile.zeroJoin at hdel
  rw [Profile.merge, contract_rowSet, hdel, Profile.join_rowSet]
  simp only [Nat.cast_zero, sub_zero]

/-- The same zero merger erases exactly the touching lower span coordinate. -/
theorem zero_merge_colSet {n m : ℕ} (A : Profile n) (R : Profile m) :
    (Profile.merge A R 0 (A.r_pos _) (R.r_pos _)).toBetaDiagram.colSet =
      (A.toBetaDiagram.colSet.image (fun x => x + R.xi 0) ∪
        R.toBetaDiagram.colSet).erase (R.xi 0) := by
  have hdel : (Profile.zeroJoin A R).zeta (⟨n, by omega⟩ : Fin (n + m + 1)).castSucc = R.xi 0 := by
    change (Profile.join A R 0 (A.r_pos _) (R.r_pos _)).zeta ⟨n, by omega⟩ = R.xi 0
    have h := Profile.join_zeta_left A R 0 (A.r_pos _) (R.r_pos _) (Fin.last n)
    simpa only [Fin.val_last, A.zeta_last, zero_add, Nat.cast_zero, sub_zero] using h
  unfold Profile.zeroJoin at hdel
  rw [Profile.merge, contract_colSet, hdel, Profile.join_colSet]
  simp only [Nat.cast_zero, sub_zero]

/-- A fixed zero-free prefix can be merged after the remaining context has been fully contracted. -/
theorem zero_prefix_contraction {n m : ℕ} (A : Profile n) (R : Profile m)
    (hA : Thick A) (hR : Thick R) (hzA : A.toBetaDiagram.ZeroFree) :
    (contractAllZeros (Profile.zeroJoin A R)).2.toBetaDiagram.schur =
      (Profile.merge A (contractAllZeros R).2 0 (A.r_pos _)
        ((contractAllZeros R).2.r_pos _)).toBetaDiagram.schur := by
  classical
  let C := (contractAllZeros R).2
  let AX := A.toBetaDiagram.rowSet.image (fun x => x + R.xi 0)
  let AY := A.toBetaDiagram.colSet.image (fun x => x + R.xi 0)
  have hAX : ∀ x ∈ AX, R.xi 0 < x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have h := profile_rowSet_bounds A hy
    omega
  have hAY : ∀ x ∈ AY, R.xi 0 ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have h := profile_colSet_bounds A hy
    omega
  have hdis : Disjoint AX AY := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hby⟩ := Finset.mem_image.mp hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    change A.xi i = a at hi
    change A.zeta j = b at hj
    apply hzA i j
    change A.xi i = A.zeta j
    omega
  have hsA : R.xi 0 ∈ AY := Finset.mem_image.mpr
    ⟨0, profile_zero_mem_colSet A, by simp⟩
  have hsR : R.xi 0 ∈ R.toBetaDiagram.rowSet :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hsets := touching_span_differences AX AY R.toBetaDiagram.rowSet R.toBetaDiagram.colSet
    (R.xi 0) hdis hAX hAY (fun _ h => (profile_rowSet_bounds R h).2)
    (fun _ h => (profile_colSet_bounds R h).2) hsA hsR
  have hJ := contractAllZeros_sets (Profile.zeroJoin A R) (Profile.zeroJoin_thick A R hA hR)
  have hC := contractAllZeros_sets R hR
  have hspan := contractAllZeros_span R hR
  have hnAX : R.xi 0 ∉ AX := fun h => (lt_irrefl _) (hAX _ h)
  have hnC : R.xi 0 ∉ C.toBetaDiagram.colSet := by
    intro h
    have hh := (profile_colSet_bounds C h).2
    rw [hspan] at hh
    exact (lt_irrefl _) hh
  apply schur_eq_of_full_sets
  · rw [hJ.1, Profile.zeroJoin, Profile.join_rowSet, Profile.join_colSet]
    simp only [Nat.cast_zero, sub_zero]
    rw [hsets.1, ← hC.1, zero_merge_rowSet, hspan]
    change AX ∪ C.toBetaDiagram.rowSet.erase (R.xi 0) =
      (AX ∪ C.toBetaDiagram.rowSet).erase (R.xi 0)
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnAX]
  · rw [hJ.2, Profile.zeroJoin, Profile.join_colSet, Profile.join_rowSet]
    simp only [Nat.cast_zero, sub_zero]
    rw [hsets.2, ← hC.2, zero_merge_colSet, hspan]
    change AY.erase (R.xi 0) ∪ C.toBetaDiagram.colSet =
      (AY ∪ C.toBetaDiagram.colSet).erase (R.xi 0)
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnC]

end SkewClassInflation
