/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FourRowClasses
import SkewJacobiNegative.TwoComponentLift

/-!
# Unbounded low-negative pattern geometry

Actual source inequalities, maximal-cofactor inheritance and endpoint
preservation for `thm:two-negatives`, `thm:column`, `prop:three-corners`,
`thm:square` and `prop:hook` in
`shields-2026-skew-jacobi-negative.tex`.  A column pattern has no bound on
its area.  No pattern is imposed on a mate.
-/

namespace SkewJacobiNegative
namespace BetaDiagram
variable {n : ℕ}

/-- All genuinely negative entries lie in the first column. -/
def ColumnNegatives (D : BetaDiagram n) : Prop :=
  ∀ i j, D.row i < D.col j → j.val = 0

/-- The literal first alternative in `thm:column`, including weak equality. -/
theorem column_negatives_iff_last_row (D : BetaDiagram (n + 2)) :
    D.ColumnNegatives ↔ D.col 1 ≤ D.row (Fin.last (n + 1)) := by
  constructor
  · intro h
    by_contra hh
    have := h (Fin.last (n + 1)) 1 (lt_of_not_ge hh)
    norm_num at this
  · intro h i j hij
    by_contra hj
    have hc := D.col_strictAnti.antitone
      (show (1 : Fin (n + 2)) ≤ j by change 1 ≤ j.val; omega)
    have hr := D.row_strictAnti.antitone (Fin.le_last i)
    omega

/-- Half-turn changes a first-column pattern into the last-row pattern;
this is the second literal alternative in `thm:column`. -/
theorem rotate_column_negatives_iff_penultimate_row (D : BetaDiagram (n + 2)) :
    D.rotate.ColumnNegatives ↔ D.col 0 ≤ D.row (Fin.last n).castSucc := by
  rw [column_negatives_iff_last_row]
  change -D.row (1 : Fin (n + 2)).rev ≤ -D.col (Fin.last (n + 1)).rev ↔ _
  have h1 : (1 : Fin (n + 2)).rev = (Fin.last n).castSucc := by
    apply Fin.ext
    simp [Fin.val_rev]
  have h0 : (Fin.last (n + 1)).rev = 0 := by apply Fin.ext; simp
  rw [h1, h0]
  omega

/-- Faithful homogenization preserves the actual column pattern. -/
theorem gamma_column_negatives_iff (D : BetaDiagram n) :
    D.gamma.ColumnNegatives ↔ D.ColumnNegatives := by
  constructor <;> intro h i j hij
  · exact h i j ((D.gamma_negative_iff i j).mpr hij)
  · exact h i j ((D.gamma_negative_iff i j).mp hij)

/-- The child retains the full column pattern without a count bound. -/
theorem corner_column_negatives (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner)
    (h : D.ColumnNegatives) : (D.cornerDiagram hP).ColumnNegatives := by
  intro i j hij
  exact h i.succ j.castSucc hij

/-- Top endpoints remain in the same unbounded column class. -/
theorem extendTop_column_negatives (D : BetaDiagram (n + 1))
    (h : D.ColumnNegatives) (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).ColumnNegatives := by
  intro i j hij
  exact h i j ((D.extendTop_negative_iff t ht i j).mp hij)

/-- Bottom endpoints retain the same full column class. -/
theorem extendBottom_column_negatives (D : BetaDiagram (n + 1))
    (h : D.ColumnNegatives) (t : ℤ) (ht : 0 < t) :
    (D.extendBottom t ht).ColumnNegatives := by
  intro i j hij
  exact h i j ((D.extendBottom_negative_iff t ht i j).mp hij)

/-- Every possible component cut of a column board is its first cut. -/
theorem column_cut_first (D : BetaDiagram (n + 2)) (h : D.ColumnNegatives)
    (i : Fin (n + 2)) (hi : i.val + 1 < n + 2)
    (hcut : D.row ⟨i.val + 1, hi⟩ < D.col i) : i = 0 := by
  apply Fin.ext
  exact h _ _ hcut

/-- A disconnected column child has a genuine first singleton cut. -/
theorem column_disconnected_first_cut (D : BetaDiagram (n + 2))
    (h : D.ColumnNegatives) (hC : ¬ D.Connected) : D.row 1 < D.col 0 := by
  by_contra hc
  apply hC
  refine ⟨by omega, ?_⟩
  intro i hi
  by_contra hbad
  have hh : D.row ⟨i.val + 1, hi⟩ < D.col i := lt_of_not_ge hbad
  have hz := D.column_cut_first h i hi hh
  subst i
  exact hc hh

/-- Literal dense block after the first singleton in a column cofactor. -/
def columnCore (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner) :
    BetaDiagram (n + 1) := (D.cornerDiagram hP).tail

/-- Zero-freeness, not a silently strict source inequality, makes the actual
block after the first singleton dense. -/
theorem columnCore_dense (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner)
    (hZ : D.ZeroFree) (h : D.ColumnNegatives) : (D.columnCore hP).Dense := by
  intro i j
  change D.col j.succ.castSucc < D.row i.succ.succ
  have hz := hZ i.succ.succ j.succ.castSucc
  have hn : ¬ D.row i.succ.succ < D.col j.succ.castSucc := by
    intro hh
    have := h _ _ hh
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  omega

/-- Above four parent rows, the two-negative budget forces the actual child
connected.  The proof covers every row count, not a bounded inventory. -/
theorem two_negative_corner_connected (D : BetaDiagram (n + 5))
    (hP : D.PositiveCorner) (hcount : negativeCount D ≤ 2) :
    (D.cornerDiagram hP).Connected := by
  apply connected_of_negativeCount_small _ (by omega)
  rw [D.corner_negativeCount hP]
  omega

/-- Exact square mask, stated on the full board. -/
def SquareNegatives (D : BetaDiagram n) : Prop :=
  ∀ i j, D.row i < D.col j ↔ n - 2 ≤ i.val ∧ j.val < 2

/-- The hook before rotation, with weak source beta comparisons left intact. -/
def HookNegatives (D : BetaDiagram n) : Prop :=
  ∀ i j, D.row i < D.col j ↔
    (n - 3 ≤ i.val ∧ j.val = 0) ∨ (i.val + 1 = n ∧ j.val = 1)

/-- A square above five rows has no possible child subdiagonal cut. -/
theorem square_corner_connected (D : BetaDiagram (n + 6))
    (hP : D.PositiveCorner) (h : D.SquareNegatives) : (D.cornerDiagram hP).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  by_contra hc
  have hn : D.row (⟨i.val + 1, hi⟩ : Fin (n + 5)).succ < D.col i.castSucc :=
    lt_of_not_ge hc
  have hh := (h _ _).mp hn
  simp only [Fin.val_succ, Fin.val_castSucc] at hh
  omega

/-- The connected square child retains precisely the square, one order down. -/
theorem corner_square_negatives (D : BetaDiagram (n + 6)) (hP : D.PositiveCorner)
    (h : D.SquareNegatives) : (D.cornerDiagram hP).SquareNegatives := by
  intro i j
  change D.row i.succ < D.col j.castSucc ↔ _
  rw [h]
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

/-- A hook above five rows likewise has a connected actual child. -/
theorem hook_corner_connected (D : BetaDiagram (n + 6))
    (hP : D.PositiveCorner) (h : D.HookNegatives) : (D.cornerDiagram hP).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  by_contra hc
  have hn : D.row (⟨i.val + 1, hi⟩ : Fin (n + 5)).succ < D.col i.castSucc :=
    lt_of_not_ge hc
  have hh := (h _ _).mp hn
  simp only [Fin.val_succ, Fin.val_castSucc] at hh
  omega

/-- Hook inheritance is exact, including both parts of the final row. -/
theorem corner_hook_negatives (D : BetaDiagram (n + 6)) (hP : D.PositiveCorner)
    (h : D.HookNegatives) : (D.cornerDiagram hP).HookNegatives := by
  intro i j
  change D.row i.succ < D.col j.castSucc ↔ _
  rw [h]
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

/-- Positive endpoint shifts do not change the square mask. -/
theorem extendTop_square_negatives (D : BetaDiagram (n + 1))
    (h : D.SquareNegatives) (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).SquareNegatives := by
  intro i j
  rw [D.extendTop_negative_iff t ht i j]
  exact h i j

/-- The same statement for the other endpoint. -/
theorem extendBottom_square_negatives (D : BetaDiagram (n + 1))
    (h : D.SquareNegatives) (t : ℤ) (ht : 0 < t) :
    (D.extendBottom t ht).SquareNegatives := by
  intro i j
  rw [D.extendBottom_negative_iff t ht i j]
  exact h i j

/-- Positive top shifts preserve the hook mask. -/
theorem extendTop_hook_negatives (D : BetaDiagram (n + 1))
    (h : D.HookNegatives) (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).HookNegatives := by
  intro i j
  rw [D.extendTop_negative_iff t ht i j]
  exact h i j

/-- Positive bottom shifts preserve the hook mask. -/
theorem extendBottom_hook_negatives (D : BetaDiagram (n + 1))
    (h : D.HookNegatives) (t : ℤ) (ht : 0 < t) :
    (D.extendBottom t ht).HookNegatives := by
  intro i j
  rw [D.extendBottom_negative_iff t ht i j]
  exact h i j

/-- The three literal weak inequalities in `prop:three-corners`. -/
def ThreeCorners (D : BetaDiagram (n + 3)) : Prop :=
  D.col 0 ≤ D.row ⟨n, by omega⟩ ∧
  D.col 1 ≤ D.row ⟨n + 1, by omega⟩ ∧
  D.col 2 ≤ D.row (Fin.last (n + 2))

/-- The three-corner hypotheses force every maximal-cofactor subdiagonal
strictly positive, without making any source weak inequality strict. -/
theorem three_corners_corner_connected (D : BetaDiagram (n + 5))
    (hP : D.PositiveCorner) (h : D.ThreeCorners) : (D.cornerDiagram hP).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  change D.col i.castSucc ≤ D.row (⟨i.val + 1, hi⟩ : Fin (n + 4)).succ
  rcases h with ⟨h0, h1, h2⟩
  change D.col 1 ≤ D.row ⟨n + 3, by omega⟩ at h1
  change D.col 2 ≤ D.row (Fin.last (n + 4)) at h2
  by_cases hi0 : i.val = 0
  · have he : i.castSucc = (0 : Fin (n + 5)) := Fin.ext hi0
    rw [he]
    have hr := D.row_strictAnti.antitone
      (show (⟨i.val + 1, hi⟩ : Fin (n + 4)).succ ≤ ⟨n + 2, by omega⟩ by
        change i.val + 2 ≤ n + 2; omega)
    omega
  · by_cases hi1 : i.val = 1
    · have he : i.castSucc = (1 : Fin (n + 5)) := Fin.ext hi1
      rw [he]
      have hr := D.row_strictAnti.antitone
        (show (⟨i.val + 1, hi⟩ : Fin (n + 4)).succ ≤ ⟨n + 3, by omega⟩ by
          change i.val + 2 ≤ n + 3; omega)
      omega
    · have hc := D.col_strictAnti.antitone
        (show (2 : Fin (n + 5)) ≤ i.castSucc by change 2 ≤ i.val; omega)
      have hr := D.row_strictAnti.antitone (Fin.le_last
        (⟨i.val + 1, hi⟩ : Fin (n + 4)).succ)
      omega

/-- The weak three-corner conditions descend by one row. -/
theorem corner_three_corners (D : BetaDiagram (n + 4)) (hP : D.PositiveCorner)
    (h : D.ThreeCorners) : (D.cornerDiagram hP).ThreeCorners := by
  change D.col (0 : Fin (n + 3)).castSucc ≤ D.row (⟨n, by omega⟩ : Fin (n + 3)).succ ∧
    D.col (1 : Fin (n + 3)).castSucc ≤ D.row (⟨n + 1, by omega⟩ : Fin (n + 3)).succ ∧
    D.col (2 : Fin (n + 3)).castSucc ≤ D.row (Fin.last (n + 2)).succ
  have hr0 : (⟨n, by omega⟩ : Fin (n + 3)).succ = (⟨n + 1, by omega⟩ : Fin (n + 4)) :=
    Fin.ext rfl
  have hr1 : (⟨n + 1, by omega⟩ : Fin (n + 3)).succ = (⟨n + 2, by omega⟩ : Fin (n + 4)) :=
    Fin.ext rfl
  have hc1 : (1 : Fin (n + 3)).castSucc = (1 : Fin (n + 4)) := by
    apply Fin.ext
    change 1 % (n + 3) = 1 % (n + 4)
    rw [Nat.mod_eq_of_lt (by omega : 1 < n + 3),
      Nat.mod_eq_of_lt (by omega : 1 < n + 4)]
  have hc2 : (2 : Fin (n + 3)).castSucc = (2 : Fin (n + 4)) := by
    apply Fin.ext
    change 2 % (n + 3) = 2 % (n + 4)
    rw [Nat.mod_eq_of_lt (by omega : 2 < n + 3),
      Nat.mod_eq_of_lt (by omega : 2 < n + 4)]
  rw [Fin.castSucc_zero, hr0, hr1, hc1, hc2, Fin.succ_last]
  exact h

/-- Gamma preserves all three weak inequalities exactly. -/
theorem gamma_three_corners_iff (D : BetaDiagram (n + 3)) :
    D.gamma.ThreeCorners ↔ D.ThreeCorners := by
  simp only [ThreeCorners, gamma]
  omega

/-- Top endpoint extension stays in the three-corner regime. -/
theorem extendTop_three_corners (D : BetaDiagram (n + 3)) (h : D.ThreeCorners)
    (t : ℤ) (ht : 0 < t) : (D.extendTop t ht).ThreeCorners := by
  rcases h with ⟨h0, h1, h2⟩
  have hrow (i : Fin (n + 3)) : D.row i ≤ (D.extendTop t ht).row i := by
    change D.row i ≤ if i = 0 then D.row i + t else D.row i
    split_ifs <;> omega
  exact ⟨h0.trans (hrow _), h1.trans (hrow _), h2.trans (hrow _)⟩

/-- Bottom endpoint extension stays in that same regime. -/
theorem extendBottom_three_corners (D : BetaDiagram (n + 3)) (h : D.ThreeCorners)
    (t : ℤ) (ht : 0 < t) : (D.extendBottom t ht).ThreeCorners := by
  rcases h with ⟨h0, h1, h2⟩
  have hcol (j : Fin (n + 3)) : (D.extendBottom t ht).col j ≤ D.col j := by
    change (if j = Fin.last (n + 2) then D.col j - t else D.col j) ≤ D.col j
    split_ifs <;> omega
  exact ⟨(hcol _).trans h0, (hcol _).trans h1, (hcol _).trans h2⟩

/-- A disconnected column cofactor produces the full singleton context with
its actual dense core.  No separation, gap or margin is supplied externally. -/
theorem column_parent_singleton_context (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hZ : D.ZeroFree) (h : D.ColumnNegatives)
    (hC : ¬ (D.cornerDiagram hP).Connected) :
    (D.columnCore hP).Dense ∧
      ∃ (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
        D.TranslationEquivalent ((D.columnCore hP).singletonContext s u v g hs hu hv hg) := by
  refine ⟨D.columnCore_dense hP hZ h, ?_⟩
  have hcut := (D.cornerDiagram hP).column_disconnected_first_cut
    (D.corner_column_negatives hP h) hC
  exact D.singleton_parent_of_first_cut hP hcut

/-- The five-row square has two genuine connected two-row cofactor factors,
even if either component contains an index-zero unit. -/
theorem square_five_corner_factors (D : BetaDiagram 5) (hP : D.PositiveCorner)
    (h : D.SquareNegatives) :
    let C := D.cornerDiagram hP
    (C.betaPrefix (a := 2) (b := 2)).Connected ∧
      (C.suffix (a := 2) (b := 2)).Connected ∧
      C.schur = (C.betaPrefix (a := 2) (b := 2)).schur *
        (C.suffix (a := 2) (b := 2)).schur := by
  dsimp only
  let C : BetaDiagram (2 + 2) := D.cornerDiagram hP
  have hcut : C.row 2 < C.col 1 := by
    change D.row 3 < D.col 1
    exact (h 3 1).mpr (by decide)
  have hleft : (C.betaPrefix (a := 2) (b := 2)).Connected := by
    refine ⟨by omega, ?_⟩
    intro i hi
    have hi0 : i = 0 := by apply Fin.ext; omega
    subst i
    change D.col 0 ≤ D.row 2
    exact le_of_not_gt (by intro hn; have hh := (h 2 0).mp hn; norm_num at hh)
  have hright : (C.suffix (a := 2) (b := 2)).Connected := by
    refine ⟨by omega, ?_⟩
    intro i hi
    have hi0 : i = 0 := by apply Fin.ext; omega
    subst i
    change D.col 2 ≤ D.row 4
    exact le_of_not_gt (by intro hn; have hh := (h 4 2).mp hn; norm_num at hh)
  exact ⟨hleft, hright, C.schur_factor_at_cut (by omega) (by omega) hcut⟩

/-- The five-row hook produces the literal singleton-first cut. -/
theorem hook_five_singleton_context (D : BetaDiagram 5) (hP : D.PositiveCorner)
    (h : D.HookNegatives) :
    let Q := (D.cornerDiagram hP).tail
    ∃ (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
      D.TranslationEquivalent (Q.singletonContext s u v g hs hu hv hg) := by
  apply D.singleton_parent_of_first_cut hP
  exact (h 2 0).mpr (by decide)

/-- The nonlinear component of the hook cofactor has exactly one genuine
negative site; its small-negative premise is therefore produced from the source. -/
theorem hook_five_core_negative_sites (D : BetaDiagram 5) (hP : D.PositiveCorner)
    (h : D.HookNegatives) :
    negativeSites (D.cornerDiagram hP).tail = ({(2, 0)} : Finset (Fin 3 × Fin 3)) := by
  ext p
  rcases p with ⟨i, j⟩
  simp only [mem_negativeSites, Finset.mem_singleton, Prod.mk.injEq]
  change D.row i.succ.succ < D.col j.succ.castSucc ↔ i = 2 ∧ j = 0
  rw [h]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The hook's actual nonlinear component has the complete one-negative class. -/
theorem hook_five_core_rigid (D : BetaDiagram 5) (hP : D.PositiveCorner)
    (h : D.HookNegatives) : (D.cornerDiagram hP).tail.RotationRigid := by
  have hcount : negativeCount (D.cornerDiagram hP).tail = 1 := by
    rw [negativeCount, D.hook_five_core_negative_sites hP h]
    simp
  apply one_negative_rigidity
  · apply connected_of_negativeCount_small _ (by omega)
    omega
  · omega

end BetaDiagram

namespace BetaDiagram
variable {n : ℕ}

/-- A connected four-row column board has at most the two actual first-column negatives. -/
theorem four_column_negative_count_le_two (D : BetaDiagram 4) (hD : D.Connected)
    (h : D.ColumnNegatives) : negativeCount D ≤ 2 := by
  classical
  have hs : negativeSites D ⊆ ({(2, 0), (3, 0)} : Finset (Fin 4 × Fin 4)) := by
    intro p hp
    have hn := (D.mem_negativeSites p.1 p.2).mp hp
    have hj := h p.1 p.2 hn
    have hi := D.negative_lt_predecessor hD hn
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp_all
  have hc := Finset.card_le_card hs
  simpa [negativeCount] using hc

/-- Full row induction for `thm:two-negatives`, with the independently produced
four-row base and the actual component-cut budget. -/
theorem two_negative_zeroFree_rigidity (D : BetaDiagram n) (hD : D.Connected)
    (hZ : D.ZeroFree) (hcount : negativeCount D ≤ 2) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 3
    · apply (rotationRigid_iff_same_order D).mpr
      intro E hE he
      exact D.small_rows_rigidity_same_order E hD hE hn he.symm
    · by_cases h4 : n = 4
      · subst n
        exact D.four_two_negative_zeroFree_rigidity hD hZ hcount
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
        let hP := D.positiveCorner_of_connected_zeroFree hD hZ
        let C := D.cornerDiagram hP
        have hC : C.Connected := D.two_negative_corner_connected hP hcount
        have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
        have hCC : negativeCount C ≤ 2 := by
          rw [D.corner_negativeCount hP]
          exact hcount
        apply D.connected_border_rigidity hD hP hC
        · exact ih (k + 4) (by omega) C hC hCZ hCC
        · intro t ht
          apply ih (k + 4) (by omega) (C.extendTop t ht)
          · exact C.extendTop_connected hC t ht
          · exact C.extendTop_zeroFree hCZ t ht
          · rw [extendTop_negativeCount]
            exact hCC

/-- `thm:two-negatives`: all actual row counts and all common betas. -/
theorem two_negative_rigidity (D : BetaDiagram n) (hD : D.Connected)
    (hcount : negativeCount D ≤ 2) : D.RotationRigid := by
  cases n with
  | zero => exact False.elim (by simpa [Connected] using hD.1)
  | succ n =>
    apply D.gamma_rigidity_descends hD
    apply D.gamma.two_negative_zeroFree_rigidity ((D.gamma_connected_iff).mpr hD)
      D.gamma_zeroFree
    simpa only [gamma_negativeCount] using hcount

/-- Every full-board mate is produced to be connected and is a motion of the source. -/
theorem two_negative_full_class (D : BetaDiagram n) (hD : D.Connected)
    (hcount : negativeCount D ≤ 2) {m : ℕ} (E : BetaDiagram m)
    (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.two_negative_rigidity hD hcount).full_mate hD E he

/-- Zero-free column rigidity has no bound on the column height or total negative count. -/
theorem column_negatives_zeroFree_rigidity (D : BetaDiagram n) (hD : D.Connected)
    (hZ : D.ZeroFree) (hcol : D.ColumnNegatives) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 3
    · apply (rotationRigid_iff_same_order D).mpr
      intro E hE he
      exact D.small_rows_rigidity_same_order E hD hE hn he.symm
    · by_cases h4 : n = 4
      · subst n
        exact D.four_two_negative_zeroFree_rigidity hD hZ
          (D.four_column_negative_count_le_two hD hcol)
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
        let hP := D.positiveCorner_of_connected_zeroFree hD hZ
        let C := D.cornerDiagram hP
        have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
        have hCcol : C.ColumnNegatives := D.corner_column_negatives hP hcol
        by_cases hC : C.Connected
        · apply D.connected_border_rigidity hD hP hC
          · exact ih (k + 4) (by omega) C hC hCZ hCcol
          · intro t ht
            exact ih (k + 4) (by omega) (C.extendTop t ht)
              (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
              (C.extendTop_column_negatives hCcol t ht)
        · obtain ⟨hcore, s, u, v, g, hs, hu, hv, hg, hT⟩ :=
            D.column_parent_singleton_context hP hZ hcol hC
          apply D.rotationRigid_of_translation _ hT
          exact (D.columnCore hP).singletonContext_rotationRigid_of_dense
            hcore s u v g hs hu hv hg

/-- The full unbounded column class, with common betas supplied through Gamma. -/
theorem column_negatives_rigidity (D : BetaDiagram n) (hD : D.Connected)
    (hcol : D.ColumnNegatives) : D.RotationRigid := by
  cases n with
  | zero => exact False.elim (by simpa [Connected] using hD.1)
  | succ n =>
    apply D.gamma_rigidity_descends hD
    exact D.gamma.column_negatives_zeroFree_rigidity
      ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree
      ((D.gamma_column_negatives_iff).mpr hcol)

/-- `thm:column`, in the manuscript's two literal weak beta inequalities. -/
theorem column_rigidity (D : BetaDiagram (n + 2)) (hD : D.Connected)
    (h : D.col 1 ≤ D.row (Fin.last (n + 1)) ∨
      D.col 0 ≤ D.row (Fin.last n).castSucc) : D.RotationRigid := by
  rcases h with h | h
  · exact D.column_negatives_rigidity hD ((D.column_negatives_iff_last_row).mpr h)
  · apply D.rotationRigid_of_rotate
    exact D.rotate.column_negatives_rigidity (D.rotate_connected hD)
      ((D.rotate_column_negatives_iff_penultimate_row).mpr h)

/-- No condition at all is imposed on an equal full-board mate in the column theorem. -/
theorem column_full_class (D : BetaDiagram (n + 2)) (hD : D.Connected)
    (h : D.col 1 ≤ D.row (Fin.last (n + 1)) ∨
      D.col 0 ≤ D.row (Fin.last n).castSucc)
    {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.column_rigidity hD h).full_mate hD E he

/-- The genuine five-row hook parent is rigid by the actual singleton producer,
with core rigidity and its fixed leader both supplied internally. -/
theorem hook_five_zeroFree_rigidity (D : BetaDiagram 5) (hD : D.Connected)
    (hZ : D.ZeroFree) (h : D.HookNegatives) : D.RotationRigid := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let Q := (D.cornerDiagram hP).tail
  have hcount : negativeCount Q = 1 := by
    rw [negativeCount, D.hook_five_core_negative_sites hP h]
    simp
  have hQ : Q.Connected := connected_of_negativeCount_small Q (by omega) (by omega)
  have hQZ : Q.ZeroFree := fun i j => hZ i.succ.succ j.succ.castSucc
  have hRQ := Q.one_negative_rigidity hQ (by omega)
  have hLead : ¬ Q.Symmetric → Q.EndpointLeader := by
    intro hS
    exact Q.endpointLeader_one_negative_three hQ hQZ hcount hS
  obtain ⟨s, u, v, g, hs, hu, hv, hg, hT⟩ := D.hook_five_singleton_context hP h
  apply D.rotationRigid_of_translation _ hT
  exact Q.singletonContext_rotationRigid hQ hQZ hRQ hLead s u v g hs hu hv hg

/-- Hook rigidity is propagated through every actual higher row count. -/
theorem hook_negatives_zeroFree_rigidity (D : BetaDiagram n) (hn : 5 ≤ n)
    (hD : D.Connected) (hZ : D.ZeroFree) (h : D.HookNegatives) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h5 : n = 5
    · subst n
      exact D.hook_five_zeroFree_rigidity hD hZ h
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      let hP := D.positiveCorner_of_connected_zeroFree hD hZ
      let C := D.cornerDiagram hP
      have hC : C.Connected := D.hook_corner_connected hP h
      have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
      have hCH : C.HookNegatives := D.corner_hook_negatives hP h
      apply D.connected_border_rigidity hD hP hC
      · exact ih (k + 5) (by omega) C (by omega) hC hCZ hCH
      · intro t ht
        exact ih (k + 5) (by omega) (C.extendTop t ht) (by omega)
          (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
          (C.extendTop_hook_negatives hCH t ht)

/-- The exact full hook mask survives Gamma, including common-beta boundaries. -/
theorem gamma_hook_negatives_iff (D : BetaDiagram n) :
    D.gamma.HookNegatives ↔ D.HookNegatives := by
  unfold HookNegatives
  simp only [gamma_negative_iff]

/-- `prop:hook` for its displayed orientation, with common betas and arbitrary mates. -/
theorem hook_negatives_rigidity (D : BetaDiagram n) (hn : 5 ≤ n)
    (hD : D.Connected) (h : D.HookNegatives) : D.RotationRigid := by
  cases n with
  | zero => omega
  | succ n =>
    apply D.gamma_rigidity_descends hD
    exact D.gamma.hook_negatives_zeroFree_rigidity hn
      ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree
      ((D.gamma_hook_negatives_iff).mpr h)

/-- Either full-board orientation in `prop:hook`, with no mate-pattern restriction. -/
theorem hook_rigidity (D : BetaDiagram n) (hn : 5 ≤ n) (hD : D.Connected)
    (h : D.HookNegatives ∨ D.rotate.HookNegatives) : D.RotationRigid := by
  rcases h with h | h
  · exact D.hook_negatives_rigidity hn hD h
  · exact D.rotationRigid_of_rotate
      (D.rotate.hook_negatives_rigidity hn (D.rotate_connected hD) h)

/-- Full arbitrary-mate hook class, including disconnected candidates. -/
theorem hook_full_class (D : BetaDiagram n) (hn : 5 ≤ n) (hD : D.Connected)
    (h : D.HookNegatives ∨ D.rotate.HookNegatives)
    {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.hook_rigidity hn hD h).full_mate hD E he

/-- Faithful homogenization retains the exact square mask. -/
theorem gamma_square_negatives_iff (D : BetaDiagram n) :
    D.gamma.SquareNegatives ↔ D.SquareNegatives := by
  unfold SquareNegatives
  simp only [gamma_negative_iff]

/-- The two actual square cofactor blocks are dense after homogenization.
No zero beta comparison is strengthened before that passage. -/
theorem square_five_blocks_dense (D : BetaDiagram 5) (hP : D.PositiveCorner)
    (hZ : D.ZeroFree) (h : D.SquareNegatives) :
    let C := D.cornerDiagram hP
    (C.betaPrefix (a := 2) (b := 2)).Dense ∧
      (C.suffix (a := 2) (b := 2)).Dense := by
  dsimp only
  constructor
  · intro i j
    change D.col (j.castAdd 2).castSucc < D.row (i.castAdd 2).succ
    have hz := hZ (i.castAdd 2).succ (j.castAdd 2).castSucc
    have hn : ¬ D.row (i.castAdd 2).succ < D.col (j.castAdd 2).castSucc := by
      intro hh
      have hm := (h _ _).mp hh
      simp only [Fin.val_succ, Fin.val_castAdd, Fin.val_castSucc] at hm
      have := i.isLt
      omega
    omega
  · intro i j
    change D.col (j.natAdd 2).castSucc < D.row (i.natAdd 2).succ
    have hz := hZ (i.natAdd 2).succ (j.natAdd 2).castSucc
    have hn : ¬ D.row (i.natAdd 2).succ < D.col (j.natAdd 2).castSucc := by
      intro hh
      have hm := (h _ _).mp hh
      simp only [Fin.val_succ, Fin.val_natAdd, Fin.val_castSucc] at hm
      omega
    omega

/-- The exact square cut produces all three positive context parameters and
the entire actual parent, not just its cofactor product. -/
theorem square_five_twoComponent_context (D : BetaDiagram 5) (hP : D.PositiveCorner)
    (h : D.SquareNegatives) :
    let C := D.cornerDiagram hP
    let Q := C.betaPrefix (a := 2) (b := 2)
    let R := C.suffix (a := 2) (b := 2)
    ∃ (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
      D.TranslationEquivalent (Q.twoComponentContext R u v g hu hv hg) := by
  dsimp only
  have hcut : (D.twoCutCore (p := 1) (r := 1) hP).row 2 <
      (D.twoCutCore (p := 1) (r := 1) hP).col 1 := by
    change D.row 3 < D.col 1
    exact (h 3 1).mpr (by decide)
  have hdata := D.parent_twoComponentContext_of_cut (p := 1) (r := 1) hP hcut
  have hcore : D.twoCutCore (p := 1) (r := 1) hP = D.cornerDiagram hP := by
    change (D.cornerDiagram hP).reindexOrder (rfl : 4 = 4) = D.cornerDiagram hP
    rfl
  rw [hcore] at hdata
  obtain ⟨hg, hT⟩ := hdata
  refine ⟨D.topMargin, D.bottomMargin,
    ((D.cornerDiagram hP).betaPrefix (a := 2) (b := 2)).col (Fin.last 1) -
      ((D.cornerDiagram hP).suffix (a := 2) (b := 2)).row 0,
    D.topMargin_pos, D.bottomMargin_pos, ?_, ?_⟩
  · exact hg
  · exact hT

/-- The two-negative theorem supplies every positive endpoint-rigidity premise
at the source's actual row count, including common betas. -/
theorem two_negative_endpoint_rigidity (D : BetaDiagram (n + 1))
    (hD : D.Connected) (hcount : negativeCount D ≤ 2)
    (t : ℤ) (ht : 0 < t) : (D.extendTop t ht).RotationRigid := by
  apply two_negative_rigidity _ (D.extendTop_connected hD t ht)
  rw [extendTop_negativeCount]
  exact hcount

/-- A zero-free core with at most two negatives supplies the actual fixed leader
in every row count at least four, including the complete four-row boundary. -/
theorem endpointLeader_two_negative_ge_four (D : BetaDiagram (n + 4))
    (hD : D.Connected) (hZ : D.ZeroFree) (hcount : negativeCount D ≤ 2)
    (hS : ¬ D.Symmetric) : D.EndpointLeader := by
  cases n with
  | zero =>
    by_cases h2 : negativeCount D = 2
    · exact D.endpointLeader_two_negative_four hD hZ h2
    · by_cases h1 : negativeCount D = 1
      · exact D.endpointLeader_one_negative_four hD hZ h1 hS
      · have h0 : negativeCount D = 0 := by omega
        have hDense : D.Dense := by
          intro i j
          have hz := hZ i j
          have hn : ¬ D.row i < D.col j := by
            intro hh
            have hm := (D.mem_negativeSites i j).mpr hh
            have hc : 0 < negativeCount D :=
              Finset.card_pos.mpr ⟨(i, j), hm⟩
            omega
          omega
        exact D.endpointLeader_dense hDense hS
  | succ n =>
    exact D.endpointLeader_small_negative hD hZ (by omega) hS

/-- The exact square mask has four negative sites at every source order ≥5. -/
theorem square_negative_count (D : BetaDiagram (n + 5)) (h : D.SquareNegatives) :
    negativeCount D = 4 := by
  classical
  let a : Fin (n + 5) := ⟨n + 3, by omega⟩
  let b : Fin (n + 5) := Fin.last (n + 4)
  have hs : negativeSites D = ({(a, 0), (a, 1), (b, 0), (b, 1)} :
      Finset (Fin (n + 5) × Fin (n + 5))) := by
    ext p
    rcases p with ⟨i, j⟩
    rw [mem_negativeSites, h]
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff]
    dsimp [a, b]
    simp only [Nat.mod_eq_of_lt (by omega : 1 < n + 5)]
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [negativeCount, hs]
  norm_num [a, b, Fin.ext_iff]

/-- The displayed hook also has exactly four sites, with its bottom tip retained. -/
theorem hook_negative_count (D : BetaDiagram (n + 5)) (h : D.HookNegatives) :
    negativeCount D = 4 := by
  classical
  let a : Fin (n + 5) := ⟨n + 2, by omega⟩
  let b : Fin (n + 5) := ⟨n + 3, by omega⟩
  let c : Fin (n + 5) := Fin.last (n + 4)
  have hs : negativeSites D = ({(a, 0), (b, 0), (c, 0), (c, 1)} :
      Finset (Fin (n + 5) × Fin (n + 5))) := by
    ext p
    rcases p with ⟨i, j⟩
    rw [mem_negativeSites, h]
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff]
    dsimp [a, b, c]
    simp only [Nat.mod_eq_of_lt (by omega : 1 < n + 5)]
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [negativeCount, hs]
  norm_num [a, b, c, Fin.ext_iff]

/-- The actual five-row square is the positive context of its two dense
two-row components; the generic full two-component producer settles every mate. -/
theorem square_five_zeroFree_rigidity (D : BetaDiagram 5) (hD : D.Connected)
    (hZ : D.ZeroFree) (h : D.SquareNegatives) : D.RotationRigid := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let C := D.cornerDiagram hP
  let Q := C.betaPrefix (a := 2) (b := 2)
  let R := C.suffix (a := 2) (b := 2)
  obtain ⟨hQ, hR⟩ := D.square_five_blocks_dense hP hZ h
  obtain ⟨u, v, g, hu, hv, hg, hT⟩ := D.square_five_twoComponent_context hP h
  apply D.rotationRigid_of_translation _ hT
  exact Q.twoComponentContext_rotationRigid_of_dense R hQ hR u v g hu hv hg

/-- `thm:square` above five rows follows through the actual connected square
child and all its positive endpoint extensions. -/
theorem square_negatives_zeroFree_rigidity (D : BetaDiagram n) (hn : 5 ≤ n)
    (hD : D.Connected) (hZ : D.ZeroFree) (h : D.SquareNegatives) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h5 : n = 5
    · subst n
      exact D.square_five_zeroFree_rigidity hD hZ h
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      let hP := D.positiveCorner_of_connected_zeroFree hD hZ
      let C := D.cornerDiagram hP
      have hC : C.Connected := D.square_corner_connected hP h
      have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
      have hCH : C.SquareNegatives := D.corner_square_negatives hP h
      apply D.connected_border_rigidity hD hP hC
      · exact ih (k + 5) (by omega) C (by omega) hC hCZ hCH
      · intro t ht
        exact ih (k + 5) (by omega) (C.extendTop t ht) (by omega)
          (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
          (C.extendTop_square_negatives hCH t ht)

/-- The complete square theorem with common betas and arbitrary connected mates. -/
theorem square_rigidity (D : BetaDiagram n) (hn : 5 ≤ n) (hD : D.Connected)
    (h : D.SquareNegatives) : D.RotationRigid := by
  cases n with
  | zero => omega
  | succ n =>
    apply D.gamma_rigidity_descends hD
    exact D.gamma.square_negatives_zeroFree_rigidity hn
      ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree
      ((D.gamma_square_negatives_iff).mpr h)

/-- The full-board square class includes every mate order and component inventory. -/
theorem square_full_class (D : BetaDiagram n) (hn : 5 ≤ n) (hD : D.Connected)
    (h : D.SquareNegatives) {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) :
    D.MotionEquivalent E := (D.square_rigidity hn hD h).full_mate hD E he

end BetaDiagram

end SkewJacobiNegative
