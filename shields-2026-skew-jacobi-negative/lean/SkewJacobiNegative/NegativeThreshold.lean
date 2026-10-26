/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.LowNegativePatterns
import SkewJacobiNegative.FourRowBorders
import SkewJacobiNegative.NegativeBudgetInventory
import SkewJacobiNegative.OneNegativeThreeComponentPlacements
import SkewJacobiNegative.TenNegativeFamilies

/-!
# The sharp negative-index rigidity threshold

The actual minimum-order cut budgets, connected-child induction and Gamma
passage in `sec:threshold-proof`, `thm:negative-threshold` and
`cor:ten-negative-high-minimum` of
`shields-2026-skew-jacobi-negative.tex`.  The sharpness witness consists of
actual seven-row diagrams from `prop:ten-negative-quartet`.
-/

namespace SkewJacobiNegative
namespace BetaDiagram
variable {n : ℕ}

/-- A genuine first cut contributes one negative per retained tail row. -/
private theorem first_cut_negative_count {m : ℕ} (C : BetaDiagram (m + 2))
    (hcut : C.row 1 < C.col 0) :
    negativeCount C = m + 1 + negativeCount C.tail := by
  classical
  have hOrder : 1 + (m + 1) = m + 2 := by omega
  let E : BetaDiagram (1 + (m + 1)) := C.reindexOrder hOrder
  have h1 : (1 : Fin (m + 2)).val = 1 := by
    change 1 % (m + 2) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hi : Fin.cast hOrder (⟨1, by omega⟩ : Fin (1 + (m + 1))) =
      (1 : Fin (m + 2)) := by
    apply Fin.ext
    simp only [Fin.val_cast, h1]
  have hj : Fin.cast hOrder (⟨1 - 1, by omega⟩ : Fin (1 + (m + 1))) =
      (0 : Fin (m + 2)) := by
    apply Fin.ext
    simp
  have hcutE : E.row ⟨1, by omega⟩ < E.col ⟨1 - 1, by omega⟩ := by
    change C.row (Fin.cast hOrder ⟨1, by omega⟩) <
      C.col (Fin.cast hOrder ⟨1 - 1, by omega⟩)
    rw [hi, hj]
    exact hcut
  have hzero : negativeCount (E.betaPrefix (a := 1) (b := m + 1)) = 0 := by
    change (negativeSites (E.betaPrefix (a := 1) (b := m + 1))).card = 0
    apply Finset.card_eq_zero.mpr
    ext p
    simp only [Finset.notMem_empty, iff_false]
    rcases p with ⟨i, j⟩
    intro hm
    have hneg := ((E.betaPrefix (a := 1) (b := m + 1)).mem_negativeSites i j).mp hm
    have hbelow := (E.betaPrefix (a := 1) (b := m + 1)).negative_below_diagonal hneg
    have hiBound := i.isLt
    have hjBound := j.isLt
    omega
  have hRows : (E.suffix (a := 1) (b := m + 1)).row = C.tail.row := by
    funext i
    change C.row (Fin.cast hOrder (i.natAdd 1)) = C.row i.succ
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
    omega
  have hCols : (E.suffix (a := 1) (b := m + 1)).col = C.tail.col := by
    funext i
    change C.col (Fin.cast hOrder (i.natAdd 1)) = C.col i.succ
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
    omega
  have hTail : E.suffix (a := 1) (b := m + 1) = C.tail := by
    cases hA : E.suffix (a := 1) (b := m + 1)
    cases hB : C.tail
    simp_all only [BetaDiagram.mk.injEq]
  have hb := E.negativeCount_at_cut (a := 1) (b := m + 1)
    (by omega) (by omega) hcutE
  change negativeCount (C.reindexOrder hOrder) =
    negativeCount (E.betaPrefix (a := 1) (b := m + 1)) +
      negativeCount (E.suffix (a := 1) (b := m + 1)) + 1 * (m + 1) at hb
  rw [C.reindexOrder_negativeCount hOrder, hzero, hTail] at hb
  simpa only [zero_add, one_mul, Nat.add_comm] using hb

/-- A genuine disconnected maximal cofactor whose budget is below the least
two-nonlinear-component rectangle has a singleton at an end.  This is the
unbounded geometric step used in `sec:threshold-proof`. -/
theorem threshold_singleton_side (D : BetaDiagram (n + 5))
    (hP : D.PositiveCorner)
    (hBudget : negativeCount D < 2 * (n + 2))
    (hdis : ¬ (D.cornerDiagram hP).Connected) :
    D.row 2 < D.col 0 ∨ D.rotate.row 2 < D.rotate.col 0 := by
  let C := D.cornerDiagram hP
  have h2 : (2 : Fin (n + 5)).val = 2 := by
    change 2 % (n + 5) = 2
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨i, hi, hcut⟩ := C.exists_negative_cut (by omega) hdis
  have hrect := C.cut_rectangle_le_negativeCount i hi hcut
  rw [D.corner_negativeCount hP] at hrect
  have hend : i.val = 0 ∨ i.val = n + 2 := by
    by_contra hh
    have hleft : 2 ≤ i.val + 1 := by omega
    have hright : 2 ≤ n + 4 - (i.val + 1) := by omega
    let a := i.val + 1 - 2
    let b := n + 4 - (i.val + 1) - 2
    have ha : i.val + 1 = a + 2 := by dsimp [a]; omega
    have hb : n + 4 - (i.val + 1) = b + 2 := by dsimp [b]; omega
    have hsum : a + b = n := by dsimp [a, b]; omega
    rw [hb, ha] at hrect
    nlinarith [Nat.zero_le (a * b)]
  rcases hend with hfirst | hlast
  · have hi0 : i = 0 := Fin.ext hfirst
    subst i
    exact Or.inl hcut
  · right
    have hr : (⟨i.val + 1, hi⟩ : Fin (n + 4)).succ =
        (0 : Fin (n + 5)).rev := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_rev, Fin.val_zero]
      omega
    have hc : i.castSucc = (2 : Fin (n + 5)).rev := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_rev, h2]
      omega
    change D.row (⟨i.val + 1, hi⟩ : Fin (n + 4)).succ < D.col i.castSucc at hcut
    change -D.col (2 : Fin (n + 5)).rev < -D.row (0 : Fin (n + 5)).rev
    rw [← hc, ← hr]
    exact neg_lt_neg hcut

/-- The actual singleton-first presentation supplies its entire count budget;
the nonlinear core is the literal retained beta tail. -/
theorem threshold_singleton_core_count (D : BetaDiagram (n + 4))
    (hP : D.PositiveCorner) (hcut : D.row 2 < D.col 0) :
    negativeCount D = n + 2 + negativeCount (D.cornerDiagram hP).tail := by
  have h := first_cut_negative_count (D.cornerDiagram hP) hcut
  rwa [D.corner_negativeCount hP] at h

/-- Three internal negatives in a core of order at least five supply all
singleton lifting inputs through the full three-negative theorem and actual
fixed endpoint leader. -/
theorem threshold_singleton_first_three_negative (D : BetaDiagram (n + 7))
    (hD : D.Connected) (hZ : D.ZeroFree) (hP : D.PositiveCorner)
    (hcut : D.row 2 < D.col 0)
    (hCoreCount : negativeCount (D.cornerDiagram hP).tail ≤ 3) :
    D.RotationRigid := by
  let Q := (D.cornerDiagram hP).tail
  change negativeCount Q ≤ 3 at hCoreCount
  have hQ : Q.Connected := Q.connected_of_negativeCount_add_two_le (by omega)
  have hQZ : Q.ZeroFree := fun i j => hZ i.succ.succ j.succ.castSucc
  obtain ⟨s, u, v, g, hs, hu, hv, hg, hT⟩ := D.singleton_parent_of_first_cut hP hcut
  apply D.rotationRigid_of_translation _ hT
  exact Q.singletonContext_rotationRigid hQ hQZ (Q.three_negative_rigidity hQ hCoreCount)
    (fun hS => Q.endpointLeader_small_negative hQ hQZ (by omega) hS)
    s u v g hs hu hv hg

/-- The singleton part of the threshold argument, with every derived premise
produced from the original board.  No minimum-order presentation is assumed. -/
theorem threshold_singleton_budget_zeroFree_rigidity (D : BetaDiagram n)
    (hD : D.Connected) (hZ : D.ZeroFree) (budget : ℕ) (hBudget : 9 ≤ budget)
    (hCount : negativeCount D ≤ budget)
    (hMin : budget ≤ minimumRealizingRows (negativePartition D) + 1) :
    D.RotationRigid := by
  induction n using Nat.strong_induction_on generalizing budget with
  | h n ih =>
    have hn := (D.connected_iff_minimumRealizingRows_le).mp hD
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    let hP := D.positiveCorner_of_connected_zeroFree hD hZ
    let C := D.cornerDiagram hP
    have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
    have hCC : negativeCount C ≤ budget := by
      rw [D.corner_negativeCount hP]
      exact hCount
    have hCM : budget ≤ minimumRealizingRows (negativePartition C) + 1 := by
      rw [D.corner_negativePartition hP]
      exact hMin
    by_cases hC : C.Connected
    · apply D.connected_border_rigidity hD hP hC
      · exact ih (k + 7) (by omega) C hC hCZ budget hBudget hCC hCM
      · intro t ht
        apply ih (k + 7) (by omega) (C.extendTop t ht)
          (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
          budget hBudget
        · rwa [extendTop_negativeCount]
        · rwa [extendTop_negativePartition]
    · have hside := D.threshold_singleton_side hP (by omega) hC
      rcases hside with hcut | hcut
      · have hcore : negativeCount C.tail ≤ 3 := by
          change negativeCount (D.cornerDiagram hP).tail ≤ 3
          have hb := D.threshold_singleton_core_count hP hcut
          omega
        exact D.threshold_singleton_first_three_negative hD hZ hP hcut hcore
      · apply D.rotationRigid_of_rotate
        have hDR := D.rotate_connected hD
        have hZR : D.rotate.ZeroFree := by
          intro i j hh
          apply hZ j.rev i.rev
          change -D.col i.rev = -D.row j.rev at hh
          omega
        let hPR := D.rotate.positiveCorner_of_connected_zeroFree hDR hZR
        have hCR : negativeCount D.rotate ≤ budget := by
          rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
          exact hCount
        have hcore : negativeCount (D.rotate.cornerDiagram hPR).tail ≤ 3 := by
          have hb := D.rotate.threshold_singleton_core_count hPR hcut
          omega
        exact D.rotate.threshold_singleton_first_three_negative hDR hZR hPR hcut hcore

/-- The genuine `2+4` cut of `eq:threshold-budget-table` reconstructs the
entire source with its actual component beta lists and produced margins. -/
theorem threshold_two_four_context (D : BetaDiagram 7) (hP : D.PositiveCorner)
    (hcut : D.row 3 < D.col 1) :
    let C := D.cornerDiagram hP
    let Q := C.betaPrefix (a := 2) (b := 4)
    let R := C.suffix (a := 2) (b := 4)
    ∃ (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
      D.TranslationEquivalent (Q.twoComponentContext R u v g hu hv hg) := by
  dsimp only
  obtain ⟨hg, hT⟩ := D.parent_twoComponentContext_of_cut (p := 1) (r := 3) hP hcut
  exact ⟨D.topMargin, D.bottomMargin, D.col 1 - D.row 3,
    D.topMargin_pos, D.bottomMargin_pos, hg, hT⟩

/-- The `3+3` row of the same table likewise produces the literal full parent.
No component order or separation parameter is supplied as a certificate. -/
theorem threshold_three_three_context (D : BetaDiagram 7) (hP : D.PositiveCorner)
    (hcut : D.row 4 < D.col 2) :
    let C := D.cornerDiagram hP
    let Q := C.betaPrefix (a := 3) (b := 3)
    let R := C.suffix (a := 3) (b := 3)
    ∃ (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
      D.TranslationEquivalent (Q.twoComponentContext R u v g hu hv hg) := by
  dsimp only
  obtain ⟨hg, hT⟩ := D.parent_twoComponentContext_of_cut (p := 2) (r := 2) hP hcut
  exact ⟨D.topMargin, D.bottomMargin, D.col 2 - D.row 4,
    D.topMargin_pos, D.bottomMargin_pos, hg, hT⟩

/-- The extra `2+5` minimum-eight case in `cor:ten-negative-high-minimum`
is reconstructed from its genuine cut, including all positive margins. -/
theorem threshold_two_five_context (D : BetaDiagram 8) (hP : D.PositiveCorner)
    (hcut : D.row 3 < D.col 1) :
    let C := D.cornerDiagram hP
    let Q := C.betaPrefix (a := 2) (b := 5)
    let R := C.suffix (a := 2) (b := 5)
    ∃ (u v g : ℤ) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g),
      D.TranslationEquivalent (Q.twoComponentContext R u v g hu hv hg) := by
  dsimp only
  obtain ⟨hg, hT⟩ := D.parent_twoComponentContext_of_cut (p := 1) (r := 4) hP hcut
  exact ⟨D.topMargin, D.bottomMargin, D.col 1 - D.row 3,
    D.topMargin_pos, D.bottomMargin_pos, hg, hT⟩

/-- Every genuine six-row cofactor cut yields a source singleton, `2+4` or
`3+3` presentation, up to rotating the actual source. -/
theorem threshold_seven_cut_alternatives (D : BetaDiagram 7)
    (hP : D.PositiveCorner) (hdis : ¬ (D.cornerDiagram hP).Connected) :
    D.row 2 < D.col 0 ∨ D.row 3 < D.col 1 ∨ D.row 4 < D.col 2 ∨
      D.rotate.row 3 < D.rotate.col 1 ∨ D.rotate.row 2 < D.rotate.col 0 := by
  obtain ⟨i, hi, hc⟩ := (D.cornerDiagram hP).exists_negative_cut (by omega) hdis
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inl hc))
  · right; right; right; left
    change D.row 5 < D.col 3 at hc
    simp only [rotate]
    norm_num [Fin.rev]
    omega
  · right; right; right; right
    change D.row 6 < D.col 4 at hc
    simp only [rotate]
    norm_num [Fin.rev]
    omega
  · norm_num at hi

/-- At the minimum-eight ten-negative boundary, the true cut rectangle rules
out `3+4` and `4+3`; the only nonlinear split is `2+5`. -/
theorem threshold_eight_cut_alternatives (D : BetaDiagram 8)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 10)
    (hdis : ¬ (D.cornerDiagram hP).Connected) :
    D.row 2 < D.col 0 ∨ D.row 3 < D.col 1 ∨
      D.rotate.row 3 < D.rotate.col 1 ∨ D.rotate.row 2 < D.rotate.col 0 := by
  obtain ⟨i, hi, hc⟩ := (D.cornerDiagram hP).exists_negative_cut (by omega) hdis
  have hb := (D.cornerDiagram hP).cut_rectangle_le_negativeCount i hi hc
  rw [D.corner_negativeCount hP] at hb
  fin_cases i
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · norm_num at hb
    omega
  · norm_num at hb
    omega
  · right; right; left
    change D.row 6 < D.col 4 at hc
    simp only [rotate]
    norm_num [Fin.rev]
    omega
  · right; right; right
    change D.row 7 < D.col 5 at hc
    simp only [rotate]
    norm_num [Fin.rev]
    omega
  · norm_num at hi

/-- Zero internal area and the inherited absence of common betas make an
actual component dense. -/
theorem threshold_dense_of_zero_count (Q : BetaDiagram n) (hZ : Q.ZeroFree)
    (hCount : negativeCount Q = 0) : Q.Dense := by
  intro i j
  have hn : ¬ Q.row i < Q.col j := by
    intro h
    have hp : 0 < negativeCount Q :=
      Finset.card_pos.mpr ⟨(i, j), (Q.mem_negativeSites i j).mpr h⟩
    omega
  have hz := hZ i j
  omega

/-- In a genuine `2+4` cofactor split, excluding the earlier singleton cut
produces a dense two-row core and a connected at-most-one-negative four-row
core.  All zero-free and leading-property inputs are inherited from the source. -/
theorem threshold_two_four_core_inputs (D : BetaDiagram 7) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 3 < D.col 1) (hNoFirst : ¬ D.row 2 < D.col 0) :
    let C := D.cornerDiagram hP
    let Q := C.betaPrefix (a := 2) (b := 4)
    let R := C.suffix (a := 2) (b := 4)
    Q.Dense ∧ R.Connected ∧ R.ZeroFree ∧ negativeCount R ≤ 1 := by
  dsimp only
  let C := D.cornerDiagram hP
  let Q := C.betaPrefix (a := 2) (b := 4)
  let R := C.suffix (a := 2) (b := 4)
  have hb := C.negativeCount_at_cut (a := 2) (b := 4) (by omega) (by omega) hcut
  rw [D.corner_negativeCount hP] at hb
  have hRC : negativeCount R ≤ 1 := by dsimp [R]; omega
  have hR : R.Connected := R.connected_of_negativeCount_add_two_le (by omega)
  have hRZ : R.ZeroFree := fun i j => hZ (i.natAdd 2).succ (j.natAdd 2).castSucc
  have h02 : D.col 0 < D.row 2 := by
    have hz := hZ 2 0
    omega
  refine ⟨?_, hR, hRZ, hRC⟩
  intro i j
  change D.col (j.castAdd 4).castSucc < D.row (i.castAdd 4).succ
  have hr := D.row_strictAnti.antitone
    (show (i.castAdd 4).succ ≤ (2 : Fin 7) by change i.val + 1 ≤ 2; omega)
  have hc := D.col_strictAnti.antitone (Fin.zero_le (j.castAdd 4).castSucc)
  omega

/-- The `3+3` split spends all nine negatives on its true cross rectangle;
both actual three-row components are therefore dense. -/
theorem threshold_three_three_dense (D : BetaDiagram 7) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 4 < D.col 2) :
    let C := D.cornerDiagram hP
    (C.betaPrefix (a := 3) (b := 3)).Dense ∧
      (C.suffix (a := 3) (b := 3)).Dense := by
  dsimp only
  let C := D.cornerDiagram hP
  have hb := C.negativeCount_at_cut (a := 3) (b := 3) (by omega) (by omega) hcut
  rw [D.corner_negativeCount hP] at hb
  dsimp only [C] at hb
  constructor
  · apply threshold_dense_of_zero_count
    · exact fun i j => hZ (i.castAdd 3).succ (j.castAdd 3).castSucc
    · omega
  · apply threshold_dense_of_zero_count
    · exact fun i j => hZ (i.natAdd 3).succ (j.natAdd 3).castSucc
    · omega

/-- The minimum-eight `2+5` split likewise spends the entire ten-negative
budget on its rectangle, so neither actual nonlinear component has a negative. -/
theorem threshold_two_five_dense (D : BetaDiagram 8) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 10)
    (hcut : D.row 3 < D.col 1) :
    let C := D.cornerDiagram hP
    (C.betaPrefix (a := 2) (b := 5)).Dense ∧
      (C.suffix (a := 2) (b := 5)).Dense := by
  dsimp only
  let C := D.cornerDiagram hP
  have hb := C.negativeCount_at_cut (a := 2) (b := 5) (by omega) (by omega) hcut
  rw [D.corner_negativeCount hP] at hb
  dsimp only [C] at hb
  constructor
  · apply threshold_dense_of_zero_count
    · exact fun i j => hZ (i.castAdd 5).succ (j.castAdd 5).castSucc
    · omega
  · apply threshold_dense_of_zero_count
    · exact fun i j => hZ (i.natAdd 2).succ (j.natAdd 2).castSucc
    · omega

/-- Common translation preserves the true negative-site count. -/
theorem threshold_shifted_count (Q : BetaDiagram n) (c : ℤ) :
    negativeCount (Q.shifted c) = negativeCount Q :=
  (Q.shifted c).negativeCount_eq_of_schur_eq Q (Q.shifted_schur c)

/-- Positive bordering preserves the whole partition and hence its true area. -/
theorem threshold_positiveBorder_count (Q : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    negativeCount (Q.positiveBorder u v hu hv) = negativeCount Q := by
  rw [← (Q.positiveBorder u v hu hv).negativePartition_sum,
    Q.positiveBorder_negativePartition u v hu hv, Q.negativePartition_sum]

/-- One separated singleton spends exactly one negative per actual core row. -/
theorem threshold_singletonCore_count (Q : BetaDiagram (n + 1))
    (s g : ℤ) (hs : 0 < s) (hg : 0 < g) :
    negativeCount (Q.singletonCore s g hs hg) = n + 1 + negativeCount Q := by
  have hc : (Q.singletonCore s g hs hg).row 1 <
      (Q.singletonCore s g hs hg).col 0 := by
    change Q.row 0 < Q.row 0 + g
    omega
  have ht : (Q.singletonCore s g hs hg).tail = Q := by rfl
  simpa only [ht] using
    first_cut_negative_count (Q.singletonCore s g hs hg) hc

/-- The count formula remains valid when the singleton is on the right. -/
theorem threshold_rightSingletonCore_count (Q : BetaDiagram (n + 1))
    (s g : ℤ) (hs : 0 < s) (hg : 0 < g) :
    negativeCount (Q.rightSingletonCore s g hs hg) = n + 1 + negativeCount Q := by
  unfold rightSingletonCore
  rw [threshold_shifted_count,
    (Q.rotate.singletonCore s g hs hg).rotate.negativeCount_eq_of_schur_eq
      (Q.rotate.singletonCore s g hs hg) (Q.rotate.singletonCore s g hs hg).rotate_schur,
    threshold_singletonCore_count,
    Q.rotate.negativeCount_eq_of_schur_eq Q Q.rotate_schur]

/-- The full actual singleton parent introduces no additional negative cells. -/
theorem threshold_singletonContext_count (Q : BetaDiagram (n + 1))
    (s u v g : ℤ) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    negativeCount (Q.singletonContext s u v g hs hu hv hg) =
      n + 1 + negativeCount Q := by
  unfold singletonContext
  rw [threshold_shifted_count, threshold_positiveBorder_count, threshold_singletonCore_count]

/-- The actual two-singleton/four-row end context spends exactly nine negatives
outside its core; the formula does not assume core density. -/
theorem threshold_threeEndContext_count (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    negativeCount (Q.threeEndContext P) = 9 + negativeCount Q := by
  unfold threeEndContext
  rw [threshold_singletonContext_count, threshold_singletonCore_count]
  omega

/-- The middle placement has the same exact actual cross cost, including
repeated singleton lengths and every positive margin regime. -/
theorem threshold_threeMiddleContext_count (Q : BetaDiagram 4)
    (P : ThreeComponentParameters) :
    negativeCount (Q.threeMiddleContext P) = 9 + negativeCount Q := by
  unfold threeMiddleContext
  rw [threshold_singletonContext_count, threshold_rightSingletonCore_count]
  omega

/-- Two genuine end cuts and a nine-negative source budget produce a dense
four-row core and the full end context, without assuming that presentation. -/
theorem threshold_dense_end_context (D : BetaDiagram 7) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut₁ : D.row 2 < D.col 0) (hcut₂ : D.row 3 < D.col 1) :
    ∃ (Q : BetaDiagram 4) (P : ThreeComponentParameters),
      Q.Dense ∧ D.TranslationEquivalent (Q.threeEndContext P) := by
  obtain ⟨Q, P, hN, hT⟩ := D.three_end_parent_of_cuts hP hcut₁ hcut₂
  have hN3 : Q.col 3 = 0 := by simpa using hN (by omega)
  have he := D.negativeCount_eq_of_schur_eq (Q.threeEndContext P) hT.schur_eq
  rw [threshold_threeEndContext_count] at he
  have hQC : negativeCount Q = 0 := by omega
  have hQZ : Q.ZeroFree := by
    obtain ⟨c, hr, hc⟩ := hT
    intro i j hij
    have hz := hZ (i.natAdd 3) (j.natAdd 2).castSucc
    apply hz
    rw [hr, hc, Q.threeEndContext_rows P, Q.threeEndContext_cols hN P]
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨Q, P, Q.threshold_dense_of_zero_count hQZ hQC, hT⟩

/-- The two genuine cuts around a middle four-row block produce density from
the same actual source budget, without assuming either singleton order. -/
theorem threshold_dense_middle_context (D : BetaDiagram 7) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut₁ : D.row 2 < D.col 0) (hcut₂ : D.row 6 < D.col 4) :
    ∃ (Q : BetaDiagram 4) (P : ThreeComponentParameters),
      Q.Dense ∧ D.TranslationEquivalent (Q.threeMiddleContext P) := by
  obtain ⟨Q, P, hN, hT⟩ := D.three_middle_parent_of_cuts hP hcut₁ hcut₂
  have hN3 : Q.col 3 = 0 := by simpa using hN (by omega)
  have he := D.negativeCount_eq_of_schur_eq (Q.threeMiddleContext P) hT.schur_eq
  rw [threshold_threeMiddleContext_count] at he
  have hQC : negativeCount Q = 0 := by omega
  have hQZ : Q.ZeroFree := by
    obtain ⟨c, hr, hc⟩ := hT
    intro i j hij
    have hz := hZ (i.natAdd 2).castSucc (j.natAdd 1).castSucc.castSucc
    apply hz
    rw [hr, hc, Q.threeMiddleContext_rows hN P, Q.threeMiddleContext_cols hN P]
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨Q, P, Q.threshold_dense_of_zero_count hQZ hQC, hT⟩

/-- A disconnected five-row tail inside the genuine first-singleton case has
a singleton at one of its own ends.  Its six-cell middle rectangles exceed
the actual remaining budget of four. -/
theorem threshold_seven_singleton_tail_cuts (D : BetaDiagram 7)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 2 < D.col 0)
    (hTail : ¬ (D.cornerDiagram hP).tail.Connected) :
    D.row 3 < D.col 1 ∨ D.row 6 < D.col 4 := by
  let Q := (D.cornerDiagram hP).tail
  have hc : negativeCount Q ≤ 4 := by
    change negativeCount (D.cornerDiagram hP).tail ≤ 4
    have hh := D.threshold_singleton_core_count hP hcut
    omega
  obtain ⟨i, hi, h⟩ := Q.exists_negative_cut (by omega) hTail
  have hb := Q.cut_rectangle_le_negativeCount i hi h
  fin_cases i
  · exact Or.inl h
  · norm_num at hb
    omega
  · norm_num at hb
    omega
  · exact Or.inr h
  · norm_num at hi

/-- The first-singleton minimum-seven source either has its actual connected
five-row core or produces one of the two actual dense three-component parents. -/
theorem threshold_seven_singleton_source_forms (D : BetaDiagram 7)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 2 < D.col 0) :
    (D.cornerDiagram hP).tail.Connected ∨
      ∃ (Q : BetaDiagram 4) (P : ThreeComponentParameters),
        Q.Dense ∧ (D.TranslationEquivalent (Q.threeEndContext P) ∨
          D.TranslationEquivalent (Q.threeMiddleContext P)) := by
  by_cases hQ : (D.cornerDiagram hP).tail.Connected
  · exact Or.inl hQ
  right
  rcases D.threshold_seven_singleton_tail_cuts hP hCount hcut hQ with he | hm
  · obtain ⟨Q, P, hD, hT⟩ := D.threshold_dense_end_context hZ hP hCount hcut he
    exact ⟨Q, P, hD, Or.inl hT⟩
  · obtain ⟨Q, P, hD, hT⟩ := D.threshold_dense_middle_context hZ hP hCount hcut hm
    exact ⟨Q, P, hD, Or.inr hT⟩

/-- The two inventories in `sec:threshold-proof` are produced at the actual
minimum, with the genuine recursive maximal-cofactor components. -/
theorem threshold_actual_minimum_inventories (D : BetaDiagram (n + 1))
    (hD : D.Connected) (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hn : 6 ≤ n)
    (hdis : ¬ (D.cornerDiagram hP).Connected) :
    let C := D.cornerDiagram hP
    (negativeCount D ≤ 9 →
      ∃ cap, ((C.componentDecomposition.components.map Sigma.fst).insertionSort
        (· ≤ ·), cap) ∈ ComponentOrderInventory.ninePatterns ∧
        (C.componentDecomposition.components.map (fun X => negativeCount X.2)).sum ≤ cap) ∧
    (negativeCount D ≤ 10 →
      ∃ cap, ((C.componentDecomposition.components.map Sigma.fst).insertionSort
        (· ≤ ·), cap) ∈ ComponentOrderInventory.tenPatterns ∧
        (C.componentDecomposition.components.map (fun X => negativeCount X.2)).sum ≤ cap) := by
  dsimp only
  have hmin := (D.corner_disconnected_iff_minimum hD hP).mp hdis
  have hp : hP = D.positiveCorner_of_connected_zeroFree hD hZ := Subsingleton.elim _ _
  subst hP
  exact ⟨fun h => D.maximal_cofactor_nine_inventory hD hZ hn hmin h,
    fun h => D.maximal_cofactor_ten_inventory hD hZ hn hmin h⟩

/-- Every actual dense nonlinear component supplies rigidity of itself and
all positive endpoints, together with its fixed leader when nonsymmetric. -/
theorem threshold_dense_lift_inputs (Q : BetaDiagram (n + 2)) (hD : Q.Dense) :
    Q.Connected ∧ Q.ZeroFree ∧ Q.RotationRigid ∧
      (∀ (t : ℤ) (ht : 0 < t), (Q.extendTop t ht).RotationRigid) ∧
      (¬ Q.Symmetric → Q.EndpointLeader) := by
  have hQ := hD.connected (by omega)
  refine ⟨hQ, hD.zeroFree, Q.rotationRigid_of_nonnegative hQ hD.nonnegative, ?_, ?_⟩
  · intro t ht
    exact (Q.extendTop t ht).rotationRigid_of_nonnegative
      (Q.extendTop_connected hQ t ht) (Q.extendTop_nonnegative hD.nonnegative t ht)
  · exact fun hS => Q.endpointLeader_dense hD hS

/-- The genuine `2+4` threshold source produces every nonlinear-component
rigidity, endpoint and leader premise from its own actual beta lists. -/
theorem threshold_two_four_lift_inputs (D : BetaDiagram 7) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 3 < D.col 1) (hNoFirst : ¬ D.row 2 < D.col 0) :
    let C := D.cornerDiagram hP
    let Q := C.betaPrefix (a := 2) (b := 4)
    let R := C.suffix (a := 2) (b := 4)
    (Q.Connected ∧ Q.ZeroFree ∧ Q.RotationRigid ∧
      (∀ (t : ℤ) (ht : 0 < t), (Q.extendTop t ht).RotationRigid) ∧
      (¬ Q.Symmetric → Q.EndpointLeader)) ∧
    (R.Connected ∧ R.ZeroFree ∧ R.RotationRigid ∧
      (∀ (t : ℤ) (ht : 0 < t), (R.extendTop t ht).RotationRigid) ∧
      (¬ R.Symmetric → R.EndpointLeader)) := by
  dsimp only
  let C := D.cornerDiagram hP
  let Q := C.betaPrefix (a := 2) (b := 4)
  let R := C.suffix (a := 2) (b := 4)
  obtain ⟨hQD, hR, hRZ, hRC⟩ :=
    D.threshold_two_four_core_inputs hZ hP hCount hcut hNoFirst
  change negativeCount R ≤ 1 at hRC
  refine ⟨Q.threshold_dense_lift_inputs hQD, hR, hRZ,
    R.two_negative_rigidity hR (by omega), ?_, ?_⟩
  · exact fun t ht => R.two_negative_endpoint_rigidity hR (by omega) t ht
  · exact fun hS => R.endpointLeader_two_negative_ge_four hR hRZ (by omega) hS

/-- The actual `2+4` budget-table case invokes the full arbitrary-mate
two-component theorem, with every core and leader input supplied internally. -/
theorem threshold_two_four_rigidity (D : BetaDiagram 7) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 3 < D.col 1) (hNoFirst : ¬ D.row 2 < D.col 0) :
    D.RotationRigid := by
  let C := D.cornerDiagram hP
  let Q := C.betaPrefix (a := 2) (b := 4)
  let R := C.suffix (a := 2) (b := 4)
  obtain ⟨⟨hQ, hQZ, hQR, _, hQL⟩, ⟨hR, hRZ, hRR, _, hRL⟩⟩ :=
    D.threshold_two_four_lift_inputs hZ hP hCount hcut hNoFirst
  obtain ⟨u, v, g, hu, hv, hg, hT⟩ := D.threshold_two_four_context hP hcut
  exact D.rotationRigid_of_translation _ hT
    (Q.twoComponentContext_rotationRigid R hQ hR hQZ hRZ hQR hRR hQL hRL
      u v g hu hv hg)

/-- The genuine `3+3` source invokes only dense core leaders and rigidity;
no dense-four lower-remainder hypothesis appears. -/
theorem threshold_three_three_rigidity (D : BetaDiagram 7) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 4 < D.col 2) : D.RotationRigid := by
  let C := D.cornerDiagram hP
  let Q := C.betaPrefix (a := 3) (b := 3)
  let R := C.suffix (a := 3) (b := 3)
  obtain ⟨hQD, hRD⟩ := D.threshold_three_three_dense hZ hP hCount hcut
  obtain ⟨u, v, g, hu, hv, hg, hT⟩ := D.threshold_three_three_context hP hcut
  exact D.rotationRigid_of_translation _ hT
    (Q.twoComponentContext_rotationRigid_of_dense R hQD hRD u v g hu hv hg)

/-- The actual minimum-eight `2+5` case invokes the same full two-component
producer on the two genuinely dense components extracted from its source. -/
theorem threshold_two_five_rigidity (D : BetaDiagram 8) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 10)
    (hcut : D.row 3 < D.col 1) : D.RotationRigid := by
  let C := D.cornerDiagram hP
  let Q := C.betaPrefix (a := 2) (b := 5)
  let R := C.suffix (a := 2) (b := 5)
  obtain ⟨hQD, hRD⟩ := D.threshold_two_five_dense hZ hP hCount hcut
  obtain ⟨u, v, g, hu, hv, hg, hT⟩ := D.threshold_two_five_context hP hcut
  exact D.rotationRigid_of_translation _ hT
    (Q.twoComponentContext_rotationRigid_of_dense R hQD hRD u v g hu hv hg)

/-- With both end-singleton cuts excluded, every actual minimum-seven source
is one of the two nonlinear-core cases already discharged above. -/
theorem threshold_seven_without_singletons_rigidity (D : BetaDiagram 7)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hdis : ¬ (D.cornerDiagram hP).Connected)
    (hNoFirst : ¬ D.row 2 < D.col 0)
    (hNoRotFirst : ¬ D.rotate.row 2 < D.rotate.col 0) : D.RotationRigid := by
  rcases D.threshold_seven_cut_alternatives hP hdis with h | h | h | h | h
  · exact False.elim (hNoFirst h)
  · exact D.threshold_two_four_rigidity hZ hP hCount h hNoFirst
  · exact D.threshold_three_three_rigidity hZ hP hCount h
  · apply D.rotationRigid_of_rotate
    have hCountR : negativeCount D.rotate ≤ 9 := by
      rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
      exact hCount
    exact D.rotate.threshold_two_four_rigidity (D.rotate_zeroFree hZ)
      (D.rotate_positiveCorner hP) hCountR h hNoRotFirst
  · exact False.elim (hNoRotFirst h)

/-- Excluding end-singleton cuts at the minimum-eight ten-negative boundary
leaves only the actual dense `2+5` source or its half-turn. -/
theorem threshold_eight_without_singletons_rigidity (D : BetaDiagram 8)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 10)
    (hdis : ¬ (D.cornerDiagram hP).Connected)
    (hNoFirst : ¬ D.row 2 < D.col 0)
    (hNoRotFirst : ¬ D.rotate.row 2 < D.rotate.col 0) : D.RotationRigid := by
  rcases D.threshold_eight_cut_alternatives hP hCount hdis with h | h | h | h
  · exact False.elim (hNoFirst h)
  · exact D.threshold_two_five_rigidity hZ hP hCount h
  · apply D.rotationRigid_of_rotate
    have hCountR : negativeCount D.rotate ≤ 10 := by
      rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
      exact hCount
    exact D.rotate.threshold_two_five_rigidity (D.rotate_zeroFree hZ)
      (D.rotate_positiveCorner hP) hCountR h
  · exact False.elim (hNoRotFirst h)

/-- A genuine connected small-negative core supplies the full singleton
conclusion using its actual rigidity and fixed leader, without an endpoint
certificate or a prescribed mate presentation. -/
theorem threshold_singleton_first_four_negative (D : BetaDiagram (n + 7))
    (hZ : D.ZeroFree) (hP : D.PositiveCorner)
    (hcut : D.row 2 < D.col 0) (hQ : (D.cornerDiagram hP).tail.Connected)
    (hCount : negativeCount (D.cornerDiagram hP).tail ≤ 4) : D.RotationRigid := by
  let Q := (D.cornerDiagram hP).tail
  have hQZ : Q.ZeroFree := fun i j => hZ i.succ.succ j.succ.castSucc
  obtain ⟨s, u, v, g, hs, hu, hv, hg, hT⟩ := D.singleton_parent_of_first_cut hP hcut
  exact D.rotationRigid_of_translation _ hT
    (Q.singletonContext_rotationRigid hQ hQZ (Q.small_negative_rigidity hQ hCount)
      (fun hS => Q.endpointLeader_small_negative hQ hQZ hCount hS)
      s u v g hs hu hv hg)

/-- The connected-five-row-core row of `eq:threshold-budget-table` supplies
its exact internal bound from the actual first-singleton rectangle. -/
theorem threshold_seven_connected_singleton_rigidity (D : BetaDiagram 7)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 2 < D.col 0) (hQ : (D.cornerDiagram hP).tail.Connected) :
    D.RotationRigid := by
  have hQC : negativeCount (D.cornerDiagram hP).tail ≤ 4 := by
    have h := D.threshold_singleton_core_count hP hcut
    omega
  exact D.threshold_singleton_first_four_negative hZ hP hcut hQ hQC

/-- In the minimum-eight singleton case the true cross cost is six and
the remaining at-most-four-negative six-row core is necessarily connected. -/
theorem threshold_eight_first_singleton_rigidity (D : BetaDiagram 8)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 10)
    (hcut : D.row 2 < D.col 0) : D.RotationRigid := by
  have hQC : negativeCount (D.cornerDiagram hP).tail ≤ 4 := by
    have h := D.threshold_singleton_core_count hP hcut
    omega
  have hQ : (D.cornerDiagram hP).tail.Connected :=
    (D.cornerDiagram hP).tail.connected_of_negativeCount_add_two_le (by omega)
  exact D.threshold_singleton_first_four_negative hZ hP hcut hQ hQC

/-- Every true disconnected seven-row maximal cofactor of a ten-negative
eight-row source is settled by its actual singleton or dense `2+5` geometry. -/
theorem threshold_eight_disconnected_rigidity (D : BetaDiagram 8)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 10)
    (hdis : ¬ (D.cornerDiagram hP).Connected) : D.RotationRigid := by
  by_cases hFirst : D.row 2 < D.col 0
  · exact D.threshold_eight_first_singleton_rigidity hZ hP hCount hFirst
  by_cases hRotFirst : D.rotate.row 2 < D.rotate.col 0
  · apply D.rotationRigid_of_rotate
    have hCR : negativeCount D.rotate ≤ 10 := by
      rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
      exact hCount
    exact D.rotate.threshold_eight_first_singleton_rigidity (D.rotate_zeroFree hZ)
      (D.rotate_positiveCorner hP) hCR hRotFirst
  exact D.threshold_eight_without_singletons_rigidity hZ hP hCount hdis hFirst hRotFirst

/-- At every possible higher minimum order, a true disconnected cofactor
has a singleton and an actual core with at most three internal negatives. -/
theorem threshold_ten_disconnected_ge_nine_rigidity (D : BetaDiagram (n + 9))
    (hD : D.Connected) (hZ : D.ZeroFree) (hP : D.PositiveCorner)
    (hCount : negativeCount D = 10)
    (hdis : ¬ (D.cornerDiagram hP).Connected) : D.RotationRigid := by
  have hside := D.threshold_singleton_side hP (by omega) hdis
  rcases hside with h | h
  · have hQC : negativeCount (D.cornerDiagram hP).tail ≤ 3 := by
      have hh := D.threshold_singleton_core_count hP h
      omega
    exact D.threshold_singleton_first_three_negative hD hZ hP h hQC
  · apply D.rotationRigid_of_rotate
    have hCR : negativeCount D.rotate = 10 := by
      rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
      exact hCount
    have hQC : negativeCount (D.rotate.cornerDiagram (D.rotate_positiveCorner hP)).tail ≤ 3 := by
      have hh := D.rotate.threshold_singleton_core_count (D.rotate_positiveCorner hP) h
      omega
    exact D.rotate.threshold_singleton_first_three_negative (D.rotate_connected hD)
      (D.rotate_zeroFree hZ) (D.rotate_positiveCorner hP) h hQC

/-- The actual ten-negative inventory bounds the disconnected cofactor order;
this uses its geometric component list, not a supplied partition census. -/
theorem threshold_ten_disconnected_order_bound (D : BetaDiagram (n + 1))
    (hD : D.Connected) (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hn : 6 ≤ n)
    (hCount : negativeCount D ≤ 10)
    (hdis : ¬ (D.cornerDiagram hP).Connected) : n ≤ 11 := by
  let C := D.cornerDiagram hP
  obtain ⟨cap, hp, _⟩ :=
    (D.threshold_actual_minimum_inventories hD hZ hP hn hdis).2 hCount
  have hs : ((C.componentDecomposition.components.map Sigma.fst).insertionSort
      (· ≤ ·)).sum = n := by
    rw [(List.perm_insertionSort (fun a b : ℕ => a ≤ b)
      (C.componentDecomposition.components.map Sigma.fst)).sum_eq]
    exact C.componentDecomposition.component_rows_sum
  simp only [ComponentOrderInventory.tenPatterns, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h
  all_goals
    obtain ⟨ho, _⟩ := h
    rw [ho] at hs
    norm_num at hs
    omega

/-- `cor:ten-negative-high-minimum` before faithful Gamma descent.  Actual
connected-child bordering preserves the source partition throughout the full
row-count induction. -/
theorem ten_negative_high_minimum_zeroFree_rigidity (D : BetaDiagram n)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D = 10)
    (hMin : 8 ≤ minimumRealizingRows (negativePartition D)) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := (D.connected_iff_minimumRealizingRows_le).mp hD
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    let hP := D.positiveCorner_of_connected_zeroFree hD hZ
    let C := D.cornerDiagram hP
    have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
    have hCC : negativeCount C = 10 := by rwa [D.corner_negativeCount hP]
    have hCM : 8 ≤ minimumRealizingRows (negativePartition C) := by
      rwa [D.corner_negativePartition hP]
    by_cases hC : C.Connected
    · apply D.connected_border_rigidity hD hP hC
      · exact ih (k + 7) (by omega) C hC hCZ hCC hCM
      · intro t ht
        apply ih (k + 7) (by omega) (C.extendTop t ht)
          (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
        · rwa [extendTop_negativeCount]
        · rwa [extendTop_negativePartition]
    · have hk : k ≤ 4 := by
        have hb := D.threshold_ten_disconnected_order_bound hD hZ hP (by omega) hCount.le hC
        omega
      by_cases hk0 : k = 0
      · subst k
        exact D.threshold_eight_disconnected_rigidity hZ hP hCount.le hC
      · have hkpos : 1 ≤ k := by omega
        interval_cases k
        all_goals exact D.threshold_ten_disconnected_ge_nine_rigidity hD hZ hP hCount hC

/-- `cor:ten-negative-high-minimum`, with common betas and arbitrary connected
mate row counts, follows from actual source induction and faithful Gamma. -/
theorem ten_negative_high_minimum_rigidity (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D = 10)
    (hMin : 8 ≤ minimumRealizingRows (negativePartition D)) : D.RotationRigid := by
  cases n with
  | zero => exact False.elim (by simpa [Connected] using hD.1)
  | succ n =>
    apply D.gamma_rigidity_descends hD
    apply D.gamma.ten_negative_high_minimum_zeroFree_rigidity
      ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree
    · simpa only [gamma_negativeCount] using hCount
    · simpa only [gamma_negative_partition] using hMin

/-- The high-minimum ten-negative corollary covers every full-board mate,
including disconnected and differently sized candidates. -/
theorem ten_negative_high_minimum_full_class (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D = 10)
    (hMin : 8 ≤ minimumRealizingRows (negativePartition D))
    {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.ten_negative_high_minimum_rigidity hD hCount hMin).full_mate hD E he

/-- The actual first-singleton minimum-seven source is rigid whether its
five-row tail is connected or splits into the two true dense placements. -/
theorem threshold_seven_first_singleton_rigidity (D : BetaDiagram 7)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hcut : D.row 2 < D.col 0) : D.RotationRigid := by
  rcases D.threshold_seven_singleton_source_forms hZ hP hCount hcut with
    hQ | ⟨Q, P, hQD, hT⟩
  · exact D.threshold_seven_connected_singleton_rigidity hZ hP hCount hcut hQ
  · rcases hT with hEnd | hMiddle
    · exact D.rotationRigid_of_translation _ hEnd
        (Q.dense_threeEndContext_rotationRigid hQD P)
    · exact D.rotationRigid_of_translation _ hMiddle
        (Q.dense_threeMiddleContext_rotationRigid hQD P)

/-- Every minimum-seven nine-negative source is settled by its actual
singleton, two-nonlinear-component or dense-four-plus-two-singletons geometry. -/
theorem threshold_seven_disconnected_rigidity (D : BetaDiagram 7)
    (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hCount : negativeCount D ≤ 9)
    (hdis : ¬ (D.cornerDiagram hP).Connected) : D.RotationRigid := by
  by_cases hFirst : D.row 2 < D.col 0
  · exact D.threshold_seven_first_singleton_rigidity hZ hP hCount hFirst
  by_cases hRotFirst : D.rotate.row 2 < D.rotate.col 0
  · apply D.rotationRigid_of_rotate
    have hCR : negativeCount D.rotate ≤ 9 := by
      rw [D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur]
      exact hCount
    exact D.rotate.threshold_seven_first_singleton_rigidity (D.rotate_zeroFree hZ)
      (D.rotate_positiveCorner hP) hCR hRotFirst
  exact D.threshold_seven_without_singletons_rigidity hZ hP hCount hdis hFirst hRotFirst

/-- The true nine-negative inventory bounds the source's actual minimum
cofactor order, retaining its entire remaining internal-negative budget. -/
theorem threshold_nine_disconnected_order_bound (D : BetaDiagram (n + 1))
    (hD : D.Connected) (hZ : D.ZeroFree) (hP : D.PositiveCorner) (hn : 6 ≤ n)
    (hCount : negativeCount D ≤ 9)
    (hdis : ¬ (D.cornerDiagram hP).Connected) : n ≤ 10 := by
  let C := D.cornerDiagram hP
  obtain ⟨cap, hp, _⟩ :=
    (D.threshold_actual_minimum_inventories hD hZ hP hn hdis).1 hCount
  have hs : ((C.componentDecomposition.components.map Sigma.fst).insertionSort
      (· ≤ ·)).sum = n := by
    rw [(List.perm_insertionSort (fun a b : ℕ => a ≤ b)
      (C.componentDecomposition.components.map Sigma.fst)).sum_eq]
    exact C.componentDecomposition.component_rows_sum
  simp only [ComponentOrderInventory.ninePatterns, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hp
  rcases hp with h | h | h | h | h | h | h | h
  all_goals
    obtain ⟨ho, _⟩ := h
    rw [ho] at hs
    norm_num at hs
    omega

/-- `thm:negative-threshold` for zero-free actual boards.  Minimum-order
geometry is produced from actual component inventories; above the minimum,
connected children and all endpoint extensions retain the negative partition
and are settled by the same strong row-count induction. -/
theorem negative_threshold_zeroFree_rigidity (D : BetaDiagram n)
    (hD : D.Connected) (hZ : D.ZeroFree) (hCount : negativeCount D ≤ 9)
    (hMin : 7 ≤ minimumRealizingRows (negativePartition D)) : D.RotationRigid := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := (D.connected_iff_minimumRealizingRows_le).mp hD
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    let hP := D.positiveCorner_of_connected_zeroFree hD hZ
    let C := D.cornerDiagram hP
    have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
    have hCC : negativeCount C ≤ 9 := by rwa [D.corner_negativeCount hP]
    have hCM : 7 ≤ minimumRealizingRows (negativePartition C) := by
      rwa [D.corner_negativePartition hP]
    by_cases hC : C.Connected
    · apply D.connected_border_rigidity hD hP hC
      · exact ih (k + 6) (by omega) C hC hCZ hCC hCM
      · intro t ht
        apply ih (k + 6) (by omega) (C.extendTop t ht)
          (C.extendTop_connected hC t ht) (C.extendTop_zeroFree hCZ t ht)
        · rwa [extendTop_negativeCount]
        · rwa [extendTop_negativePartition]
    · have hk : k ≤ 4 := by
        have hb := D.threshold_nine_disconnected_order_bound hD hZ hP (by omega) hCount hC
        omega
      have hActual := (D.corner_disconnected_iff_minimum hD hP).mp hC
      by_cases hk0 : k = 0
      · subst k
        exact D.threshold_seven_disconnected_rigidity hZ hP hCount hC
      · have hkpos : 1 ≤ k := by omega
        interval_cases k
        all_goals
          exact D.threshold_singleton_budget_zeroFree_rigidity hD hZ 9
            (by omega) hCount (by omega)

/-- `thm:negative-threshold`: every connected source with at most nine
negatives and actual minimum at least seven is rotation-rigid, including all
common-beta boundaries and arbitrary connected mate row counts. -/
theorem negative_threshold_rigidity (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D ≤ 9)
    (hMin : 7 ≤ minimumRealizingRows (negativePartition D)) : D.RotationRigid := by
  cases n with
  | zero => exact False.elim (by simpa [Connected] using hD.1)
  | succ n =>
    apply D.gamma_rigidity_descends hD
    apply D.gamma.negative_threshold_zeroFree_rigidity
      ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree
    · simpa only [gamma_negativeCount] using hCount
    · simpa only [gamma_negative_partition] using hMin

/-- The negative-index rigidity threshold applies to every full-board mate;
its connectedness and actual row count are consequences, not hypotheses. -/
theorem negative_threshold_full_class (D : BetaDiagram n)
    (hD : D.Connected) (hCount : negativeCount D ≤ 9)
    (hMin : 7 ≤ minimumRealizingRows (negativePartition D))
    {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.negative_threshold_rigidity hD hCount hMin).full_mate hD E he

end BetaDiagram


namespace TenParameters

/-- Both seven-row families supply unequal rotation orbits with equal Schur
functions, ten actual negative indices and actual minimum realizing order seven.
This is the sharpness assertion of `thm:negative-threshold`. -/
theorem negative_threshold_sharpness (P : TenParameters) (second : Bool) :
    let D := P.diagram (if second then .fb else .fa)
    let E := P.diagram (if second then .hb else .ha)
    D.Connected ∧ E.Connected ∧ D.schur = E.schur ∧
      negativeCount D = 10 ∧ negativeCount E = 10 ∧
      minimumRealizingRows (negativePartition D) = 7 ∧
      minimumRealizingRows (negativePartition E) = 7 ∧
      ¬ D.TranslationEquivalent E ∧ ¬ D.RotationEquivalent E := by
  dsimp only
  refine ⟨P.connected _, P.connected _, ?_, P.negativeCount_eq_ten _,
    P.negativeCount_eq_ten _, P.minimum_rows_eq_seven _,
    P.minimum_rows_eq_seven _, P.not_translation _ _ ?_, P.not_rotation _ _⟩
  · cases second
    · exact P.schur_eq_A
    · exact P.schur_eq_B
  · cases second <;> decide

end TenParameters

/-- A concrete common-beta boundary witness: the sharpness statement remains
true at `d = 0`, rather than requiring a zero-free subfamily. -/
def thresholdSharpnessParameters : TenParameters where
  a := 1
  b := 2
  d := 0
  a_pos := by norm_num
  d_nonneg := by norm_num
  separated := by norm_num

/-- The numeric witness is a pair of actual diagrams, not a supplied
classification certificate. -/
theorem negative_threshold_sharpness_exists :
    ∃ D E : BetaDiagram 7,
      D.Connected ∧ E.Connected ∧ D.schur = E.schur ∧
      negativeCount D = 10 ∧ negativeCount E = 10 ∧
      minimumRealizingRows (negativePartition D) = 7 ∧
      minimumRealizingRows (negativePartition E) = 7 ∧
      ¬ D.TranslationEquivalent E ∧ ¬ D.RotationEquivalent E := by
  exact ⟨thresholdSharpnessParameters.diagram .fa,
    thresholdSharpnessParameters.diagram .ha,
    thresholdSharpnessParameters.negative_threshold_sharpness false⟩

end SkewJacobiNegative
