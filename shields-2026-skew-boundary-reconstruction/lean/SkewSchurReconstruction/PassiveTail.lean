/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.PassiveMatrices
import SkewSchurReconstruction.RatioNormalization

/-!
# The actual passive tail

Formalizes “The passive tail” (`app:rank4`): “Top-row transfers and passive
tails”, “Starvation and both-passive vanishing” (`lem:starvation`,
`cor:both-passive`), and “Mixed factorization” (`prop:block-factorization`).
Passive columns use the largest supported shift of the actual cofactor defect.
Connectedness supplies every deleted-column determinant's nonvanishing.
The saturated capacity in both-passive vanishing is the paper's explicit
hypothesis, not a conclusion of the starvation count.  Sorry-free.
-/

namespace SkewSchurReconstruction

private theorem fin_suffix_card_iff {N : ℕ} (s : Finset (Fin N))
    (hsuffix : ∀ i ∈ s, ∀ j, i ≤ j → j ∈ s) (i : Fin N) :
    i ∈ s ↔ N - s.card ≤ i.val := by
  classical
  by_cases hs : s.Nonempty
  · let t := s.min' hs
    have he : s = Finset.Ici t := by
      ext j
      constructor
      · intro hj
        exact Finset.mem_Ici.mpr (Finset.min'_le s j hj)
      · intro hj
        exact hsuffix t (Finset.min'_mem s hs) j (Finset.mem_Ici.mp hj)
    have ht := t.isLt
    rw [he, Finset.mem_Ici, Fin.card_Ici]
    change t.val ≤ i.val ↔ N - (N - t.val) ≤ i.val
    omega
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hi := i.isLt
    simp only [he, Finset.notMem_empty, Finset.card_empty, Nat.sub_zero, false_iff]
    omega

namespace Diagram

variable {n : ℕ}

/-- The columns beyond the last supported shift of the actual defect. -/
noncomputable def passiveColumns (X Y : Diagram n) (hG : gridDefect X Y ≠ 0) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun j => lastDefectShift X Y hG < X.capShift j)

/-- Actual rows whose entries vanish at every active column. -/
noncomputable def starvedRows (X Y : Diagram n) (hG : gridDefect X Y ≠ 0) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, j ∉ passiveColumns X Y hG → X.capMatrix i j = 0)

@[simp] theorem mem_passiveColumns (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (j : Fin (n + 1)) : j ∈ passiveColumns X Y hG ↔ lastDefectShift X Y hG < X.capShift j := by
  simp [passiveColumns]

@[simp] theorem mem_starvedRows (X Y : Diagram n) (hG : gridDefect X Y ≠ 0) (i : Fin n) :
    i ∈ starvedRows X Y hG ↔ ∀ j, j ∉ passiveColumns X Y hG → X.capMatrix i j = 0 := by
  classical
  simp [starvedRows]

/-- Matrix zero entries are precisely the negative complete indices. -/
theorem capMatrix_eq_zero_iff (X : Diagram n) (i : Fin n) (j : Fin (n + 1)) :
    X.capMatrix i j = 0 ↔ X.capShift j < X.rowParam i := by
  change complete (X.capShift j - X.rowParam i) = 0 ↔ _
  constructor
  · intro hz
    by_contra hn
    have hp := (complete_ne_zero_iff (X.capShift j - X.rowParam i)).mpr (by omega)
    exact hp hz
  · intro h
    exact complete_of_neg (by omega)

/-- Starvation is the active-column coordinate inequality in `app:rank4`. -/
theorem starved_iff_active_below (X Y : Diagram n) (hG : gridDefect X Y ≠ 0) (i : Fin n) :
    i ∈ starvedRows X Y hG ↔
      ∀ j, j ∉ passiveColumns X Y hG → X.capShift j < X.rowParam i := by
  simp only [mem_starvedRows, capMatrix_eq_zero_iff]

theorem passiveColumns_upper_closed (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    {i j : Fin (n + 1)} (hi : i ∈ passiveColumns X Y hG) (hij : i ≤ j) :
    j ∈ passiveColumns X Y hG := by
  apply (mem_passiveColumns X Y hG j).mpr
  exact ((mem_passiveColumns X Y hG i).mp hi).trans_le (X.capShift_strictMono.monotone hij)

theorem starvedRows_upper_closed (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    {i j : Fin n} (hi : i ∈ starvedRows X Y hG) (hij : i ≤ j) :
    j ∈ starvedRows X Y hG := by
  apply (starved_iff_active_below X Y hG j).mpr
  intro k hk
  exact ((starved_iff_active_below X Y hG i).mp hi k hk).trans_le
    (X.rowParam_strictMono.monotone hij)

/-- Passive columns are exactly the last `P` columns. -/
theorem passiveColumns_suffix (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (j : Fin (n + 1)) :
    j ∈ passiveColumns X Y hG ↔ n + 1 - (passiveColumns X Y hG).card ≤ j.val := by
  exact fin_suffix_card_iff _ (fun _ hi _ hij => passiveColumns_upper_closed X Y hG hi hij) j

/-- Starved rows are exactly the last `high.card` rows. -/
theorem starvedRows_suffix (X Y : Diagram n) (hG : gridDefect X Y ≠ 0) (i : Fin n) :
    i ∈ starvedRows X Y hG ↔ n - (starvedRows X Y hG).card ≤ i.val := by
  exact fin_suffix_card_iff _ (fun _ hi _ hij => starvedRows_upper_closed X Y hG hi hij) i

/-- Actual connected cofactors supply every deleted-column minor's nonzero determinant. -/
theorem connected_deleted_minor_ne_zero (X : Diagram n) (hX : X.Connected)
    (j : Fin (n + 1)) : (X.capMatrix.submatrix id j.succAbove).det ≠ 0 := by
  intro hz
  apply X.cofactor_ne_zero squareWeight hX j
  unfold cofactor signedMaximalCofactor
  rw [hz, mul_zero]

/-- The starvation bound has no undischarged maximal-minor premise. -/
theorem passive_tail_starvation (X Y : Diagram n) (hX : X.Connected)
    (hG : gridDefect X Y ≠ 0) (hpassive : (passiveColumns X Y hG).Nonempty) :
    (starvedRows X Y hG).card ≤ (passiveColumns X Y hG).card - 1 := by
  obtain ⟨j, hj⟩ := hpassive
  apply high_card_le_passive_sub_one X.capMatrix (starvedRows X Y hG)
    (passiveColumns X Y hG) j hj
  · intro i hi k hk
    exact ((mem_starvedRows X Y hG i).mp hi) k hk
  · exact connected_deleted_minor_ne_zero X hX j

/-- Both-passive vanishing for every actual square submatrix retaining all starved rows.
The saturated capacity is exactly the explicit assumption of `cor:both-passive`. -/
theorem passive_tail_both_passive {m : ℕ} (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (i j : Fin (n + 1)) (hi : i ∈ passiveColumns X Y hG)
    (hj : j ∈ passiveColumns X Y hG) (hij : i ≠ j)
    (hsaturated : (starvedRows X Y hG).card = (passiveColumns X Y hG).card - 1)
    (rows : Fin m → Fin n) (cols : Fin m → Fin (n + 1))
    (hrows : Function.Injective rows) (hcols : Function.Injective cols)
    (hcover : ∀ r ∈ starvedRows X Y hG, ∃ k, rows k = r)
    (havoid_i : ∀ k, cols k ≠ i) (havoid_j : ∀ k, cols k ≠ j) :
    (X.capMatrix.submatrix rows cols).det = 0 := by
  apply both_passive_submatrix_det_eq_zero X.capMatrix (starvedRows X Y hG)
    (passiveColumns X Y hG) i j hi hj hij hsaturated rows cols hrows hcols hcover havoid_i havoid_j
  intro r hr c hc
  exact ((mem_starvedRows X Y hG r).mp hr) c hc

/-- A top-row transfer has no passive column even without a common normalized grid. -/
theorem top_transfer_no_passive (X Y : Diagram n) (hX : X.Connected) (hY : Y.Connected)
    (hG : gridDefect X Y ≠ 0) (hinner : X.inner = Y.inner) (htop : X.top ≠ Y.top) :
    passiveColumns X Y hG = ∅ := by
  classical
  have he := lastDefectShift_eq_terminalBound_of_top_ne X Y hX hY hG hinner htop
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hp := (mem_passiveColumns X Y hG j).mp hj
  have hc := X.capShift_strictMono.monotone (Fin.le_last j)
  unfold terminalBound at he
  rw [he] at hp
  have hm : X.capShift (Fin.last n) ≤ max (X.capShift (Fin.last n)) (Y.capShift (Fin.last n)) :=
    le_max_left _ _
  omega

private theorem starvedCard_le_n (X Y : Diagram n) (hG : gridDefect X Y ≠ 0) :
    (starvedRows X Y hG).card ≤ n := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card (Finset.subset_univ (starvedRows X Y hG)))

/-- The selected columns in their original increasing order. -/
noncomputable def sortedCapMinor (X : Diagram n) (J : Finset (Fin (n + 1)))
    (hJ : J.card = n) : Matrix (Fin n) (Fin n) CompleteRing :=
  X.capMatrix.submatrix id (J.orderEmbOfFin hJ)

/-- The sorted minor with only a dimension cast, not a row or column permutation. -/
noncomputable def passiveBlockMatrix (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (J : Finset (Fin (n + 1))) (hJ : J.card = n) :
    Matrix (Fin (n - (starvedRows X Y hG).card + (starvedRows X Y hG).card))
      (Fin (n - (starvedRows X Y hG).card + (starvedRows X Y hG).card)) CompleteRing :=
  (sortedCapMinor X J hJ).submatrix
    (Fin.castOrderIso (Nat.sub_add_cancel (starvedCard_le_n X Y hG))).toEquiv
    (Fin.castOrderIso (Nat.sub_add_cancel (starvedCard_le_n X Y hG))).toEquiv

/-- The low-row/active-column block of the actual sorted minor. -/
noncomputable def passiveLowBlock (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (J : Finset (Fin (n + 1))) (hJ : J.card = n) :
    Matrix (Fin (n - (starvedRows X Y hG).card))
      (Fin (n - (starvedRows X Y hG).card)) CompleteRing :=
  (passiveBlockMatrix X Y hG J hJ).submatrix
    (Fin.castAdd (starvedRows X Y hG).card) (Fin.castAdd (starvedRows X Y hG).card)

/-- The high-row/passive-column block of the actual sorted minor. -/
noncomputable def passiveHighBlock (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (J : Finset (Fin (n + 1))) (hJ : J.card = n) :
    Matrix (Fin (starvedRows X Y hG).card) (Fin (starvedRows X Y hG).card) CompleteRing :=
  (passiveBlockMatrix X Y hG J hJ).submatrix
    (Fin.natAdd (n - (starvedRows X Y hG).card))
    (Fin.natAdd (n - (starvedRows X Y hG).card))

/-- A sorted selection with exactly `high.card` passive columns has its passive
columns exactly in the last `high.card` positions. -/
theorem selected_passive_suffix (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (J : Finset (Fin (n + 1))) (hJ : J.card = n)
    (hcount : (J ∩ passiveColumns X Y hG).card = (starvedRows X Y hG).card)
    (i : Fin n) :
    J.orderEmbOfFin hJ i ∈ passiveColumns X Y hG ↔
      n - (starvedRows X Y hG).card ≤ i.val := by
  classical
  let c := J.orderEmbOfFin hJ
  let T : Finset (Fin n) := Finset.univ.filter (fun i => c i ∈ passiveColumns X Y hG)
  have himage : T.image c = J ∩ passiveColumns X Y hG := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_inter.mpr ⟨J.orderEmbOfFin_mem hJ i, (Finset.mem_filter.mp hi).2⟩
    · intro hj
      obtain ⟨hjJ, hjP⟩ := Finset.mem_inter.mp hj
      rw [← J.image_orderEmbOfFin_univ hJ] at hjJ
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hjJ
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, hi⟩
      simpa only [c, hi] using hjP
  have hcard : T.card = (starvedRows X Y hG).card := by
    rw [← hcount, ← himage, Finset.card_image_of_injective T c.injective]
  have hsuffix : ∀ a ∈ T, ∀ b, a ≤ b → b ∈ T := by
    intro a ha b hab
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ b, ?_⟩
    exact passiveColumns_upper_closed X Y hG (Finset.mem_filter.mp ha).2 (c.monotone hab)
  have hi := fin_suffix_card_iff T hsuffix i
  rw [hcard] at hi
  simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hi

/-- The lower-left block is actually zero: its rows are starved and its selected
columns are active, by the proved suffix counts. -/
theorem passiveBlockMatrix_lower_left_zero (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (J : Finset (Fin (n + 1))) (hJ : J.card = n)
    (hcount : (J ∩ passiveColumns X Y hG).card = (starvedRows X Y hG).card) :
    ∀ i : Fin (starvedRows X Y hG).card,
      ∀ j : Fin (n - (starvedRows X Y hG).card),
        passiveBlockMatrix X Y hG J hJ
          (Fin.natAdd (n - (starvedRows X Y hG).card) i)
          (Fin.castAdd (starvedRows X Y hG).card j) = 0 := by
  intro i j
  let e := (Fin.castOrderIso (Nat.sub_add_cancel (starvedCard_le_n X Y hG))).toEquiv
  let r : Fin n := e (Fin.natAdd (n - (starvedRows X Y hG).card) i)
  let k : Fin n := e (Fin.castAdd (starvedRows X Y hG).card j)
  have hr : r ∈ starvedRows X Y hG := by
    apply (starvedRows_suffix X Y hG r).mpr
    change n - (starvedRows X Y hG).card ≤ n - (starvedRows X Y hG).card + i.val
    omega
  have hk : J.orderEmbOfFin hJ k ∉ passiveColumns X Y hG := by
    rw [selected_passive_suffix X Y hG J hJ hcount]
    change ¬ n - (starvedRows X Y hG).card ≤ j.val
    exact not_le.mpr j.isLt
  exact ((mem_starvedRows X Y hG r).mp hr) (J.orderEmbOfFin hJ k) hk

/-- Mixed factorization for the actual sorted column selection, `prop:block-factorization`.
No sign occurs because the dimension cast changes neither index order. -/
theorem passive_tail_block_factorization (X Y : Diagram n) (hG : gridDefect X Y ≠ 0)
    (J : Finset (Fin (n + 1))) (hJ : J.card = n)
    (hcount : (J ∩ passiveColumns X Y hG).card = (starvedRows X Y hG).card) :
    (sortedCapMinor X J hJ).det =
      (passiveLowBlock X Y hG J hJ).det * (passiveHighBlock X Y hG J hJ).det := by
  have h := det_sorted_passive_blocks (passiveBlockMatrix X Y hG J hJ)
    (passiveBlockMatrix_lower_left_zero X Y hG J hJ hcount)
  change (passiveBlockMatrix X Y hG J hJ).det =
    (passiveLowBlock X Y hG J hJ).det * (passiveHighBlock X Y hG J hJ).det at h
  unfold passiveBlockMatrix at h
  rw [Matrix.det_submatrix_equiv_self] at h
  exact h

end Diagram
end SkewSchurReconstruction
