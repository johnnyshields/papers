/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinCompositions
import SkewClassInflation.ZeroSeamCoefficients

/-!
# Literal thin-family row and seam readings

Formalizes the zero-gap multiplicity in `eq:thin-readings` of
`shields-2026-skew-class-inflation.tex`.  Counts are derived from the full
ordered profile construction, with no omission of zero-gap positions.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative
open scoped BigOperators

/-- Joining inserts precisely one new zero seam and retains every original zero seam. -/
theorem zeroSeamCount_zeroJoin {n m : ℕ} (P : Profile n) (Q : Profile m) :
    zeroSeamCount (Profile.zeroJoin P Q) = zeroSeamCount P + zeroSeamCount Q + 1 := by
  classical
  let c : Fin (n + m + 1) := ⟨n, by omega⟩
  unfold zeroSeamCount
  rw [Fin.sum_univ_succAbove _ c, Fin.sum_univ_add]
  have hl : (∑ i : Fin n,
      if (Profile.zeroJoin P Q).g (c.succAbove (i.castAdd m)) = 0 then 1 else 0) =
      ∑ i : Fin n, if P.g i = 0 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i.castAdd m).castSucc < c := by change i.val < n; exact i.isLt
    rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    change (if Profile.joinGaps P Q 0 ⟨i.val, by omega⟩ = 0 then 1 else 0) = _
    rw [Profile.joinGaps_left]
  have hr : (∑ i : Fin m,
      if (Profile.zeroJoin P Q).g (c.succAbove (i.natAdd n)) = 0 then 1 else 0) =
      ∑ i : Fin m, if Q.g i = 0 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : c ≤ (i.natAdd n).castSucc := by change n ≤ n + i.val; omega
    rw [Fin.succAbove_of_le_castSucc _ _ hi]
    have he : (i.natAdd n).succ = (⟨n + 1 + i.val, by have := i.isLt; omega⟩ :
        Fin (n + m + 1)) := by apply Fin.ext; simp; omega
    rw [he]
    change (if Profile.joinGaps P Q 0 ⟨n + 1 + i.val, by omega⟩ = 0 then 1 else 0) = _
    rw [Profile.joinGaps_right]
  rw [hl, hr]
  have hc : (Profile.zeroJoin P Q).g c = 0 := Profile.joinGaps_middle P Q 0
  rw [hc, ite_eq_left rfl]
  omega

namespace ThinParameters

variable (B : ThinParameters)

/-- A single overlapped block has no zero internal seam on the entire thin domain. -/
theorem innerPower_zeroSeamCount (a : ℕ) (ha : 0 < a) :
    zeroSeamCount (B.innerPower a ha) = 0 := by
  have hc : B.c ≠ 0 := Nat.ne_of_gt B.c_pos
  simp [zeroSeamCount, innerPower, hc]

/-- The number of zero seams in a chain is exactly the number of joins. -/
theorem chain_zeroSeamCount (a : ℕ) (ha : 0 < a) (l : List ℕ) (h : ∀ k ∈ l, 0 < k) :
    zeroSeamCount (B.chain a ha l h).2 = l.length := by
  induction l generalizing a with
  | nil => exact B.innerPower_zeroSeamCount a ha
  | cons b l ih =>
    change zeroSeamCount (Profile.zeroJoin (B.innerPower a ha)
      (B.chain b (h b List.mem_cons_self) l
        (fun k hk => h k (List.mem_cons_of_mem _ hk))).2) = _
    rw [zeroSeamCount_zeroJoin, B.innerPower_zeroSeamCount,
      ih b (h b List.mem_cons_self) (fun k hk => h k (List.mem_cons_of_mem _ hk))]
    simp

/-- The full thin source has exactly one fewer zero seam than outer blocks. -/
theorem diagram_zeroSeamCount {M : ℕ} (α : Composition M) (hM : 0 < M) :
    zeroSeamCount (B.diagram α hM).2 + 1 = α.length := by
  unfold diagram
  split
  · rename_i he
    have h := α.blocks_sum
    rw [he] at h
    simp only [List.sum_nil] at h
    omega
  · rename_i a l he
    rw [B.chain_zeroSeamCount]
    simp [Composition.length, he]

end ThinParameters
end SkewClassInflation
