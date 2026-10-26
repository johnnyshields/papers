/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.MergeBetaSets
import SkewClassInflation.ThinBetaSets
import SkewClassInflation.ZeroCutReassembly

/-!
# Merging the first two actual thin blocks

The literal ordered contraction underlying `eq:thin-substitution`
in `shields-2026-skew-class-inflation.tex`.  Only the selected suffix
beta is erased; repeated numerical row lengths are not split by value.
Sorry-free.
-/

namespace SkewClassInflation

/-- Positive word suffixes are strictly between zero and the full word sum. -/
theorem wordSuffixSet_bounds (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    ∀ k ∈ wordSuffixSet l, 0 < k ∧ k < l.sum := by
  let α : Composition l.sum := ⟨l, fun h => hl _ h, rfl⟩
  have he : wordSuffixSet l = suffixSet α := (wordSuffixSet_blocks α)
  rw [he]
  intro k hk
  exact Finset.mem_Ioo.mp (suffixSet_subset α hk)

/-- A proper suffix set is independent of the value of the first part. -/
theorem wordSuffixSet_head (a b : ℕ) (l : List ℕ) :
    wordSuffixSet (a :: l) = wordSuffixSet (b :: l) := by
  cases l with
  | nil => rw [wordSuffixSet_single, wordSuffixSet_single]
  | cons c l => rw [wordSuffixSet_cons a _ (by simp), wordSuffixSet_cons b _ (by simp)]

namespace ThinParameters

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

variable (B : ThinParameters)

/-- A strictly nonzero residue grid cannot contain a multiple of its period. -/
theorem grid_excludes_multiple (r N s : ℕ) (hr : 0 < r) (hrq : r < B.boundary.q) :
    (s : ℤ) * B.boundary.q ∉ arithmeticGrid r B.boundary.q N := by
  intro he
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp he
  have hm := congrArg (fun x : ℤ => x % B.boundary.q) hj
  rw [mul_comm (j : ℤ), Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by omega) (by omega), Int.mul_emod_left] at hm
  omega

/-- Erasing a selected boundary leaves exactly the undeleted suffixes and the intact grid. -/
theorem erase_grid_boundary (r N s : ℕ) (S : Finset ℕ)
    (hr : 0 < r) (hrq : r < B.boundary.q) (hs : s ∉ S) :
    (arithmeticGrid r B.boundary.q N ∪
      (insert s S).image (fun k : ℕ => (k : ℤ) * B.boundary.q)).erase
        ((s : ℤ) * B.boundary.q) =
      arithmeticGrid r B.boundary.q N ∪ S.image (fun k : ℕ => (k : ℤ) * B.boundary.q) := by
  classical
  have hq : 0 < (B.boundary.q : ℤ) := by
    have := B.boundary.p_pos
    have := B.boundary.ap_lt_q
    omega
  have hnot : (s : ℤ) * B.boundary.q ∉
      arithmeticGrid r B.boundary.q N ∪ S.image (fun k : ℕ => (k : ℤ) * B.boundary.q) := by
    rintro he
    rcases Finset.mem_union.mp he with he | he
    · exact B.grid_excludes_multiple r N s hr hrq he
    · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp he
      have hks : k = s := by
        have hh := mul_right_cancel₀ (ne_of_gt hq) he
        exact_mod_cast hh
      exact hs (hks ▸ hk)
  rw [Finset.image_insert, Finset.union_insert, Finset.erase_insert hnot]

/-- The literal first-block merger combines precisely the first two copy multiplicities. -/
theorem merge_chain (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    let R := B.chain b hb l hl
    (⟨a + R.1, Profile.merge (B.innerPower a ha) R.2 0
      ((B.innerPower a ha).r_pos _) (R.2.r_pos _)⟩ : ConnectedProfile) =
      B.chain (a + b) (by omega) l hl := by
  classical
  let R := B.chain b hb l hl
  let hbl : ∀ k ∈ b :: l, 0 < k := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hb
    · exact hl k hk
  have hq := B.boundary_q_eq
  have hca := B.c_lt_a
  have hab := B.a_lt_b
  have hT : wordSuffixSet (a :: b :: l) = insert (b + l.sum) (wordSuffixSet (b :: l)) := by
    simpa only [List.sum_cons] using wordSuffixSet_cons a (b :: l) (by simp)
  have htarget : wordSuffixSet ((a + b) :: l) = wordSuffixSet (b :: l) :=
    wordSuffixSet_head (a + b) b l
  have hsmall := wordSuffixSet_bounds (b :: l) hbl
  have hrow : b + l.sum ∉ insert (a + b + l.sum) (wordSuffixSet (b :: l)) := by
    intro he
    rcases Finset.mem_insert.mp he with he | he
    · omega
    · have hh := (hsmall _ he).2
      simp only [List.sum_cons] at hh
      omega
  have hcol : b + l.sum ∉ insert 0 (wordSuffixSet (b :: l)) := by
    intro he
    rcases Finset.mem_insert.mp he with he | he
    · omega
    · have hh := (hsmall _ he).2
      simp only [List.sum_cons] at hh
      omega
  apply profileSigma_eq_of_full_sets
  · rw [Profile.merge, contract_rowSet]
    change (B.chain a ha (b :: l) hbl).2.toBetaDiagram.rowSet.erase
      ((Profile.zeroJoin (B.innerPower a ha) R.2).xi
        (⟨a, by omega⟩ : Fin (a + R.1 + 1)).succ) = _
    rw [Profile.zeroJoin_seam_xi, B.chain_span, B.chain_rowSet, B.chain_rowSet,
      hT, htarget]
    simp only [List.sum_cons]
    rw [show a + (b + l.sum) = a + b + l.sum by omega,
      Finset.insert_comm (a + b + l.sum) (b + l.sum)]
    exact B.erase_grid_boundary B.b (a + b + l.sum) (b + l.sum) _ (by omega) (by omega) hrow
  · rw [Profile.merge, contract_colSet]
    change (B.chain a ha (b :: l) hbl).2.toBetaDiagram.colSet.erase
      ((Profile.zeroJoin (B.innerPower a ha) R.2).zeta
        (⟨a, by omega⟩ : Fin (a + R.1 + 1)).castSucc) = _
    rw [Profile.zeroJoin_seam_zeta, B.chain_span, B.chain_colSet, B.chain_colSet,
      hT, htarget]
    simp only [List.sum_cons]
    rw [show a + (b + l.sum) = a + b + l.sum by omega,
      Finset.insert_comm 0 (b + l.sum)]
    have hbc : ((B.b - B.c : ℕ) : ℤ) = (B.b : ℤ) - B.c := by omega
    rw [← hbc]
    exact B.erase_grid_boundary (B.b - B.c) (a + b + l.sum) (b + l.sum) _
      (by omega) (by omega) hcol

end ThinParameters
end SkewClassInflation
