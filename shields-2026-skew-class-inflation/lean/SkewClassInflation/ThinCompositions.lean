/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinPowerRigidity
import SkewClassInflation.ProfileJoins
import SkewClassInflation.CompositionSuffixes

/-!
# The actual thin repeated-block diagrams

Formalizes `G_alpha` in `eq:thin-domain` and the full row count in
`eq:thin-readings` of `shields-2026-skew-class-inflation.tex`.
Every block is the literal profile `E_m`; all joins retain both endpoint
rows and insert a genuine zero seam.  Sorry-free.
-/

namespace SkewClassInflation

/-- A literal zero join on the disjoint union of all positive row counts. -/
def ConnectedProfile.zeroJoin (D E : ConnectedProfile) : ConnectedProfile :=
  ⟨D.1 + E.1 + 1, Profile.zeroJoin D.2 E.2⟩

namespace ThinParameters

variable (B : ThinParameters)

/-- Join a nonempty positive block word in its original order, without replacing any inner. -/
def chain (a : ℕ) (ha : 0 < a) : (l : List ℕ) → (∀ k ∈ l, 0 < k) → ConnectedProfile
  | [], _ => ⟨a, B.innerPower a ha⟩
  | b :: l, h => ConnectedProfile.zeroJoin ⟨a, B.innerPower a ha⟩
      (chain b (h b List.mem_cons_self) l
        (fun k hk => h k (List.mem_cons_of_mem _ hk)))

/-- The full number of nonempty rows is the total copy multiplicity plus the outer length. -/
theorem chain_row_count (a : ℕ) (ha : 0 < a) (l : List ℕ) (h : ∀ k ∈ l, 0 < k) :
    (B.chain a ha l h).1 + 1 = a + l.sum + (l.length + 1) := by
  induction l generalizing a with
  | nil => simp [chain]
  | cons b l ih =>
    have hh := ih b (h b List.mem_cons_self)
      (fun k hk => h k (List.mem_cons_of_mem _ hk))
    simp only [chain, ConnectedProfile.zeroJoin, List.sum_cons, List.length_cons]
    omega

/-- Every actual thin chain is Hessenberg, including its zero joining seams. -/
theorem chain_thick (a : ℕ) (ha : 0 < a) (l : List ℕ) (h : ∀ k ∈ l, 0 < k) :
    SkewJacobiNegative.Staircase.Thick (B.chain a ha l h).2 := by
  induction l generalizing a with
  | nil => exact B.innerPower_thick a ha
  | cons b l ih =>
    exact Profile.zeroJoin_thick _ _ (B.innerPower_thick a ha)
      (ih b (h b List.mem_cons_self) (fun k hk => h k (List.mem_cons_of_mem _ hk)))

/-- The actual `G_alpha` attached to a positive composition, across its exact ordered block word. -/
def diagram {M : ℕ} (α : Composition M) (hM : 0 < M) : ConnectedProfile :=
  match he : α.blocks with
  | [] => False.elim (by have h := α.blocks_sum; rw [he] at h; simp only [List.sum_nil] at h; omega)
  | a :: l => B.chain a (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun k hk => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hk))

/-- The row count is produced by the concrete construction, not carried as a class assumption. -/
theorem diagram_row_count {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (B.diagram α hM).1 + 1 = M + α.length := by
  unfold diagram
  split
  · rename_i he
    have h := α.blocks_sum
    rw [he] at h
    simp only [List.sum_nil] at h
    omega
  · rename_i a l he
    have ha : 0 < a := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    have hl : ∀ k ∈ l, 0 < k :=
      fun k hk => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hk)
    have hs : a + l.sum = M := by simpa [he] using α.blocks_sum
    have hlen : α.length = l.length + 1 := by simp [Composition.length, he]
    have hh := B.chain_row_count a ha l hl
    exact hh.trans (by omega)

/-- No Hessenberg assumption is imposed on a mate; it is proved here for the source. -/
theorem diagram_thick {M : ℕ} (α : Composition M) (hM : 0 < M) :
    SkewJacobiNegative.Staircase.Thick (B.diagram α hM).2 := by
  unfold diagram
  split
  · rename_i he
    have h := α.blocks_sum
    rw [he] at h
    simp only [List.sum_nil] at h
    omega
  · rename_i a l he
    exact B.chain_thick a _ l _

/-- A singleton outer composition gives exactly one literal overlapped block. -/
theorem diagram_single (M : ℕ) (hM : 0 < M) :
    B.diagram (Composition.single M hM) hM = ⟨M, B.innerPower M hM⟩ := rfl

end ThinParameters
end SkewClassInflation
