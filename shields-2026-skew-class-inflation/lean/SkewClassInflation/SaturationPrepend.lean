/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationSourceData
import SkewClassInflation.ProfileMergeInverse

/-!
# Literal prepend identities for general repeated-inner sources

The source-assembly identities used by `lem:total-contraction-inverse`
of `shields-2026-skew-class-inflation.tex`.  Joining bounds are supplied
by the actual source row bounds.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- A single outer part is exactly its full actual inner power. -/
theorem diagram_single (m : ℕ) (hm : 0 < m) :
    A.diagram (Composition.single m hm) hm = ⟨m * A.k, A.power m hm⟩ := rfl

/-- A proved nonempty outer word identifies the actual source with its literal chain. -/
theorem diagram_eq_chain {M : ℕ} (α : Composition M) (hM : 0 < M)
    (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b)
    (he : α.blocks = a :: l) : A.diagram α hM = A.chain a ha l hl := by
  unfold diagram
  split
  · rename_i hnil
    rw [he] at hnil
    cases hnil
  · rename_i b q hbq
    have hh := List.cons.inj (he.symm.trans hbq)
    obtain ⟨rfl, rfl⟩ := hh
    rfl

/-- The nonempty tail supplies the literal joined source behind one fixed first power. -/
theorem chain_blocks {m M : ℕ} (hm : 0 < m) (α : Composition M) (hM : 0 < M) :
    A.chain m hm α.blocks (fun _ h => α.blocks_pos h) =
      ⟨m * A.k + (A.diagram α hM).1 + 1,
        Profile.join (A.power m hm) (A.diagram α hM).2 A.d
          (A.power_rows_above_seam m hm _) (A.diagram_rows_above_seam α hM _)⟩ := by
  have hex : ∃ a l, α.blocks = a :: l := by
    cases he : α.blocks with
    | nil =>
      have hs := α.blocks_sum
      rw [he] at hs
      simp only [List.sum_nil] at hs
      omega
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨a, l, he⟩ := hex
  have hdiag := A.diagram_eq_chain α hM a
    (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
    (fun b hb => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hb)) he
  have htail : A.d < (A.chain a
      (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun b hb => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hb))).2.r 0 := by
    rw [A.chain_first]
    have := A.first_bound
    omega
  have hjoin := Profile.join_right_congr (A.power m hm) (A.diagram α hM)
    (A.chain a (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun b hb => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hb))) A.d
    (A.power_rows_above_seam m hm _) (A.diagram_rows_above_seam α hM _) htail hdiag
  apply Eq.trans _ hjoin.symm
  simp only [he]
  rfl

/-- Prepending an outer part is the literal larger-seam join of its power with the old source. -/
theorem diagram_prepend {m M : ℕ} (hm : 0 < m) (α : Composition M) (hM : 0 < M) :
    A.diagram ((Composition.single m hm).append α) (by omega) =
      ⟨m * A.k + (A.diagram α hM).1 + 1,
        Profile.join (A.power m hm) (A.diagram α hM).2 A.d
          (A.power_rows_above_seam m hm _) (A.diagram_rows_above_seam α hM _)⟩ := by
  change A.chain m hm α.blocks (fun _ h => α.blocks_pos h) = _
  exact A.chain_blocks hm α hM

end SkewClassInflation.SaturationInner
