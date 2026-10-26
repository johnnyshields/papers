/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CoarseningTwoParts

/-!
# Actual coarsening inventories on canonical compositions

The composition-level interface to `eq:ribbon-coarsening` of
`shields-2026-skew-class-inflation.tex`.  Nonempty compositions use
exactly the already constructed positive row masks.  Word congruence
proves representation independence; no abstract replacement for the
actual multiplicity data is introduced.  Sorry-free.
-/

namespace SkewClassInflation

/-- The actual positive coarsening inventory of a canonical composition, with the empty unit. -/
noncomputable def coarseningInventory {N : ℕ} (α : Composition N) : Multiset (Multiset ℕ+) :=
  match he : α.blocks with
  | [] => {0}
  | a :: l =>
    let ha : 0 < a := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    let hl : ∀ b ∈ l, 0 < b := fun b hb =>
      α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hb)
    let R := ribbonRows a ha l hl
    coarseningPartitions R.r R.r_pos

/-- An actual empty source has exactly its empty coarsening unit. -/
theorem coarseningInventory_of_nil {N : ℕ} (α : Composition N) (he : α.blocks = []) :
    coarseningInventory α = {0} := by
  unfold coarseningInventory
  split
  · rfl
  · rename_i a l hblocks
    rw [he] at hblocks
    cases hblocks

/-- Equal actual words give the same inventory, independently of indexed total weights. -/
theorem coarseningInventory_eq_of_blocks_eq {M N : ℕ}
    (α : Composition M) (β : Composition N) (he : α.blocks = β.blocks) :
    coarseningInventory α = coarseningInventory β := by
  have hh : (⟨M, α⟩ : (K : ℕ) × Composition K) = ⟨N, β⟩ :=
    Composition.sigma_eq_iff_blocks_eq.mpr he
  exact congrArg (fun D : (K : ℕ) × Composition K => coarseningInventory D.2) hh

/-- Every nonempty canonical composition supplies a concrete positive finite row vector. -/
theorem exists_positive_row_word {N : ℕ} (α : Composition N) (hN : 0 < N) :
    ∃ n : ℕ, ∃ r : Fin (n + 1) → ℕ, (∀ i, 0 < r i) ∧ List.ofFn r = α.blocks := by
  cases he : α.blocks with
  | nil =>
    have hh := α.blocks_sum
    rw [he, List.sum_nil] at hh
    omega
  | cons a l =>
    let ha : 0 < a := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    let hl : ∀ b ∈ l, 0 < b := fun b hb =>
      α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hb)
    let R := ribbonRows a ha l hl
    exact ⟨l.length, R.r, R.r_pos, ribbonRows_word a ha l hl⟩

/-- The composition interface is the original mask inventory of every positive row vector. -/
theorem coarseningInventory_rowComposition {n : ℕ} (r : Fin (n + 1) → ℕ)
    (hr : ∀ i, 0 < r i) :
    coarseningInventory (rowComposition r hr) = coarseningPartitions r hr := by
  unfold coarseningInventory
  split
  · rename_i he
    have hh := congrArg List.length he
    change (List.ofFn r).length = 0 at hh
    rw [List.length_ofFn] at hh
    omega
  · rename_i a l he
    let ha : 0 < a := (rowComposition r hr).blocks_pos
      (by rw [he]; exact List.mem_cons_self)
    let hl : ∀ b ∈ l, 0 < b := fun b hb => (rowComposition r hr).blocks_pos
      (by rw [he]; exact List.mem_cons_of_mem _ hb)
    let R := ribbonRows a ha l hl
    change coarseningPartitions R.r R.r_pos = coarseningPartitions r hr
    apply coarseningPartitions_eq_of_row_word_eq R.r r R.r_pos hr
    change List.ofFn (ribbonRows a ha l hl).r = List.ofFn r
    rw [ribbonRows_word]
    exact he.symm

/-- Every positive finite word representation has the same actual inventory as its composition. -/
theorem coarseningInventory_eq_of_row_word {N n : ℕ} (α : Composition N)
    (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) (he : List.ofFn r = α.blocks) :
    coarseningInventory α = coarseningPartitions r hr :=
  (coarseningInventory_eq_of_blocks_eq α (rowComposition r hr) he.symm).trans
    (coarseningInventory_rowComposition r hr)

/-- Canonical nonempty ribbon equality is exactly equality of the actual coarsening inventories. -/
theorem ribbon_eq_iff_coarseningInventory {M N : ℕ}
    (α : Composition M) (β : Composition N) (hM : 0 < M) (hN : 0 < N) :
    ribbonWord α.blocks = ribbonWord β.blocks ↔ coarseningInventory α = coarseningInventory β := by
  obtain ⟨n, r, hr, hα⟩ := exists_positive_row_word α hM
  obtain ⟨m, s, hs, hβ⟩ := exists_positive_row_word β hN
  rw [coarseningInventory_eq_of_row_word α r hr hα,
    coarseningInventory_eq_of_row_word β s hs hβ, ← hα, ← hβ]
  exact ribbon_eq_iff_coarseningPartitions r s hr hs

/-- Exact two-part composition multiplicity, with no midpoint duplication. -/
theorem coarseningInventory_count_pair {N : ℕ} (α : Composition N) (a b : ℕ+)
    (hsum : a.val + b.val = N) :
    (coarseningInventory α).count (a ::ₘ b ::ₘ 0) =
      if a = b then (if a.val ∈ properCuts α then 1 else 0)
      else (if a.val ∈ properCuts α then 1 else 0) +
        (if b.val ∈ properCuts α then 1 else 0) := by
  have hN : 0 < N := by have := a.pos; omega
  obtain ⟨n, r, hr, hα⟩ := exists_positive_row_word α hN
  have hw : (∑ i, r i) = N := by
    have hh := congrArg List.sum hα
    simpa only [List.sum_ofFn, α.blocks_sum] using hh
  have hs : a.val + b.val = ∑ i, r i := hsum.trans hw.symm
  have hc : properCuts (rowComposition r hr) = properCuts α :=
    properCuts_eq_of_blocks_eq (rowComposition r hr) α hα
  rw [coarseningInventory_eq_of_row_word α r hr hα,
    coarseningPartitions_count_pair r hr a b hs, hc]

/-- The canonical two-part multiplicity gives the reflected-cut count in both midpoint regimes. -/
theorem coarseningInventory_two_cut_type {N : ℕ} (α : Composition N) (a b : ℕ+)
    (hsum : a.val + b.val = N) :
    (if a = b then 2 else 1) * (coarseningInventory α).count (a ::ₘ b ::ₘ 0) =
      (if a.val ∈ properCuts α then 1 else 0) + (if b.val ∈ properCuts α then 1 else 0) := by
  classical
  rw [coarseningInventory_count_pair α a b hsum]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, two_mul]
  · simp only [ite_eq_right hab, one_mul]

end SkewClassInflation
