/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CompositionCoarseningInventory
import SkewClassInflation.RibbonReversal

/-!
# Reflected cut types of actual equivalent compositions

The zero, single, and double cut types used in the ribbon factorization
input to `lem:overlap-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Their invariance follows from
exact two-part coarsening counts.  Nonreconstructibility supplies an
actual least single-type cut; it is not an additional assumed datum.
Sorry-free.
-/

namespace SkewClassInflation

/-- The number of actual cuts at a coordinate and its reflection, with midpoint doubling. -/
def compositionCutType {N : ℕ} (α : Composition N) (x : ℕ) : ℕ :=
  (if x ∈ properCuts α then 1 else 0) + (if N - x ∈ properCuts α then 1 else 0)

/-- Every coordinate has one of the three stated cut types. -/
theorem compositionCutType_le_two {N : ℕ} (α : Composition N) (x : ℕ) :
    compositionCutType α x ≤ 2 := by
  unfold compositionCutType
  split_ifs <;> decide

/-- Endpoint and exterior coordinates have type zero, including the empty-weight boundary. -/
theorem compositionCutType_outside {N : ℕ} (α : Composition N) (x : ℕ)
    (hx : x = 0 ∨ N ≤ x) : compositionCutType α x = 0 := by
  have hz : 0 ∉ properCuts α := by
    intro hm
    exact (Nat.lt_irrefl 0) (properCuts_bounds α 0 hm).1
  have hhigh : ∀ y, N ≤ y → y ∉ properCuts α := by
    intro y hy hm
    exact (Nat.not_lt_of_ge hy) (properCuts_bounds α y hm).2
  rcases hx with rfl | hx
  · simp only [compositionCutType, Nat.sub_zero, ite_eq_right hz,
      ite_eq_right (hhigh N le_rfl), zero_add]
  · simp only [compositionCutType, Nat.sub_eq_zero_of_le hx,
      ite_eq_right (hhigh x hx), ite_eq_right hz, zero_add]

/-- Type one means that exactly one of the two reflected cuts is present. -/
theorem compositionCutType_one_iff {N : ℕ} (α : Composition N) (x : ℕ) :
    compositionCutType α x = 1 ↔
      (x ∈ properCuts α ∧ N - x ∉ properCuts α) ∨
        (x ∉ properCuts α ∧ N - x ∈ properCuts α) := by
  classical
  by_cases hx : x ∈ properCuts α <;> by_cases hr : N - x ∈ properCuts α <;>
    simp [compositionCutType, hx, hr]

/-- Equal actual inventories preserve every cut type, including endpoints and the midpoint. -/
theorem coarseningInventory_cut_type {N : ℕ} (α β : Composition N)
    (he : coarseningInventory α = coarseningInventory β) (x : ℕ) :
    compositionCutType α x = compositionCutType β x := by
  by_cases hx : 0 < x ∧ x < N
  · let a : ℕ+ := ⟨x, hx.1⟩
    let b : ℕ+ := ⟨N - x, Nat.sub_pos_of_lt hx.2⟩
    have hs : a.val + b.val = N := Nat.add_sub_of_le hx.2.le
    have ha := coarseningInventory_two_cut_type α a b hs
    have hb := coarseningInventory_two_cut_type β a b hs
    rw [he] at ha
    exact ha.symm.trans hb
  · have hout : x = 0 ∨ N ≤ x := by omega
    rw [compositionCutType_outside α x hout, compositionCutType_outside β x hout]

/-- At every even-type coordinate, actual inventory equality fixes cut membership. -/
theorem coarseningInventory_cut_membership_of_not_one {N : ℕ} (α β : Composition N)
    (he : coarseningInventory α = coarseningInventory β) (x : ℕ)
    (hn : compositionCutType α x ≠ 1) :
    (x ∈ properCuts α ↔ x ∈ properCuts β) := by
  classical
  have ht := coarseningInventory_cut_type α β he x
  by_cases ha : x ∈ properCuts α
  · by_cases hb : x ∈ properCuts β
    · exact iff_of_true ha hb
    · simp only [compositionCutType, ite_eq_left ha, ite_eq_right hb] at ht hn
      split_ifs at ht hn <;> omega
  · by_cases hb : x ∈ properCuts β
    · simp only [compositionCutType, ite_eq_right ha, ite_eq_left hb] at ht hn
      split_ifs at ht hn <;> omega
    · exact iff_of_false ha hb

/-- With no single-type coordinate, the actual inventory reconstructs the complete composition. -/
theorem coarseningInventory_reconstruct_of_no_single {N : ℕ} (α β : Composition N)
    (hno : ∀ x, compositionCutType α x ≠ 1)
    (he : coarseningInventory α = coarseningInventory β) : α = β := by
  apply properCuts_injective
  ext x
  exact coarseningInventory_cut_membership_of_not_one α β he x (hno x)

/-- Reconstruction from the actual coarsening data up to whole-word reversal. -/
def ribbonReconstructible {N : ℕ} (α : Composition N) : Prop :=
  ∀ β : Composition N, coarseningInventory β = coarseningInventory α → β = α ∨ β = α.reverse

/-- A source without type-one cuts is reconstructible, with no reversal ambiguity left. -/
theorem ribbonReconstructible_of_no_single {N : ℕ} (α : Composition N)
    (hno : ∀ x, compositionCutType α x ≠ 1) : ribbonReconstructible α := by
  intro β hβ
  exact Or.inl (coarseningInventory_reconstruct_of_no_single α β hno hβ.symm).symm

/-- Failure of reconstruction supplies a genuine mate outside both literal orientations. -/
theorem exists_nonrotation_inventory_mate {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) :
    ∃ β : Composition N, coarseningInventory β = coarseningInventory α ∧
      β ≠ α ∧ β ≠ α.reverse := by
  classical
  by_contra hnone
  apply hn
  intro β hβ
  by_cases he : β = α
  · exact Or.inl he
  · by_cases hr : β = α.reverse
    · exact Or.inr hr
    · exact (hnone ⟨β, hβ, he, hr⟩).elim

/-- A nonreconstructible source necessarily has an actual single-type coordinate. -/
theorem exists_single_cut_of_not_reconstructible {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) : ∃ x, compositionCutType α x = 1 := by
  classical
  by_contra hnone
  apply hn
  apply ribbonReconstructible_of_no_single
  intro x hx
  exact hnone ⟨x, hx⟩

/-- The first type-one coordinate is actual, proper, and least, rather than assumed. -/
theorem exists_first_single_cut {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) :
    ∃ k, 0 < k ∧ k < N ∧ compositionCutType α k = 1 ∧
      ∀ j < k, compositionCutType α j ≠ 1 := by
  classical
  have hex := exists_single_cut_of_not_reconstructible α hn
  let k := Nat.find hex
  have hk : compositionCutType α k = 1 := Nat.find_spec hex
  have hproper : 0 < k ∧ k < N := by
    by_contra hbad
    have hout : k = 0 ∨ N ≤ k := by omega
    have hz := compositionCutType_outside α k hout
    omega
  exact ⟨k, hproper.1, hproper.2, hk, fun j hj => Nat.find_min hex hj⟩

/-- Actual composition reversal reflects every coordinate in the true full weight interval. -/
theorem properCuts_reverse_iff {N : ℕ} (α : Composition N) (x : ℕ) (hx : x ≤ N) :
    x ∈ properCuts α.reverse ↔ N - x ∈ properCuts α := by
  rw [← wordProperCuts_blocks α.reverse, Composition.reverse_blocks]
  have hh := wordProperCuts_reverse_reflect α.blocks x (by rw [α.blocks_sum]; exact hx)
  simpa only [α.blocks_sum, wordProperCuts_blocks α] using hh

/-- Whole-word reversal preserves the actual inventory, including the empty unit composition. -/
theorem coarseningInventory_reverse {N : ℕ} (α : Composition N) :
    coarseningInventory α.reverse = coarseningInventory α := by
  by_cases hN : 0 < N
  · exact (ribbon_eq_iff_coarseningInventory α.reverse α hN hN).mp
      (ribbonWord_reverse α hN)
  · have hzero : N = 0 := by omega
    subst N
    have hn : α.blocks = [] := α.blocks_eq_nil.mpr rfl
    have hr : α.reverse = α := by
      apply Composition.ext
      simp only [Composition.reverse_blocks, hn, List.reverse_nil]
    rw [hr]

/-- Reconstructibility from actual data is unchanged by reversing the given source. -/
theorem ribbonReconstructible_reverse_iff {N : ℕ} (α : Composition N) :
    ribbonReconstructible α.reverse ↔ ribbonReconstructible α := by
  constructor
  · intro hr β hβ
    have hh := hr β (hβ.trans (coarseningInventory_reverse α).symm)
    rcases hh with hh | hh
    · exact Or.inr hh
    · exact Or.inl (by simpa only [Composition.reverse_reverse] using hh)
  · intro hr β hβ
    have hh := hr β (hβ.trans (coarseningInventory_reverse α))
    rcases hh with hh | hh
    · exact Or.inr (by simpa only [Composition.reverse_reverse] using hh)
    · exact Or.inl hh

/-- A single-type coordinate supplies an actual orientation with that cut present. -/
theorem inventory_oriented_of_type_one {N : ℕ} (α : Composition N) (k : ℕ)
    (hk : compositionCutType α k = 1) :
    ∃ γ : Composition N, (γ = α ∨ γ = α.reverse) ∧
      coarseningInventory γ = coarseningInventory α ∧
      k ∈ properCuts γ ∧ N - k ∉ properCuts γ := by
  rcases (compositionCutType_one_iff α k).mp hk with ⟨hc, hcr⟩ | ⟨hc, hcr⟩
  · exact ⟨α, Or.inl rfl, rfl, hc, hcr⟩
  · have hb := properCuts_bounds α (N - k) hcr
    have hkn : k ≤ N := by omega
    have hrk : k ∈ properCuts α.reverse := (properCuts_reverse_iff α k hkn).mpr hcr
    have hrn : N - k ∉ properCuts α.reverse := by
      intro hm
      have hh := (properCuts_reverse_iff α (N - k) (Nat.sub_le _ _)).mp hm
      have hkk : N - (N - k) = k := by omega
      rw [hkk] at hh
      exact hc hh
    exact ⟨α.reverse, Or.inr rfl, coarseningInventory_reverse α, hrk, hrn⟩

/-- A normalized single source cut supplies a normalized orientation of every actual mate. -/
theorem inventory_mate_oriented_at_cut {N : ℕ} (α β : Composition N) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α)
    (he : coarseningInventory β = coarseningInventory α) :
    ∃ γ : Composition N, (γ = β ∨ γ = β.reverse) ∧
      coarseningInventory γ = coarseningInventory α ∧
      k ∈ properCuts γ ∧ N - k ∉ properCuts γ := by
  classical
  have hα : compositionCutType α k = 1 := by simp only [compositionCutType,
    ite_eq_left hk, ite_eq_right hkr, add_zero]
  have hβ : compositionCutType β k = 1 := (coarseningInventory_cut_type β α he k).trans hα
  obtain ⟨γ, hγ, hInv, hkγ, hkrγ⟩ := inventory_oriented_of_type_one β k hβ
  exact ⟨γ, hγ, hInv.trans he, hkγ, hkrγ⟩

/-- Nonreconstructibility produces a normalized source and its actual least single-type cut. -/
theorem exists_normalized_first_single_cut {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) :
    ∃ γ : Composition N, ∃ k : ℕ, (γ = α ∨ γ = α.reverse) ∧
      coarseningInventory γ = coarseningInventory α ∧ ¬ ribbonReconstructible γ ∧
      0 < k ∧ k < N ∧ compositionCutType γ k = 1 ∧
      k ∈ properCuts γ ∧ N - k ∉ properCuts γ ∧
      ∀ j < k, compositionCutType γ j ≠ 1 := by
  obtain ⟨k, hk0, hkN, hk, hmin⟩ := exists_first_single_cut α hn
  obtain ⟨γ, hγ, hInv, hcut, href⟩ := inventory_oriented_of_type_one α k hk
  refine ⟨γ, k, hγ, hInv, ?_, hk0, hkN, ?_, hcut, href, ?_⟩
  · rcases hγ with he | he
    · rw [he]
      exact hn
    · rw [he]
      exact fun h => hn ((ribbonReconstructible_reverse_iff α).mp h)
  · exact (coarseningInventory_cut_type γ α hInv k).trans hk
  · intro j hj he
    have hh := coarseningInventory_cut_type γ α hInv j
    exact hmin j hj (hh.symm.trans he)

/-- A nonrotation mate can be oriented at the source cut without becoming a source rotation. -/
theorem exists_oriented_nonrotation_mate {N : ℕ} (α : Composition N)
    (hn : ¬ ribbonReconstructible α) (k : ℕ)
    (hk : k ∈ properCuts α) (hkr : N - k ∉ properCuts α) :
    ∃ β : Composition N, coarseningInventory β = coarseningInventory α ∧
      k ∈ properCuts β ∧ N - k ∉ properCuts β ∧ β ≠ α ∧ β ≠ α.reverse := by
  obtain ⟨β, hInv, hne, hnr⟩ := exists_nonrotation_inventory_mate α hn
  obtain ⟨γ, hγ, hEq, hcut, href⟩ := inventory_mate_oriented_at_cut α β k hk hkr hInv
  refine ⟨γ, hEq, hcut, href, ?_, ?_⟩
  · intro he
    rcases hγ with hh | hh
    · exact hne (hh.symm.trans he)
    · have hr := congrArg Composition.reverse (hh.symm.trans he)
      exact hnr (by simpa only [Composition.reverse_reverse] using hr)
  · intro he
    rcases hγ with hh | hh
    · exact hnr (hh.symm.trans he)
    · have hr := congrArg Composition.reverse (hh.symm.trans he)
      exact hne (by simpa only [Composition.reverse_reverse] using hr)

end SkewClassInflation
