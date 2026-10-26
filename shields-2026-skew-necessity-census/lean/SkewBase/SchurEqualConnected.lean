import SkewBase.RowOverlaps

/-!
# A diagram Schur-equal to a connected diagram is connected, of the same area

Formalizes `shields-2026-skew-base-computational.tex`, `lem:invariants`: let `F` be connected and
`s_H = s_F`; then `H` is connected and `|H| = |F|`.

`H` is any skew diagram with rows `i < ℓ`, some possibly empty (`BetaRows`).  The paper obtains
connectedness from the factorization of `s_H` over its components and the irreducibility of the
skew Schur function of a connected diagram.  Here it comes from the row overlap partitions
(`rowOverlaps_eq_of_schur_eq`): `ρ^{(1)}` counts the nonempty rows and `ρ^{(2)}` counts the pairs of
adjacent rows sharing a column, and a set of `n + 1` nonempty rows with `n` such pairs is a run of
consecutive rows, each sharing a column with the next.  This is connectedness of the diagram (a
skew diagram is connected exactly when its nonempty rows are consecutive and adjacent rows share a
column), and no irreducibility is used.  The area is the sum of the row lengths, `ρ^{(1)}`.

Sorry-free.
-/

namespace SkewBase

open SkewGluing

namespace BetaRows

variable {ℓ : ℕ}

theorem card_rowOverlaps (B : BetaRows ℓ) (k : ℕ) :
    (B.rowOverlaps k).card =
      ((Finset.range (ℓ - (k - 1))).filter fun i => 0 < B.overlap (k - 1) i).card := by
  unfold rowOverlaps overlaps
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- The rows of the diagram that are nonempty. -/
def nonemptyRows (B : BetaRows ℓ) : Finset ℕ :=
  (Finset.range ℓ).filter fun i => B.zeta i < B.xi i

/-- The positions `i` where the rows `i` and `i + 1` share a column. -/
def overlappingPairs (B : BetaRows ℓ) : Finset ℕ :=
  (Finset.range (ℓ - 1)).filter fun i => 0 < B.overlap 1 i

theorem card_nonemptyRows (B : BetaRows ℓ) : B.nonemptyRows.card = (B.rowOverlaps 1).card := by
  rw [card_rowOverlaps, nonemptyRows]
  simp only [Nat.sub_self, Nat.sub_zero]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp only [overlap, Nat.cast_zero, add_zero]
  omega

theorem card_overlappingPairs (B : BetaRows ℓ) :
    B.overlappingPairs.card = (B.rowOverlaps 2).card := by
  rw [card_rowOverlaps, overlappingPairs]

theorem mem_nonemptyRows_of_mem_overlappingPairs (B : BetaRows ℓ) {i : ℕ}
    (h : i ∈ B.overlappingPairs) : i ∈ B.nonemptyRows ∧ i + 1 ∈ B.nonemptyRows := by
  rw [overlappingPairs, Finset.mem_filter, Finset.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  simp only [overlap] at h2
  simp only [nonemptyRows, Finset.mem_filter, Finset.mem_range]
  have a1 := B.zeta_lt i (i + 1) (by omega) (by omega)
  have a2 := B.xi_lt i (i + 1) (by omega) (by omega)
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

end BetaRows

/-- A set of `n + 1` naturals with `n` elements `i` such that `i` and `i + 1` both belong to it is
an interval, and those `n` elements are all but its last. -/
theorem finset_run_of_card (S E : Finset ℕ) (n : ℕ) (hS : S.card = n + 1)
    (hE : ∀ i ∈ E, i ∈ S ∧ i + 1 ∈ S) (hcard : E.card = n) :
    ∃ a, S = Finset.Icc a (a + n) ∧ E = Finset.Ico a (a + n) := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set m := S.max' hne with hm
  set a := S.min' hne with ha
  have hmS : m ∈ S := Finset.max'_mem S hne
  have haS : a ∈ S := Finset.min'_mem S hne
  have hEsub : E ⊆ S.erase m := by
    intro i hi
    obtain ⟨h1, h2⟩ := hE i hi
    refine Finset.mem_erase.mpr ⟨?_, h1⟩
    intro h
    have := Finset.le_max' S (i + 1) h2
    omega
  have hcardE : (S.erase m).card = n := by
    rw [Finset.card_erase_of_mem hmS]; omega
  have hEeq : E = S.erase m := Finset.eq_of_subset_of_card_le hEsub (by omega)
  have hsucc : ∀ i ∈ S, i < m → i + 1 ∈ S := by
    intro i hi him
    have : i ∈ E := by rw [hEeq]; exact Finset.mem_erase.mpr ⟨by omega, hi⟩
    exact (hE i this).2
  have hall : ∀ c, a ≤ c → c ≤ m → c ∈ S := by
    intro c hac
    induction c, hac using Nat.le_induction with
    | base => intro _; exact haS
    | succ c hac ih =>
      intro hcm
      exact hsucc c (ih (by omega)) (by omega)
  have hSeq : S = Finset.Icc a m := by
    ext c
    simp only [Finset.mem_Icc]
    constructor
    · intro hc
      exact ⟨Finset.min'_le S c hc, Finset.le_max' S c hc⟩
    · rintro ⟨h1, h2⟩
      exact hall c h1 h2
  have ham : a ≤ m := Finset.min'_le S m hmS
  have hcardS : S.card = m + 1 - a := by rw [hSeq, Nat.card_Icc]
  have hmn : m = a + n := by omega
  refine ⟨a, ?_, ?_⟩
  · rw [hSeq, hmn]
  · rw [hEeq, hSeq, hmn]
    ext c
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ico]
    omega

end SkewBase

namespace SkewGluing.Profile

open SkewBase

variable {n : ℕ}

/-- The row overlaps `ρ^{(1)}` of the diagram of a profile are its row lengths. -/
theorem rowOverlaps_one_toBetaRows (F : Profile n) :
    F.toBetaRows.rowOverlaps 1 = F.rowMultiset := by
  rw [BetaRows.rowOverlaps, ← rowOverlapPartition, rowOverlapPartition_one]
  refine Multiset.filter_eq_self.mpr fun a ha => ?_
  obtain ⟨i, rfl⟩ := mem_rowMultiset.mp ha
  exact F.r_pos i

/-- The row overlaps `ρ^{(2)}` of the diagram of a profile are its gaps plus one. -/
theorem rowOverlaps_two_toBetaRows (F : Profile n) :
    F.toBetaRows.rowOverlaps 2 = F.gapMultiset.map (· + 1) := by
  rw [BetaRows.rowOverlaps, ← rowOverlapPartition, rowOverlapPartition_two]
  refine Multiset.filter_eq_self.mpr fun a ha => ?_
  obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp ha
  omega

theorem card_rowOverlaps_one (F : Profile n) : (F.toBetaRows.rowOverlaps 1).card = n + 1 := by
  rw [rowOverlaps_one_toBetaRows, rowMultiset, Multiset.card_map]
  simp

theorem card_rowOverlaps_two (F : Profile n) : (F.toBetaRows.rowOverlaps 2).card = n := by
  rw [rowOverlaps_two_toBetaRows, Multiset.card_map, gapMultiset, Multiset.card_map]
  simp

end SkewGluing.Profile

namespace SkewBase

open SkewGluing

namespace BetaRows

variable {ℓ : ℕ}

/-- **`lem:invariants`, connectedness and area.**  A skew diagram `H` with `s_H = s_F` for a
connected `F` with `n + 1` rows has exactly `n + 1` nonempty rows, they are consecutive
(`a, …, a + n`), and every two adjacent ones share a column: `H` is connected. -/
theorem connected_of_schur_eq {n : ℕ} (F : Profile n) (B : BetaRows ℓ)
    (h : B.schur = F.schur) :
    ∃ a, a + n < ℓ ∧ (∀ i, i < ℓ → (B.zeta i < B.xi i ↔ a ≤ i ∧ i ≤ a + n)) ∧
      ∀ j, j < n → 0 < B.overlap 1 (a + j) := by
  have hF : B.schur = F.toBetaRows.schur := by rw [Profile.toBetaRows_schur]; exact h
  have h1 := rowOverlaps_eq_of_schur_eq ℓ (n + 1) B F.toBetaRows hF 1
  have h2 := rowOverlaps_eq_of_schur_eq ℓ (n + 1) B F.toBetaRows hF 2
  have c1 : B.nonemptyRows.card = n + 1 := by
    rw [card_nonemptyRows, h1, Profile.card_rowOverlaps_one]
  have c2 : B.overlappingPairs.card = n := by
    rw [card_overlappingPairs, h2, Profile.card_rowOverlaps_two]
  obtain ⟨a, hS, hE⟩ := finset_run_of_card B.nonemptyRows B.overlappingPairs n c1
    (fun i hi => B.mem_nonemptyRows_of_mem_overlappingPairs hi) c2
  have hmem : a + n ∈ B.nonemptyRows := by rw [hS]; simp
  have hlt : a + n < ℓ := by
    simp only [nonemptyRows, Finset.mem_filter, Finset.mem_range] at hmem
    exact hmem.1
  refine ⟨a, hlt, fun i hi => ?_, fun j hj => ?_⟩
  · have : i ∈ B.nonemptyRows ↔ a ≤ i ∧ i ≤ a + n := by
      rw [hS, Finset.mem_Icc]
    simp only [nonemptyRows, Finset.mem_filter, Finset.mem_range] at this
    constructor
    · intro hz; exact this.mp ⟨hi, hz⟩
    · intro hr; exact (this.mpr hr).2
  · have : a + j ∈ B.overlappingPairs := by rw [hE]; simp; omega
    simp only [overlappingPairs, Finset.mem_filter] at this
    exact this.2

/-- **`lem:invariants`, area.**  Schur-equal diagrams have the same number of cells. -/
theorem area_eq_of_schur_eq {ℓ' : ℕ} {B : BetaRows ℓ} {B' : BetaRows ℓ'}
    (h : B.schur = B'.schur) :
    ∑ i ∈ Finset.range ℓ, (B.xi i - B.zeta i).toNat =
      ∑ i ∈ Finset.range ℓ', (B'.xi i - B'.zeta i).toNat := by
  have key : ∀ {k : ℕ} (C : BetaRows k),
      ∑ i ∈ Finset.range k, (C.xi i - C.zeta i).toNat = (C.rowOverlaps 1).sum := by
    intro k C
    rw [rowOverlaps, overlaps]
    simp only [Nat.sub_self, Nat.sub_zero]
    set M := (Finset.range k).val.map (C.overlap 0) with hM
    have hz : ((M).filter fun a => ¬ 0 < a).sum = 0 :=
      Multiset.sum_eq_zero fun x hx => by
        have := (Multiset.mem_filter.mp hx).2
        omega
    have := congrArg Multiset.sum (Multiset.filter_add_not (fun a => 0 < a) M)
    rw [Multiset.sum_add, hz, add_zero] at this
    rw [this, hM, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [overlap]
  rw [key, key, rowOverlaps_eq_of_schur_eq ℓ ℓ' B B' h 1]

/-- A skew diagram Schur-equal to a connected `F` has the area of `F`. -/
theorem area_eq_of_schur_eq_profile {n : ℕ} (F : Profile n) (B : BetaRows ℓ)
    (h : B.schur = F.schur) :
    ∑ i ∈ Finset.range ℓ, (B.xi i - B.zeta i).toNat = ∑ i, F.r i := by
  have := area_eq_of_schur_eq (B := B) (B' := F.toBetaRows)
    (by rw [Profile.toBetaRows_schur]; exact h)
  rw [this, ← Fin.sum_univ_eq_sum_range (fun i => (F.toBetaRows.xi i - F.toBetaRows.zeta i).toNat)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := F.xi_sub_zeta i
  rw [Profile.toBetaRows_xi, Profile.toBetaRows_zeta]
  omega

end BetaRows

end SkewBase
