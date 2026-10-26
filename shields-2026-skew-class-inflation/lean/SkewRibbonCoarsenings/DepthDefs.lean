/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/DepthDefs.lean
import SkewRibbonCoarsenings.LiftIdentity
import SkewRibbonCoarsenings.LowOrder

/-!
# First distinguishing depth and the cumulative optimum

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:depth` (`eq:depth-defs`).

`dep n β γ` is the least number of parts of a partition `λ ⊢ n` with `m_β(λ) ≠ m_γ(λ)`;
`depthEq n` is the maximum of `dep` over unequal pairs of compositions of weight `n` (an empty
maximum is `0`), and `cumDepth N` is the maximum of `depthEq n` over `1 ≤ n ≤ N`.  Compositions of
weight `n` are the subsets of `Finset.Ioo 0 n`, so both maxima are `Finset.sup`s.  The bridge
lemmas identify `dep ≥ s` with the absence of monomials of ordinary degree `< s` in the
difference of the coarsening polynomials.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open MvPolynomial Finset

/-! ### Monomials of weight `n` are partitions of `n` -/

lemma posParts_map_val (m : Multiset ℕ+) :
    posParts (m.map (fun x : ℕ+ => (x : ℕ))) = m := by
  induction m using Multiset.induction with
  | empty => simp [posParts]
  | cons a m ih =>
    rw [Multiset.map_cons, posParts_cons_pos a.pos, ih]
    congr 1

lemma weight_hgen_eq_sum (d : ℕ+ →₀ ℕ) :
    Finsupp.weight hgenWeight d =
      ((Finsupp.toMultiset d).map (fun x : ℕ+ => (x : ℕ))).sum := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, Multiset.map_add, Multiset.sum_add, hf, hg]
  | single a b =>
    simp [Finsupp.weight_apply, hgenWeight, Finsupp.toMultiset_single, Multiset.map_nsmul,
      Multiset.sum_nsmul]

/-- A monomial of weight `n` in the `h_j` is `h_λ` for a partition `λ ⊢ n` whose number of parts is
the ordinary degree of the monomial. -/
lemma exists_partition_of_weight {n : ℕ} {d : ℕ+ →₀ ℕ}
    (hd : Finsupp.weight hgenWeight d = n) :
    ∃ P : n.Partition, Multiset.toFinsupp (posParts P.parts) = d ∧
      Multiset.card P.parts = Finsupp.degree d := by
  classical
  let lam : Multiset ℕ := (Finsupp.toMultiset d).map (fun x : ℕ+ => (x : ℕ))
  have hpos : ∀ i ∈ lam, 0 < i := by
    intro i hi
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hi
    exact x.pos
  have hsum : lam.sum = n := by
    rw [← hd, weight_hgen_eq_sum]
  refine ⟨⟨lam, fun {i} hi => hpos i hi, hsum⟩, ?_, ?_⟩
  · change Multiset.toFinsupp (posParts lam) = d
    rw [posParts_map_val, Finsupp.toMultiset_toFinsupp]
  · change Multiset.card lam = _
    rw [Multiset.card_map]
    conv_rhs => rw [← Finsupp.toMultiset_toFinsupp d, degree_toFinsupp]

/-! ### The bridge between truncation and partitions -/

/-- `G_β - G_γ` has no monomial of ordinary degree `< s` exactly when `m_β(λ) = m_γ(λ)` for every
partition `λ ⊢ n` with fewer than `s` parts. -/
theorem ordGE_G_sub_iff {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') {s : ℕ} :
    ordGE s (G n S - G n S') ↔
      ∀ P : n.Partition, Multiset.card P.parts < s → mult n S P.parts = mult n S' P.parts := by
  constructor
  · intro h P hP
    have hpos : ∀ x ∈ P.parts, 0 < x := fun x hx => P.parts_pos hx
    have hc := h (Multiset.toFinsupp (posParts P.parts)) (by
      rw [degree_toFinsupp, card_posParts hpos]; exact hP)
    rw [MvPolynomial.coeff_sub, coeff_G hn hS _ hpos, coeff_G hn hS' _ hpos] at hc
    omega
  · intro h d hd
    by_cases hw : Finsupp.weight hgenWeight d = n
    · obtain ⟨P, rfl, hcard⟩ := exists_partition_of_weight hw
      have hpos : ∀ x ∈ P.parts, 0 < x := fun x hx => P.parts_pos hx
      rw [MvPolynomial.coeff_sub, coeff_G hn hS _ hpos, coeff_G hn hS' _ hpos,
        h P (by omega)]
      simp
    · rw [MvPolynomial.coeff_sub, (G_isWeightedHomogeneous hS).coeff_eq_zero d hw,
        (G_isWeightedHomogeneous hS').coeff_eq_zero d hw, sub_zero]

/-- Equal coarsening polynomials are exactly equal multiplicities at every partition of `n`. -/
theorem G_eq_iff_mult {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') :
    G n S = G n S' ↔ ∀ P : n.Partition, mult n S P.parts = mult n S' P.parts := by
  constructor
  · intro h P
    have h0 : ordGE (Multiset.card P.parts + 1) (G n S - G n S') := by
      rw [h, sub_self]; exact ordGE_zero _
    exact (ordGE_G_sub_iff hn hS hS').mp h0 P (by omega)
  · intro h
    rw [← sub_eq_zero]
    ext d
    have := (ordGE_G_sub_iff hn hS hS' (s := Finsupp.degree d + 1)).mpr (fun P _ => h P) d
      (by omega)
    simpa using this

/-! ### The depth, `D_=`, and `C` of `eq:depth-defs` -/

/-- `eq:depth-defs`: the first distinguishing depth
`dep(β,γ) = min {ℓ(λ) : m_β(λ) ≠ m_γ(λ)}`, the minimum over partitions `λ ⊢ n`; it is `0` when no
partition distinguishes (`G_β = G_γ`), a case in which the paper does not define it. -/
noncomputable def dep (n : ℕ) (S S' : Finset ℕ) : ℕ :=
  sInf {k | ∃ P : n.Partition, mult n S P.parts ≠ mult n S' P.parts ∧
    Multiset.card P.parts = k}

open Classical in
/-- `eq:depth-defs`: `D_=(n)`, the maximum of `dep(β,γ)` over compositions `β, γ` of weight `n`
(subsets of `{1, …, n-1}`) with `G_β ≠ G_γ`; the empty maximum is `0`. -/
noncomputable def depthEq (n : ℕ) : ℕ :=
  (((Finset.Ioo 0 n).powerset ×ˢ (Finset.Ioo 0 n).powerset).filter
    fun p => G n p.1 ≠ G n p.2).sup fun p => dep n p.1 p.2

/-- `eq:depth-defs`: `C(N) = max_{1 ≤ n ≤ N} D_=(n)`. -/
noncomputable def cumDepth (N : ℕ) : ℕ := (Finset.Icc 1 N).sup depthEq

/-- `eq:depth-defs`: `dep` is witnessed by a partition with exactly `dep` parts at which the
multiplicities differ, whenever the inventories are unequal. -/
theorem dep_witness {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') (h : G n S ≠ G n S') :
    ∃ P : n.Partition, mult n S P.parts ≠ mult n S' P.parts ∧
      Multiset.card P.parts = dep n S S' := by
  have hne : ∃ P : n.Partition, mult n S P.parts ≠ mult n S' P.parts := by
    by_contra hcon
    push Not at hcon
    exact h ((G_eq_iff_mult hn hS hS').mpr hcon)
  obtain ⟨P, hP⟩ := hne
  have hmem := Nat.sInf_mem (s := {k | ∃ P : n.Partition, mult n S P.parts ≠ mult n S' P.parts ∧
    Multiset.card P.parts = k}) ⟨_, P, hP, rfl⟩
  obtain ⟨Q, hQ, hQc⟩ := hmem
  exact ⟨Q, hQ, hQc⟩

/-- `dep` is at most the number of parts of any partition at which the multiplicities differ. -/
theorem dep_le_card {n : ℕ} {S S' : Finset ℕ} (P : n.Partition)
    (h : mult n S P.parts ≠ mult n S' P.parts) : dep n S S' ≤ Multiset.card P.parts :=
  Nat.sInf_le ⟨P, h, rfl⟩

/-- The bridge: `dep(β,γ) ≥ s` iff `G_β - G_γ` has no monomial of ordinary degree `< s`
(for unequal inventories). -/
theorem le_dep_iff {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') (h : G n S ≠ G n S') {s : ℕ} :
    s ≤ dep n S S' ↔ ordGE s (G n S - G n S') := by
  rw [ordGE_G_sub_iff hn hS hS']
  constructor
  · intro hs P hP
    by_contra hne
    have := dep_le_card P hne
    omega
  · intro hs
    obtain ⟨P, hP, hc⟩ := dep_witness hn hS hS' h
    by_contra hlt
    exact hP (hs P (by omega))

/-- A pair of unequal compositions of weight `n`, equal in all ordinary degrees `< s`, whose
difference has a nonzero coefficient at a partition of `n` with exactly `s` parts, has depth
exactly `s` (and in particular unequal inventories). -/
theorem dep_eq_of_witness {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') {s : ℕ} (hlow : ordGE s (G n S - G n S'))
    (P : n.Partition) (hP : mult n S P.parts ≠ mult n S' P.parts)
    (hc : Multiset.card P.parts = s) : G n S ≠ G n S' ∧ dep n S S' = s := by
  have hne : G n S ≠ G n S' := fun h => hP ((G_eq_iff_mult hn hS hS').mp h P)
  refine ⟨hne, le_antisymm (hc ▸ dep_le_card P hP) ((le_dep_iff hn hS hS' hne).mpr hlow)⟩

/-- `dep(β,γ) ≤ D_=(n)` for unequal compositions of weight `n`. -/
theorem dep_le_depthEq {n : ℕ} {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S')
    (h : G n S ≠ G n S') : dep n S S' ≤ depthEq n := by
  classical
  unfold depthEq
  exact Finset.le_sup (f := fun p : Finset ℕ × Finset ℕ => dep n p.1 p.2) (b := (S, S'))
    (by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
        exact ⟨⟨hS, hS'⟩, h⟩)

/-- `D_=(n) ≤ C(N)` for `1 ≤ n ≤ N`. -/
theorem depthEq_le_cumDepth {n N : ℕ} (h1 : 1 ≤ n) (hN : n ≤ N) : depthEq n ≤ cumDepth N :=
  Finset.le_sup (f := depthEq) (Finset.mem_Icc.mpr ⟨h1, hN⟩)

/-- `C` is nondecreasing. -/
theorem cumDepth_mono {N M : ℕ} (h : N ≤ M) : cumDepth N ≤ cumDepth M :=
  Finset.sup_mono (Finset.Icc_subset_Icc le_rfl h)

/-- An unequal pair of weight `n ≤ N` has depth at most `C(N)`. -/
theorem dep_le_cumDepth {n N : ℕ} (h1 : 1 ≤ n) (hN : n ≤ N) {S S' : Finset ℕ}
    (hS : IsCutSet n S) (hS' : IsCutSet n S') (h : G n S ≠ G n S') :
    dep n S S' ≤ cumDepth N :=
  (dep_le_depthEq hS hS' h).trans (depthEq_le_cumDepth h1 hN)

/-- A bound valid for every unequal pair of weight `n` bounds `D_=(n)`. -/
theorem depthEq_le_of_forall {n b : ℕ}
    (h : ∀ S S' : Finset ℕ, IsCutSet n S → IsCutSet n S' → G n S ≠ G n S' → dep n S S' ≤ b) :
    depthEq n ≤ b := by
  classical
  unfold depthEq
  refine Finset.sup_le fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hp
  exact h p.1 p.2 hp.1.1 hp.1.2 hp.2

/-- A bound valid for every unequal pair of weight `n ≤ N` bounds `C(N)`. -/
theorem cumDepth_le_of_forall {N b : ℕ}
    (h : ∀ n, 1 ≤ n → n ≤ N → ∀ S S' : Finset ℕ, IsCutSet n S → IsCutSet n S' →
      G n S ≠ G n S' → dep n S S' ≤ b) : cumDepth N ≤ b := by
  unfold cumDepth
  refine Finset.sup_le fun n hn => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  exact depthEq_le_of_forall (h n h1 h2)

/-- At weight one there is only the empty composition, so `D_=(1) = 0`. -/
theorem depthEq_one : depthEq 1 = 0 := by
  classical
  unfold depthEq
  have : (Finset.Ioo 0 1 : Finset ℕ) = ∅ := by decide
  simp [this]

/-- `thm:main-depth`, the case `N = 1`: `C(1) = 0` (the maximum is empty). -/
theorem cumDepth_one : cumDepth 1 = 0 := by
  unfold cumDepth
  simp [depthEq_one]

end SkewRibbonCoarsenings
