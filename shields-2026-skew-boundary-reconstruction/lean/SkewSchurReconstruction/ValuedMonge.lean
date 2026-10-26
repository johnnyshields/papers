/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.MaximalCofactors
import SkewSchurReconstruction.MongeAssignments
import SkewSchurReconstruction.MinimizerChains
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Order.Fin.Basic

/-!
# Strict-Monge boards over valued integral domains

Generic valued-domain determinant and exact-kernel infrastructure for "An abstract
Strict-Monge cofactor principle" (`subsec:abstract`, `thm:abstract-monge`).
Entries of both boards are sampled from one family. Valuation laws come from Mathlib's
`AddValuation`, and only Ferrers support and strict Monge are standing entry assumptions.
Row and column parameters range over independent linear orders; no arithmetic
structure on either index type is used.
Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R]
variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Standing data of a faithful valued entry family, with Ferrers support. -/
structure ValuedMongeFamily (R Γ ι κ : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [LinearOrder ι] [LinearOrder κ] where
  /-- The additive valuation of the coefficient domain. -/
  valuation : AddValuation R (WithTop Γ)
  finite : ∀ x : R, x ≠ 0 → valuation x ≠ ⊤
  /-- The common entry family sampled by both boards. -/
  entry : ι → κ → R
  support_mono : ∀ {A A' : ι} {d d' : κ},
    A ≤ A' → d' ≤ d → entry A' d' ≠ 0 → entry A d ≠ 0
  strict_monge : ∀ {A A' : ι} {d d' : κ}, A < A' → d < d' →
    entry A d ≠ 0 → entry A' d' ≠ 0 → entry A d' ≠ 0 → entry A' d ≠ 0 →
    (valuation (entry A d)).untopD 0 + (valuation (entry A' d')).untopD 0 <
      (valuation (entry A d')).untopD 0 + (valuation (entry A' d)).untopD 0

/-- Finite minimizers for an arbitrary ordered value group. -/
noncomputable def orderedArgmin {α : Type*} (s : Finset α)
    (c : α → Γ) : Finset α := by
  classical
  exact s.filter (fun x => ∀ y ∈ s, c x ≤ c y)

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
@[simp] theorem mem_orderedArgmin {α : Type*} {s : Finset α}
    {c : α → Γ} {x : α} :
    x ∈ orderedArgmin s c ↔ x ∈ s ∧ ∀ y ∈ s, c x ≤ c y := by
  classical
  simp [orderedArgmin]

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem orderedArgmin_nonempty {α : Type*}
    (s : Finset α) (c : α → Γ) (hs : s.Nonempty) : (orderedArgmin s c).Nonempty := by
  classical
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image (s : Set α) c s.finite_toSet hs
  exact ⟨x, mem_orderedArgmin.mpr ⟨hx, hmin⟩⟩

namespace ValuedMongeFamily

variable {ρ χ : Type*} [LinearOrder ρ] [LinearOrder χ]
variable (F : ValuedMongeFamily R Γ ρ χ)

/-- Finite entry cost on the supported part of the family. -/
noncomputable def cost (A : ρ) (d : χ) : Γ := (F.valuation (F.entry A d)).untopD 0

theorem valuation_entry_eq {A : ρ} {d : χ} (h : F.entry A d ≠ 0) :
    F.valuation (F.entry A d) = (F.cost A d : WithTop Γ) := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (F.finite _ h)
  unfold cost
  rw [← hc, WithTop.untopD_coe]

/-- The actual matrix sampled from the common entry family. -/
def board {n p : ℕ} (A : Fin n → ρ) (d : Fin p → χ) : Matrix (Fin n) (Fin p) R :=
  Matrix.of fun i j => F.entry (A i) (d j)

/-- Feasibility means precisely that every selected entry is nonzero. -/
def feasible {n : ℕ} (A : Fin n → ρ) (d : Fin n → χ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, F.entry (A i) (d (σ i)) ≠ 0

/-- The finite cost of a feasible permutation. -/
noncomputable def assignmentCost {n : ℕ} (A : Fin n → ρ) (d : Fin n → χ)
    (σ : Equiv.Perm (Fin n)) : Γ := ∑ i, F.cost (A i) (d (σ i))

theorem uncross_feasible {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    (hA : StrictMono A) (hd : StrictMono d) {σ : Equiv.Perm (Fin n)}
    (hf : F.feasible A d σ) {i j : Fin n} (hij : i < j) (hinv : σ j < σ i) :
    F.feasible A d (uncrossMatching σ i j) := by
  intro k
  by_cases hki : k = i
  · subst k
    simpa using F.support_mono (hA hij).le le_rfl (hf j)
  by_cases hkj : k = j
  · subst k
    simpa using F.support_mono le_rfl (hd hinv).le (hf j)
  simpa only [uncrossMatching_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using hf k

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem sum_two_rows {n : ℕ} (f : Fin n → Γ) {i j : Fin n} (hij : i ≠ j) :
    (∑ k, f k) = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  classical
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    simp [hij.symm]
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) f hj]
  abel

theorem uncross_cost_lt {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    (hA : StrictMono A) (hd : StrictMono d) {σ : Equiv.Perm (Fin n)}
    (hf : F.feasible A d σ) {i j : Fin n} (hij : i < j) (hinv : σ j < σ i) :
    F.assignmentCost A d (uncrossMatching σ i j) < F.assignmentCost A d σ := by
  have hleft := F.support_mono (hA hij).le le_rfl (hf j)
  have hright := F.support_mono le_rfl (hd hinv).le (hf j)
  have hpair := F.strict_monge (hA hij) (hd hinv) hleft hright (hf i) (hf j)
  have hrest : (∑ k ∈ (Finset.univ.erase i).erase j,
      F.cost (A k) (d (uncrossMatching σ i j k))) =
      ∑ k ∈ (Finset.univ.erase i).erase j, F.cost (A k) (d (σ k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    simp only [uncrossMatching_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  unfold assignmentCost
  rw [sum_two_rows _ (ne_of_lt hij), sum_two_rows _ (ne_of_lt hij)]
  simp only [uncrossMatching_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  simp only [uncrossMatching_apply] at hrest
  rw [hrest]
  change F.cost (A i) (d (σ j)) + F.cost (A j) (d (σ i)) <
    F.cost (A i) (d (σ i)) + F.cost (A j) (d (σ j)) at hpair
  exact add_lt_add_left hpair _

theorem minimizing_assignment_eq_identity {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    (hA : StrictMono A) (hd : StrictMono d) {σ : Equiv.Perm (Fin n)}
    (hf : F.feasible A d σ)
    (hmin : ∀ τ, F.feasible A d τ → F.assignmentCost A d σ ≤ F.assignmentCost A d τ) :
    σ = Equiv.refl (Fin n) := by
  by_contra hn
  obtain ⟨i, j, hij, hinv⟩ := exists_matching_inversion σ hn
  exact (not_lt_of_ge (hmin _ (F.uncross_feasible hA hd hf hij hinv)))
    (F.uncross_cost_lt hA hd hf hij hinv)

theorem identity_cost_lt {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    (hA : StrictMono A) (hd : StrictMono d) {σ : Equiv.Perm (Fin n)}
    (hf : F.feasible A d σ) (hne : σ ≠ Equiv.refl (Fin n)) :
    F.assignmentCost A d (Equiv.refl (Fin n)) < F.assignmentCost A d σ := by
  classical
  let S : Set (Equiv.Perm (Fin n)) := {τ | F.feasible A d τ}
  obtain ⟨τ, hτ, hmin⟩ := Set.exists_min_image S (F.assignmentCost A d)
    (Set.toFinite S) ⟨σ, hf⟩
  have ht := F.minimizing_assignment_eq_identity hA hd hτ hmin
  subst τ
  obtain ⟨i, j, hij, hinv⟩ := exists_matching_inversion σ hne
  exact (hmin _ (F.uncross_feasible hA hd hf hij hinv)).trans_lt
    (F.uncross_cost_lt hA hd hf hij hinv)

/-- A finite sum with a unique strictly smallest valued summand has that summand's valuation. -/
theorem valuation_sum_unique {ι : Type*} (s : Finset ι) (f : ι → R) {i : ι}
    (hi : i ∈ s) (hfi : f i ≠ 0)
    (hmin : ∀ j ∈ s, j ≠ i → F.valuation (f i) < F.valuation (f j)) :
    F.valuation (∑ j ∈ s, f j) = F.valuation (f i) := by
  classical
  rw [← Finset.add_sum_erase s f hi]
  apply F.valuation.map_add_eq_of_lt_left
  apply F.valuation.map_lt_sum (F.finite _ hfi)
  intro j hj
  exact hmin j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)

/-- A unique strictly smallest summand cannot occur in an exact zero relation. -/
theorem zero_sum_not_unique_min {ι : Type*} (s : Finset ι) (f : ι → R)
    (hsum : ∑ j ∈ s, f j = 0) {i : ι} (hi : i ∈ s) (hfi : f i ≠ 0) :
    ∃ j ∈ s, j ≠ i ∧ F.valuation (f j) ≤ F.valuation (f i) := by
  classical
  by_contra hn
  have hmin : ∀ j ∈ s, j ≠ i → F.valuation (f i) < F.valuation (f j) := by
    intro j hj hji
    exact lt_of_not_ge (fun h => hn ⟨j, hj, hji, h⟩)
  have he := F.valuation_sum_unique s f hi hfi hmin
  rw [hsum, F.valuation.map_zero] at he
  exact F.finite _ hfi he.symm

/-- Actual signed maximal cofactors on the sampled board. -/
noncomputable def cofactors {n : ℕ} (A : Fin n → ρ) (d : Fin (n + 1) → χ) :
    Fin (n + 1) → R := signedMaximalCofactor (F.board A d)

/-- The actual cofactor difference on two boards sampled from the same family. -/
noncomputable def defect {n : ℕ} (A B : Fin n → ρ) (d : Fin (n + 1) → χ) :
    Fin (n + 1) → R := fun j => F.cofactors A d j - F.cofactors B d j

/-- Shared row parameters give exact defect kernels, independently of valuation assumptions. -/
theorem shared_row_defect_relation {n : ℕ} (A B : Fin n → ρ) (d : Fin (n + 1) → χ)
    (i : Fin n) (hi : A i = B i) :
    ∑ j, F.entry (A i) (d j) * F.defect A B d j = 0 := by
  apply shared_row_sum_cofactor_sub_eq_zero (F.board A d) (F.board B d) i i
  funext j
  simp only [board, Matrix.of_apply, hi]

/-- Every nonzero lowest summand in a shared row's exact relation has a second tied summand. -/
theorem shared_row_tropical_balancing {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (i : Fin n) (hi : A i = B i)
    (j : Fin (n + 1)) (hj : F.entry (A i) (d j) * F.defect A B d j ≠ 0)
    (hmin : ∀ k, F.valuation (F.entry (A i) (d j) * F.defect A B d j) ≤
      F.valuation (F.entry (A i) (d k) * F.defect A B d k)) :
    ∃ k, k ≠ j ∧ F.valuation (F.entry (A i) (d k) * F.defect A B d k) =
      F.valuation (F.entry (A i) (d j) * F.defect A B d j) := by
  obtain ⟨k, _, hkj, hk⟩ := F.zero_sum_not_unique_min Finset.univ
    (fun k => F.entry (A i) (d k) * F.defect A B d k)
    (F.shared_row_defect_relation A B d i hi) (Finset.mem_univ j) hj
  exact ⟨k, hkj, le_antisymm hk (hmin k)⟩

/-- The signed Leibniz term in the row-to-column convention. -/
noncomputable def determinantTerm {n : ℕ} (A : Fin n → ρ) (d : Fin n → χ)
    (σ : Equiv.Perm (Fin n)) : R :=
  Equiv.Perm.sign σ • ∏ i, F.entry (A i) (d (σ i))

theorem determinant_expansion {n : ℕ} (A : Fin n → ρ) (d : Fin n → χ) :
    (F.board A d).det = ∑ σ, F.determinantTerm A d σ := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  rfl

theorem determinantTerm_ne_zero {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    {σ : Equiv.Perm (Fin n)} (hf : F.feasible A d σ) :
    F.determinantTerm A d σ ≠ 0 := by
  have hp : (∏ i, F.entry (A i) (d (σ i))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [determinantTerm, hs] using hp

theorem determinantTerm_eq_zero {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    {σ : Equiv.Perm (Fin n)} (hf : ¬ F.feasible A d σ) :
    F.determinantTerm A d σ = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hf
  have hz : F.entry (A i) (d (σ i)) = 0 := not_ne_iff.mp hi
  unfold determinantTerm
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, smul_zero]

private theorem valuation_product_eq_cost {ι : Type*} (s : Finset ι)
    (a : ι → ρ) (d : ι → χ) (hf : ∀ i ∈ s, F.entry (a i) (d i) ≠ 0) :
    F.valuation (∏ i ∈ s, F.entry (a i) (d i)) =
      ((∑ i ∈ s, F.cost (a i) (d i) : Γ) : WithTop Γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, F.valuation.map_one, WithTop.coe_zero]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, F.valuation.map_mul,
        F.valuation_entry_eq (hf i (Finset.mem_insert_self _ _)),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), WithTop.coe_add]

theorem determinantTerm_valuation {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    {σ : Equiv.Perm (Fin n)} (hf : F.feasible A d σ) :
    F.valuation (F.determinantTerm A d σ) =
      (F.assignmentCost A d σ : WithTop Γ) := by
  have hp := F.valuation_product_eq_cost Finset.univ A (fun i => d (σ i)) (fun i _ => hf i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [determinantTerm, assignmentCost, hs] using hp

/-- Strict Monge forces the determinant's actual valuation to equal the increasing matching cost. -/
theorem ordered_determinant_valuation {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    (hA : StrictMono A) (hd : StrictMono d)
    (hf : ∀ i, F.entry (A i) (d i) ≠ 0) :
    F.valuation (F.board A d).det = ((∑ i, F.cost (A i) (d i) : Γ) : WithTop Γ) := by
  classical
  let e : Equiv.Perm (Fin n) := Equiv.refl _
  have he : F.feasible A d e := hf
  rw [F.determinant_expansion]
  have hmin : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), σ ≠ e →
      F.valuation (F.determinantTerm A d e) <
        F.valuation (F.determinantTerm A d σ) := by
    intro σ _ hσ
    rw [F.determinantTerm_valuation he]
    by_cases hfeas : F.feasible A d σ
    · rw [F.determinantTerm_valuation hfeas]
      exact WithTop.coe_lt_coe.mpr (F.identity_cost_lt hA hd hfeas hσ)
    · rw [F.determinantTerm_eq_zero hfeas, F.valuation.map_zero]
      exact WithTop.coe_lt_top _
  rw [F.valuation_sum_unique Finset.univ (F.determinantTerm A d)
    (Finset.mem_univ e) (F.determinantTerm_ne_zero he) hmin,
    F.determinantTerm_valuation he]
  rfl

theorem ordered_determinant_ne_zero {n : ℕ} {A : Fin n → ρ} {d : Fin n → χ}
    (hA : StrictMono A) (hd : StrictMono d)
    (hf : ∀ i, F.entry (A i) (d i) ≠ 0) : (F.board A d).det ≠ 0 := by
  intro hz
  have he := F.ordered_determinant_valuation hA hd hf
  rw [hz, F.valuation.map_zero] at he
  exact WithTop.coe_ne_top he.symm

/-- All maximal-minor increasing matchings are supported. -/
def maximalMatchingsFeasible {n : ℕ} (A : Fin n → ρ) (d : Fin (n + 1) → χ) : Prop :=
  ∀ (j : Fin (n + 1)) (i : Fin n), F.entry (A i) (d (j.succAbove i)) ≠ 0

/-- The actual maximal-cofactor valuation is its increasing matching cost. -/
theorem cofactor_valuation {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    (j : Fin (n + 1)) :
    F.valuation (F.cofactors A d j) =
      ((∑ i, F.cost (A i) (d (j.succAbove i)) : Γ) : WithTop Γ) := by
  have hminor : (F.board A d).submatrix id j.succAbove =
      F.board A (fun i => d (j.succAbove i)) := by
    ext i k
    rfl
  unfold cofactors signedMaximalCofactor
  rw [F.valuation.map_mul, F.valuation.map_pow, F.valuation.map_neg,
    F.valuation.map_one, nsmul_zero, zero_add, hminor]
  exact F.ordered_determinant_valuation hA (hd.comp (Fin.strictMono_succAbove j)) (hf j)

theorem cofactor_ne_zero {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    (j : Fin (n + 1)) : F.cofactors A d j ≠ 0 := by
  intro hz
  have he := F.cofactor_valuation hA hd hf j
  rw [hz, F.valuation.map_zero] at he
  exact WithTop.coe_ne_top he.symm

/-- Normalized actions of actual cofactors; `top` is the shared first row parameter. -/
noncomputable def action {n : ℕ} (A : Fin n → ρ) (d : Fin (n + 1) → χ)
    (top : ρ) (j : Fin (n + 1)) : Γ :=
  (F.valuation (F.cofactors A d j)).untopD 0 + F.cost top (d j)

theorem action_eq_matching_cost {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    (top : ρ) (j : Fin (n + 1)) :
    F.action A d top j = (∑ i, F.cost (A i) (d (j.succAbove i))) + F.cost top (d j) := by
  rw [action, F.cofactor_valuation hA hd hf j, WithTop.untopD_coe]

private theorem adjacent_cost_exchange {n : ℕ} (A : Fin n → ρ) (d : Fin (n + 1) → χ)
    (j : Fin n) :
    (∑ i, F.cost (A i) (d (j.succ.succAbove i))) -
      (∑ i, F.cost (A i) (d (j.castSucc.succAbove i))) =
        F.cost (A j) (d j.castSucc) - F.cost (A j) (d j.succ) := by
  classical
  rw [← Finset.sum_sub_distrib]
  have he : ∀ i : Fin n,
      F.cost (A i) (d (j.succ.succAbove i)) -
        F.cost (A i) (d (j.castSucc.succAbove i)) =
      if i = j then F.cost (A j) (d j.castSucc) - F.cost (A j) (d j.succ) else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      simp
    · rcases lt_or_gt_of_ne hij with hi | hi
      · simp [hij, Fin.succAbove_succ_of_le _ _ hi.le, Fin.succAbove_castSucc_of_lt _ _ hi]
      · simp [hij, Fin.succAbove_succ_of_lt _ _ hi, Fin.succAbove_castSucc_of_le _ _ hi.le]
  simp_rw [he]
  simp

/-- The action recurrence is derived from actual determinant valuations. -/
theorem action_recurrence {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    (top : ρ) (j : Fin n) :
    F.action A d top j.succ - F.action A d top j.castSucc =
      F.cost (A j) (d j.castSucc) - F.cost (A j) (d j.succ) +
        F.cost top (d j.succ) - F.cost top (d j.castSucc) := by
  rw [F.action_eq_matching_cost hA hd hf, F.action_eq_matching_cost hA hd hf]
  have he := F.adjacent_cost_exchange A d j
  calc
    (∑ i, F.cost (A i) (d (j.succ.succAbove i))) + F.cost top (d j.succ) -
        ((∑ i, F.cost (A i) (d (j.castSucc.succAbove i))) + F.cost top (d j.castSucc)) =
      ((∑ i, F.cost (A i) (d (j.succ.succAbove i))) -
        (∑ i, F.cost (A i) (d (j.castSucc.succAbove i)))) +
        F.cost top (d j.succ) - F.cost top (d j.castSucc) := by abel
    _ = _ := by rw [he]

/-- Supported defect coordinates in a row sampled from the common family. -/
noncomputable def rowDefectSupport {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun j => F.entry row (d j) ≠ 0 ∧ F.defect A B d j ≠ 0)

/-- Finite valued cost of a supported common-row defect summand. -/
noncomputable def rowDefectCost {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) (j : Fin (n + 1)) : Γ :=
  F.cost row (d j) + (F.valuation (F.defect A B d j)).untopD 0

/-- The common-row minimizing set is computed on the actual supported defect. -/
noncomputable def rowMinimizers {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) : Finset (Fin (n + 1)) :=
  orderedArgmin (F.rowDefectSupport A B d row) (F.rowDefectCost A B d row)

theorem rowDefectCost_valuation {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) (j : Fin (n + 1))
    (hj : j ∈ F.rowDefectSupport A B d row) :
    F.valuation (F.entry row (d j) * F.defect A B d j) =
      (F.rowDefectCost A B d row j : WithTop Γ) := by
  classical
  obtain ⟨he, hg⟩ := (Finset.mem_filter.mp hj).2
  rw [F.valuation.map_mul, F.valuation_entry_eq he]
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (F.finite _ hg)
  unfold rowDefectCost
  rw [← hc, WithTop.untopD_coe, WithTop.coe_add]

/-- Strict Monge makes actual supported common-row minimizers interlace. -/
theorem rowMinimizers_interlace {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (hd : StrictMono d)
    {row row' : ρ} (hr : row < row') {x y : Fin (n + 1)}
    (hx : x ∈ F.rowMinimizers A B d row)
    (hy : y ∈ F.rowMinimizers A B d row') : x ≤ y := by
  classical
  obtain ⟨hxs, hxmin⟩ := mem_orderedArgmin.mp hx
  obtain ⟨hys, hymin⟩ := mem_orderedArgmin.mp hy
  obtain ⟨hxe, hxg⟩ := (Finset.mem_filter.mp hxs).2
  obtain ⟨hye, hyg⟩ := (Finset.mem_filter.mp hys).2
  by_contra hn
  have hyx : y < x := lt_of_not_ge hn
  have hye' := F.support_mono hr.le le_rfl hye
  have hxe' := F.support_mono le_rfl (hd hyx).le hye
  have hys' : y ∈ F.rowDefectSupport A B d row := by simp [rowDefectSupport, hye', hyg]
  have hxs' : x ∈ F.rowDefectSupport A B d row' := by simp [rowDefectSupport, hxe', hxg]
  have hxy := hxmin y hys'
  have hyx' := hymin x hxs'
  have hmonge := F.strict_monge hr (hd hyx) hye' hxe' hxe hye
  change F.cost row (d y) + F.cost row' (d x) <
    F.cost row (d x) + F.cost row' (d y) at hmonge
  unfold rowDefectCost at hxy hyx'
  have hsum := add_le_add hxy hyx'
  have hnorm :
      (F.cost row (d x) + F.cost row' (d y)) +
          ((F.valuation (F.defect A B d x)).untopD 0 +
            (F.valuation (F.defect A B d y)).untopD 0) ≤
      (F.cost row (d y) + F.cost row' (d x)) +
          ((F.valuation (F.defect A B d x)).untopD 0 +
            (F.valuation (F.defect A B d y)).untopD 0) := by
    convert hsum using 1 <;> abel
  exact not_lt_of_ge (add_le_add_iff_right _ |>.mp hnorm) hmonge

theorem diagonal_support {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hf : F.maximalMatchingsFeasible A d) (i : Fin n) :
    F.entry (A i) (d i.castSucc) ≠ 0 := by
  simpa only [Fin.succAbove_succ_self] using hf i.succ i

/-- Equal initial normalized actions synchronize through an unchanged row prefix. -/
theorem actions_synchronized {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (j : Fin (n + 1)) (hj : j.val ≤ r.val) :
    F.action A d top j = F.action B d top j := by
  have hall : ∀ k (hk : k < n + 1), k ≤ r.val →
      F.action A d top ⟨k, hk⟩ = F.action B d top ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro _ _; exact hzero
    | succ k ih =>
        intro hk hkr
        let i : Fin n := ⟨k, by omega⟩
        have hi : i.val < r.val := by dsimp [i]; omega
        have hp : F.action A d top i.castSucc = F.action B d top i.castSucc :=
          ih (by omega) (by omega)
        have heA := F.action_recurrence hA hd hfA top i
        have heB := F.action_recurrence hB hd hfB top i
        rw [← hprefix i hi] at heB
        change F.action A d top i.succ = F.action B d top i.succ
        have he := heA.trans heB.symm
        rw [hp] at he
        have hh := congrArg (fun z => z + F.action B d top i.castSucc) he
        simpa only [sub_add_cancel] using hh
  exact hall j.val j.isLt hj

/-- The first changed parameter forces a strict action split in the next cofactor. -/
theorem first_action_split_lt {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r < B r) :
    F.action A d top r.succ < F.action B d top r.succ := by
  have hp := F.actions_synchronized hA hB hd hfA hfB top hzero r hprefix
    r.castSucc (by rfl)
  have heA := F.action_recurrence hA hd hfA top r
  have heB := F.action_recurrence hB hd hfB top r
  have hAs := hfA r.castSucc r
  have hBs := hfB r.castSucc r
  simp only [Fin.succAbove_castSucc_self] at hAs hBs
  have hmonge := F.strict_monge hchanged
    (hd (show r.castSucc < r.succ by change r.val < r.val + 1; omega))
    (F.diagonal_support hfA r) hBs hAs (F.diagonal_support hfB r)
  change F.cost (A r) (d r.castSucc) + F.cost (B r) (d r.succ) <
    F.cost (A r) (d r.succ) + F.cost (B r) (d r.castSucc) at hmonge
  have hdelta : F.cost (A r) (d r.castSucc) - F.cost (A r) (d r.succ) <
      F.cost (B r) (d r.castSucc) - F.cost (B r) (d r.succ) := by
    apply sub_lt_sub_iff.mpr
    simpa only [add_comm] using hmonge
  have hinc := add_lt_add_right hdelta (F.cost top (d r.succ) - F.cost top (d r.castSucc))
  have hinc' : F.action A d top r.succ - F.action A d top r.castSucc <
      F.action B d top r.succ - F.action B d top r.castSucc := by
    rw [heA, heB]
    convert hinc using 1 <;> abel
  rw [hp] at hinc'
  have htranslated := add_lt_add_left hinc' (F.action B d top r.castSucc)
  simpa only [sub_add_cancel] using htranslated

theorem first_action_split_ne {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r) :
    F.action A d top r.succ ≠ F.action B d top r.succ := by
  rcases lt_or_gt_of_ne hchanged with hlt | hgt
  · exact (F.first_action_split_lt hA hB hd hfA hfB top hzero r hprefix hlt).ne
  · exact (F.first_action_split_lt hB hA hd hfB hfA top hzero.symm r
      (fun i hi => (hprefix i hi).symm) hgt).ne'

/-- Unequal cofactor valuations cannot cancel at the first forced split. -/
theorem first_split_defect_valuation {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r) :
    F.valuation (F.defect A B d r.succ) =
      min (F.valuation (F.cofactors A d r.succ)) (F.valuation (F.cofactors B d r.succ)) := by
  have hn := F.first_action_split_ne hA hB hd hfA hfB top hzero r hprefix hchanged
  have hv : F.valuation (F.cofactors A d r.succ) ≠
      F.valuation (F.cofactors B d r.succ) := by
    intro he
    apply hn
    simp only [action, he]
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · rw [defect, F.valuation.map_sub_eq_of_lt_left hlt, min_eq_left hlt.le]
  · rw [defect, F.valuation.map_sub_eq_of_lt_right hgt, min_eq_right hgt.le]

theorem first_split_defect_ne_zero {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r) : F.defect A B d r.succ ≠ 0 := by
  intro hz
  have he := F.first_split_defect_valuation hA hB hd hfA hfB top hzero r hprefix hchanged
  rw [hz, F.valuation.map_zero] at he
  have hfin := F.finite _ (F.cofactor_ne_zero hA hd hfA r.succ)
  have hl : (⊤ : WithTop Γ) ≤ F.valuation (F.cofactors A d r.succ) :=
    he.le.trans (min_le_left _ _)
  exact hfin (top_le_iff.mp hl)

theorem rowMinimizers_card_two {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (i : Fin n) (hi : A i = B i)
    (hs : (F.rowDefectSupport A B d (A i)).Nonempty) :
    2 ≤ (F.rowMinimizers A B d (A i)).card := by
  classical
  obtain ⟨j, hj⟩ := orderedArgmin_nonempty (F.rowDefectSupport A B d (A i))
    (F.rowDefectCost A B d (A i)) hs
  obtain ⟨hjs, hjmin⟩ := mem_orderedArgmin.mp hj
  have hjnz := (Finset.mem_filter.mp hjs).2
  have hpj : F.entry (A i) (d j) * F.defect A B d j ≠ 0 :=
    mul_ne_zero hjnz.1 hjnz.2
  have hminv : ∀ k, F.valuation (F.entry (A i) (d j) * F.defect A B d j) ≤
      F.valuation (F.entry (A i) (d k) * F.defect A B d k) := by
    intro k
    by_cases hks : k ∈ F.rowDefectSupport A B d (A i)
    · rw [F.rowDefectCost_valuation A B d (A i) j hjs,
        F.rowDefectCost_valuation A B d (A i) k hks]
      exact WithTop.coe_le_coe.mpr (hjmin k hks)
    · have hz : F.entry (A i) (d k) * F.defect A B d k = 0 := by
        have hn : ¬(F.entry (A i) (d k) ≠ 0 ∧ F.defect A B d k ≠ 0) := by
          simpa only [rowDefectSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hks
        by_cases he : F.entry (A i) (d k) = 0
        · rw [he, zero_mul]
        · have hg : F.defect A B d k = 0 := by
            by_contra hgn
            exact hn ⟨he, hgn⟩
          rw [hg, mul_zero]
      rw [hz, F.valuation.map_zero]
      exact le_top
  obtain ⟨k, hkj, he⟩ := F.shared_row_tropical_balancing A B d i hi j hpj hminv
  have hknz : F.entry (A i) (d k) * F.defect A B d k ≠ 0 := by
    intro hz
    rw [hz, F.valuation.map_zero] at he
    exact F.finite _ hpj he.symm
  have hks : k ∈ F.rowDefectSupport A B d (A i) := by
    simp only [rowDefectSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mul_ne_zero_iff.mp hknz)
  have hcost : F.rowDefectCost A B d (A i) k = F.rowDefectCost A B d (A i) j := by
    rw [F.rowDefectCost_valuation A B d (A i) k hks,
      F.rowDefectCost_valuation A B d (A i) j hjs] at he
    exact WithTop.coe_injective he
  have hk : k ∈ F.rowMinimizers A B d (A i) :=
    mem_orderedArgmin.mpr ⟨hks, fun x hx => hcost ▸ hjmin x hx⟩
  have hsub : {j, k} ⊆ F.rowMinimizers A B d (A i) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  simpa [hkj, Ne.symm hkj] using hc

/-- Tilted cost of an actual parent cofactor in a sampled row. -/
noncomputable def parentTiltedCost {n : ℕ}
    (A : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) (j : Fin (n + 1)) : Γ :=
  (F.valuation (F.cofactors A d j)).untopD 0 + F.cost row (d j)

theorem parentTiltedCost_recurrence {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    (row : ρ) (j : Fin n) :
    F.parentTiltedCost A d row j.succ - F.parentTiltedCost A d row j.castSucc =
      F.cost (A j) (d j.castSucc) - F.cost (A j) (d j.succ) +
        F.cost row (d j.succ) - F.cost row (d j.castSucc) :=
  F.action_recurrence hA hd hf row j

theorem parentTiltedCost_lt_succ {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    {row : ρ} (j : Fin n) (hr : row < A j) :
    F.parentTiltedCost A d row j.castSucc < F.parentTiltedCost A d row j.succ := by
  have hdiag := F.diagonal_support hf j
  have hs := hf j.castSucc j
  simp only [Fin.succAbove_castSucc_self] at hs
  have hrd := F.support_mono hr.le le_rfl hdiag
  have hrs := F.support_mono hr.le le_rfl hs
  have hm := F.strict_monge hr
    (hd (show j.castSucc < j.succ by change j.val < j.val + 1; omega)) hrd hs hrs hdiag
  change F.cost row (d j.castSucc) + F.cost (A j) (d j.succ) <
    F.cost row (d j.succ) + F.cost (A j) (d j.castSucc) at hm
  have he := F.parentTiltedCost_recurrence hA hd hf row j
  have hdelta : F.cost row (d j.castSucc) - F.cost (A j) (d j.castSucc) <
      F.cost row (d j.succ) - F.cost (A j) (d j.succ) :=
    sub_lt_sub_iff.mpr hm
  have hp : 0 < F.cost (A j) (d j.castSucc) - F.cost (A j) (d j.succ) +
      F.cost row (d j.succ) - F.cost row (d j.castSucc) := by
    convert sub_pos.mpr hdelta using 1
    abel
  rw [← he] at hp
  exact sub_pos.mp hp

theorem parentTiltedCost_tail_lt {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    {row : ρ} (r : Fin n) (hr : row < A r) (j : Fin (n + 1))
    (hj : r.val + 1 < j.val) :
    F.parentTiltedCost A d row r.succ < F.parentTiltedCost A d row j := by
  let f : Fin (n - r.val - 1 + 1) → Fin (n + 1) :=
    fun i => ⟨r.val + 1 + i.val, by omega⟩
  have hmono : StrictMono (fun i => F.parentTiltedCost A d row (f i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    let s : Fin n := ⟨r.val + 1 + i.val, by omega⟩
    have h0 : f i.castSucc = s.castSucc := Fin.ext rfl
    have h1 : f i.succ = s.succ := by apply Fin.ext; simp [f, s]; omega
    rw [h0, h1]
    apply F.parentTiltedCost_lt_succ hA hd hf
    apply hr.trans
    apply hA
    change r.val < r.val + 1 + i.val
    omega
  let b : Fin (n - r.val - 1 + 1) := ⟨j.val - (r.val + 1), by omega⟩
  have hfb : f b = j := by apply Fin.ext; dsimp [f, b]; omega
  have hf0 : f 0 = r.succ := by apply Fin.ext; simp [f]
  have hb : (0 : Fin (n - r.val - 1 + 1)) < b := by
    change 0 < j.val - (r.val + 1)
    omega
  simpa only [hfb, hf0] using hmono hb

/-- The exact valued summand, including infinity at unsupported or zero defect coordinates. -/
noncomputable def tiltedDefectValue {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) (j : Fin (n + 1)) : WithTop Γ :=
  F.valuation (F.entry row (d j) * F.defect A B d j)

theorem parentTiltedCost_valuation {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    (row : ρ) (j : Fin (n + 1)) (he : F.entry row (d j) ≠ 0) :
    F.valuation (F.cofactors A d j) + F.valuation (F.entry row (d j)) =
      (F.parentTiltedCost A d row j : WithTop Γ) := by
  rw [F.cofactor_valuation hA hd hf, F.valuation_entry_eq he]
  simp only [parentTiltedCost, F.cofactor_valuation hA hd hf, WithTop.untopD_coe,
    WithTop.coe_add]

theorem tiltedDefectValue_parent_lower_bound {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) (j : Fin (n + 1)) :
    min (F.valuation (F.cofactors A d j) + F.valuation (F.entry row (d j)))
      (F.valuation (F.cofactors B d j) + F.valuation (F.entry row (d j))) ≤
      F.tiltedDefectValue A B d row j := by
  rw [min_add_add_right]
  have h := add_le_add_right
    (F.valuation.map_sub (F.cofactors A d j) (F.cofactors B d j))
    (F.valuation (F.entry row (d j)))
  simpa only [tiltedDefectValue, defect, F.valuation.map_mul, add_comm] using h

theorem prefix_row_entry_support {n : ℕ} {A : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hd : StrictMono d) (hf : F.maximalMatchingsFeasible A d)
    (r i : Fin n) (hi : i < r) (j : Fin (n + 1)) (hj : r.val ≤ j.val) :
    F.entry (A i) (d j) ≠ 0 := by
  apply F.support_mono (hA hi).le _ (F.diagonal_support hf r)
  exact (hd.monotone (show r.castSucc ≤ j from hj))

/-- Generic no-backflow: every later supported common-row summand lies strictly above the anchor. -/
theorem no_backflow {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r) (i : Fin n) (hi : i < r)
    (j : Fin (n + 1)) (hj : r.val + 1 < j.val) :
    F.tiltedDefectValue A B d (A i) r.succ <
      F.tiltedDefectValue A B d (A i) j := by
  have his : A i = B i := hprefix i hi
  have hes := F.prefix_row_entry_support hA hd hfA r i hi r.succ (by simp)
  have hej := F.prefix_row_entry_support hA hd hfA r i hi j (by omega)
  have hltA := F.parentTiltedCost_tail_lt hA hd hfA r (hA hi) j hj
  have hltB := F.parentTiltedCost_tail_lt hB hd hfB r
    (show A i < B r by rw [his]; exact hB hi) j hj
  have hmin : min (F.parentTiltedCost A d (A i) r.succ)
      (F.parentTiltedCost B d (A i) r.succ) <
      min (F.parentTiltedCost A d (A i) j) (F.parentTiltedCost B d (A i) j) := by
    apply lt_min
    · exact (min_le_left _ _).trans_lt hltA
    · exact (min_le_right _ _).trans_lt hltB
  have hanchor : F.tiltedDefectValue A B d (A i) r.succ =
      ((min (F.parentTiltedCost A d (A i) r.succ)
        (F.parentTiltedCost B d (A i) r.succ)) : WithTop Γ) := by
    rw [tiltedDefectValue, F.valuation.map_mul,
      F.first_split_defect_valuation hA hB hd hfA hfB top hzero r hprefix hchanged,
      add_comm, ← min_add_add_right,
      F.parentTiltedCost_valuation hA hd hfA (A i) r.succ hes,
      F.parentTiltedCost_valuation hB hd hfB (A i) r.succ hes]
  have hbound := F.tiltedDefectValue_parent_lower_bound A B d (A i) j
  rw [F.parentTiltedCost_valuation hA hd hfA (A i) j hej,
    F.parentTiltedCost_valuation hB hd hfB (A i) j hej] at hbound
  rw [hanchor]
  exact (WithTop.coe_lt_coe.mpr hmin).trans_le (by simpa using hbound)

theorem common_row_support_nonempty {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r) (i : Fin n) (hi : i < r) :
    (F.rowDefectSupport A B d (A i)).Nonempty := by
  classical
  refine ⟨r.succ, ?_⟩
  simp only [rowDefectSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨F.prefix_row_entry_support hA hd hfA r i hi r.succ (by simp),
    F.first_split_defect_ne_zero hA hB hd hfA hfB top hzero r hprefix hchanged⟩

theorem common_row_minimizers_upper_bound {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r) (i : Fin n) (hi : i < r)
    (j : Fin (n + 1)) (hj : j ∈ F.rowMinimizers A B d (A i)) :
    j.val ≤ r.val + 1 := by
  classical
  obtain ⟨hjs, hjmin⟩ := mem_orderedArgmin.mp hj
  have has : r.succ ∈ F.rowDefectSupport A B d (A i) := by
    simp only [rowDefectSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨F.prefix_row_entry_support hA hd hfA r i hi r.succ (by simp),
      F.first_split_defect_ne_zero hA hB hd hfA hfB top hzero r hprefix hchanged⟩
  by_contra hn
  have hv := F.no_backflow hA hB hd hfA hfB top hzero r hprefix hchanged i hi j
    (by omega)
  change F.valuation (F.entry (A i) (d r.succ) * F.defect A B d r.succ) <
    F.valuation (F.entry (A i) (d j) * F.defect A B d j) at hv
  rw [F.rowDefectCost_valuation A B d (A i) r.succ has,
    F.rowDefectCost_valuation A B d (A i) j hjs] at hv
  exact (not_lt_of_ge (hjmin r.succ has)) (WithTop.coe_lt_coe.mp hv)

/-- Minimizing columns, represented by their ordered natural labels. -/
noncomputable def columnMinimizers {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) : Finset ℕ :=
  (F.rowMinimizers A B d row).image Fin.val

theorem columnMinimizers_card {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (row : ρ) :
    (F.columnMinimizers A B d row).card = (F.rowMinimizers A B d row).card :=
  Finset.card_image_of_injective _ Fin.val_injective

theorem columnMinimizers_interlace {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (hd : StrictMono d)
    {row row' : ρ} (hr : row < row') :
    ∀ x ∈ F.columnMinimizers A B d row,
      ∀ y ∈ F.columnMinimizers A B d row', x ≤ y := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  exact F.rowMinimizers_interlace A B d hd hr ha hb

/-- Exact kernels force the rightmost actual minimizers to march strictly. -/
theorem columnMinimizers_march {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (hd : StrictMono d)
    {i j : Fin n} (hij : A i < A j) (hi : A i = B i) (hj : A j = B j)
    (hsi : (F.rowDefectSupport A B d (A i)).Nonempty)
    (hsj : (F.rowDefectSupport A B d (A j)).Nonempty) :
    (F.columnMinimizers A B d (A i)).max'
        (by apply Finset.card_pos.mp; rw [F.columnMinimizers_card];
            have := F.rowMinimizers_card_two A B d i hi hsi; omega) <
      (F.columnMinimizers A B d (A j)).max'
        (by apply Finset.card_pos.mp; rw [F.columnMinimizers_card];
            have := F.rowMinimizers_card_two A B d j hj hsj; omega) := by
  apply interlacing_max_strict
  · rw [F.columnMinimizers_card]
    exact F.rowMinimizers_card_two A B d j hj hsj
  · exact F.columnMinimizers_interlace A B d hd hij

/-- The positive normalized-defect floor, retaining infinite coordinates honestly. -/
noncomputable def positiveFloor {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (top : ρ) : WithTop Γ := by
  classical
  exact (Finset.univ.erase 0).inf (F.tiltedDefectValue A B d top)

theorem strict_floor_excludes_zero {n : ℕ}
    (A B : Fin n → ρ) (d : Fin (n + 1) → χ) (top : ρ)
    (hfloor : F.positiveFloor A B d top < F.tiltedDefectValue A B d top 0) :
    0 ∉ F.rowMinimizers A B d top := by
  classical
  intro h0
  obtain ⟨h0s, h0min⟩ := mem_orderedArgmin.mp h0
  obtain ⟨j, _, hjlt⟩ := Finset.inf_lt_iff.mp hfloor
  have hjnz : F.entry top (d j) * F.defect A B d j ≠ 0 := by
    intro hz
    unfold tiltedDefectValue at hjlt
    rw [hz, F.valuation.map_zero] at hjlt
    exact not_lt_of_ge le_top hjlt
  have hjs : j ∈ F.rowDefectSupport A B d top := by
    simp only [rowDefectSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact mul_ne_zero_iff.mp hjnz
  change F.valuation (F.entry top (d j) * F.defect A B d j) <
    F.valuation (F.entry top (d 0) * F.defect A B d 0) at hjlt
  rw [F.rowDefectCost_valuation A B d top j hjs,
    F.rowDefectCost_valuation A B d top 0 h0s] at hjlt
  exact not_lt_of_ge (h0min j hjs) (WithTop.coe_lt_coe.mp hjlt)

/-- Natural labels of the common-prefix rows. -/
def commonPrefixRow {n : ℕ} (r : Fin n) (i : Fin r.val) : Fin n :=
  ⟨i.val, by omega⟩

/-- The strict floor forces the actual common-row minimizers to be consecutive adjacent pairs. -/
theorem strict_floor_adjacent_chain {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (r : Fin n) (hr : 0 < r.val)
    (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r)
    (hzero : F.action A d (A ⟨0, by omega⟩) 0 = F.action B d (A ⟨0, by omega⟩) 0)
    (hfloor : F.positiveFloor A B d (A ⟨0, by omega⟩) <
      F.tiltedDefectValue A B d (A ⟨0, by omega⟩) 0) :
    ∀ i : Fin r.val, F.columnMinimizers A B d (A (commonPrefixRow r i)) =
      {i.val + 1, i.val + 2} := by
  classical
  let top := A (⟨0, by omega⟩ : Fin n)
  let M : Fin r.val → Finset ℕ :=
    fun i => F.columnMinimizers A B d (A (commonPrefixRow r i))
  have hcard : ∀ i, 2 ≤ (M i).card := by
    intro i
    rw [F.columnMinimizers_card]
    apply F.rowMinimizers_card_two A B d (commonPrefixRow r i)
    · apply hprefix
      exact i.isLt
    · apply F.common_row_support_nonempty hA hB hd hfA hfB top hzero r hprefix hchanged
      exact i.isLt
  have hupper : ∀ i, ∀ x ∈ M i, x ≤ r.val + 1 := by
    intro i x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact F.common_row_minimizers_upper_bound hA hB hd hfA hfB top hzero r hprefix
      hchanged (commonPrefixRow r i) i.isLt j hj
  have hzeroM : 0 ∉ M ⟨0, hr⟩ := by
    intro hz
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp hz
    have hj' : j = 0 := Fin.ext hj0
    subst j
    exact F.strict_floor_excludes_zero A B d top hfloor hj
  have hinter : ∀ i j : Fin r.val, i.val + 1 = j.val →
      ∀ x ∈ M i, ∀ y ∈ M j, x ≤ y := by
    intro i j hij
    apply F.columnMinimizers_interlace A B d hd
    apply hA
    change i.val < j.val
    omega
  exact cap_fixed_interlacing_chain hr M hcard hupper hzeroM hinter

theorem cofactor_valuations_synchronized {n : ℕ}
    {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (j : Fin (n + 1)) (hj : j.val ≤ r.val) :
    F.valuation (F.cofactors A d j) = F.valuation (F.cofactors B d j) := by
  have he := F.actions_synchronized hA hB hd hfA hfB top hzero r hprefix j hj
  unfold action at he
  have hu := add_right_cancel he
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp
    (F.finite _ (F.cofactor_ne_zero hA hd hfA j))
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp
    (F.finite _ (F.cofactor_ne_zero hB hd hfB j))
  rw [← ha, ← hb, WithTop.untopD_coe, WithTop.untopD_coe] at hu
  rw [← ha, ← hb, hu]

theorem first_cofactor_valuation_split {n : ℕ}
    {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r) :
    F.valuation (F.cofactors A d r.succ) ≠ F.valuation (F.cofactors B d r.succ) := by
  intro he
  apply F.first_action_split_ne hA hB hd hfA hfB top hzero r hprefix hchanged
  simp only [action, he]

/-- Rightmost common-row minimizers march without supplied balancing or support conclusions. -/
theorem common_row_minimizers_march {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (top : ρ) (hzero : F.action A d top 0 = F.action B d top 0)
    (r : Fin n) (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r) (i j : Fin n) (hij : i < j) (hj : j < r) :
    ∃ x ∈ F.columnMinimizers A B d (A i),
      ∃ y ∈ F.columnMinimizers A B d (A j),
        (∀ a ∈ F.columnMinimizers A B d (A i), a ≤ x) ∧
        (∀ b ∈ F.columnMinimizers A B d (A j), b ≤ y) ∧ x < y := by
  have hi : i < r := hij.trans hj
  have hsi := F.common_row_support_nonempty hA hB hd hfA hfB top hzero r hprefix hchanged i hi
  have hsj := F.common_row_support_nonempty hA hB hd hfA hfB top hzero r hprefix hchanged j hj
  have hci := F.rowMinimizers_card_two A B d i (hprefix i hi) hsi
  have hcj := F.rowMinimizers_card_two A B d j (hprefix j hj) hsj
  have hnei : (F.columnMinimizers A B d (A i)).Nonempty := by
    apply Finset.card_pos.mp
    rw [F.columnMinimizers_card]
    omega
  have hnej : (F.columnMinimizers A B d (A j)).Nonempty := by
    apply Finset.card_pos.mp
    rw [F.columnMinimizers_card]
    omega
  refine ⟨_, Finset.max'_mem _ hnei, _, Finset.max'_mem _ hnej, ?_, ?_, ?_⟩
  · intro a ha
    exact Finset.le_max' _ _ ha
  · intro b hb
    exact Finset.le_max' _ _ hb
  · exact F.columnMinimizers_march A B d hd (hA hij) (hprefix i hi) (hprefix j hj) hsi hsj

/-- All four clauses of `thm:abstract-monge` for actual common-family boards. -/
theorem abstract_monge {n : ℕ} {A B : Fin n → ρ} {d : Fin (n + 1) → χ}
    (hA : StrictMono A) (hB : StrictMono B) (hd : StrictMono d)
    (hfA : F.maximalMatchingsFeasible A d) (hfB : F.maximalMatchingsFeasible B d)
    (r : Fin n) (hr : 0 < r.val)
    (hprefix : ∀ i : Fin n, i.val < r.val → A i = B i)
    (hchanged : A r ≠ B r)
    (hzero : F.action A d (A ⟨0, by omega⟩) 0 = F.action B d (A ⟨0, by omega⟩) 0) :
    ((∀ j : Fin (n + 1), j.val ≤ r.val →
        F.valuation (F.cofactors A d j) = F.valuation (F.cofactors B d j)) ∧
      F.valuation (F.cofactors A d r.succ) ≠ F.valuation (F.cofactors B d r.succ)) ∧
    (∀ i : Fin n, i < r → ∀ j : Fin (n + 1), r.val + 1 < j.val →
      F.tiltedDefectValue A B d (A i) r.succ < F.tiltedDefectValue A B d (A i) j) ∧
    ((∀ i : Fin n, i < r → 2 ≤ (F.rowMinimizers A B d (A i)).card) ∧
      (∀ i j : Fin n, i < j → j < r →
        ∀ x ∈ F.columnMinimizers A B d (A i),
          ∀ y ∈ F.columnMinimizers A B d (A j), x ≤ y) ∧
      (∀ i j : Fin n, i < j → j < r →
        ∃ x ∈ F.columnMinimizers A B d (A i),
          ∃ y ∈ F.columnMinimizers A B d (A j),
            (∀ a ∈ F.columnMinimizers A B d (A i), a ≤ x) ∧
            (∀ b ∈ F.columnMinimizers A B d (A j), b ≤ y) ∧ x < y)) ∧
    (F.positiveFloor A B d (A ⟨0, by omega⟩) <
        F.tiltedDefectValue A B d (A ⟨0, by omega⟩) 0 →
      ∀ i : Fin r.val, F.columnMinimizers A B d (A (commonPrefixRow r i)) =
        {i.val + 1, i.val + 2}) := by
  let top := A (⟨0, by omega⟩ : Fin n)
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    exact F.cofactor_valuations_synchronized hA hB hd hfA hfB top hzero r hprefix j hj
  · exact F.first_cofactor_valuation_split hA hB hd hfA hfB top hzero r hprefix hchanged
  · intro i hi j hj
    exact F.no_backflow hA hB hd hfA hfB top hzero r hprefix hchanged i hi j hj
  · intro i hi
    exact F.rowMinimizers_card_two A B d i (hprefix i hi)
      (F.common_row_support_nonempty hA hB hd hfA hfB top hzero r hprefix hchanged i hi)
  · intro i j hij hj
    exact F.columnMinimizers_interlace A B d hd (hA hij)
  · intro i j hij hj
    exact F.common_row_minimizers_march hA hB hd hfA hfB top hzero r hprefix hchanged i j hij hj
  · intro hfloor
    exact F.strict_floor_adjacent_chain hA hB hd hfA hfB r hr hprefix hchanged hzero hfloor

end ValuedMongeFamily
end SkewSchurReconstruction
