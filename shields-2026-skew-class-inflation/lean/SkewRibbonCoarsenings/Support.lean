/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/Support.lean
import SkewRibbonCoarsenings.ColorGraphs
import SkewRibbonCoarsenings.Setting

/-!
# Support separation

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:balance`, subsection
`subsec:support` (`thm:support`, `rem:positive-equilibrium`).

* `positive_equilibrium` is `rem:positive-equilibrium`: for disjoint-support skew-ternary
  matrices `U, V` on a finite set with at least two vertices satisfying `eq:matrix-triangle`, if
  `A = U + V` has a strictly positive real null vector, the support graphs of `U` and `V` cannot
  both be connected.
* `supportSeparation` is `thm:support`, in the form `SupportSeparation` of `Setting.lean`.  Its
  proof builds the cyclic matrices `U_{ij} = u(j - i)`, `V_{ij} = v(j - i)`, checks
  `eq:matrix-triangle` from `eq:FE`, identifies "support generates the cyclic group" with
  connectivity of the Cayley color graph (`cyclic_connected`), and applies
  `positive_equilibrium` with `π ≡ 1`.

Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

section Equilibrium

variable {X : Type*} [Fintype X]

/-- `rem:positive-equilibrium`, displayed computation: a constant cut of a skew-symmetric matrix
with a strictly positive real null vector `π` has value zero, because
`0 = ∑_{i ∈ P} π_i (A π)_i = c (∑_{i ∈ P} π_i) (∑_{j ∈ Q} π_j)`. -/
theorem const_cut_value_zero {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) (π : X → ℝ)
    (hπ : ∀ i, 0 < π i) (hnull : ∀ i, ∑ j, (A i j : ℝ) * π j = 0) {P : X → Prop} {c : ℤ}
    (hP : IsCutOf (fun p q => A p q = c) univ P) : c = 0 := by
  classical
  obtain ⟨⟨p0, -, hPp0⟩, ⟨q0, -, hPq0⟩, hcross⟩ := hP
  set Pf : Finset X := univ.filter P with hPf
  set Qf : Finset X := univ.filter fun x => ¬P x with hQf
  -- the weighted sum over rows in `P`
  have h1 : ∑ i ∈ Pf, π i * ∑ j, (A i j : ℝ) * π j = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hnull i, mul_zero]
  have hsplit : ∀ i, ∑ j, (A i j : ℝ) * π j =
      ∑ j ∈ Pf, (A i j : ℝ) * π j + ∑ j ∈ Qf, (A i j : ℝ) * π j := fun i =>
    (Finset.sum_filter_add_sum_filter_not univ P _).symm
  -- the internal part vanishes by skew-symmetry
  have hint : ∑ i ∈ Pf, π i * ∑ j ∈ Pf, (A i j : ℝ) * π j = 0 := by
    have hneg : ∑ i ∈ Pf, π i * ∑ j ∈ Pf, (A i j : ℝ) * π j =
        -∑ i ∈ Pf, π i * ∑ j ∈ Pf, (A i j : ℝ) * π j := by
      conv_lhs => rw [show (∑ i ∈ Pf, π i * ∑ j ∈ Pf, (A i j : ℝ) * π j) =
          ∑ i ∈ Pf, ∑ j ∈ Pf, π i * ((A i j : ℝ) * π j) by
        simp only [Finset.mul_sum]]
      rw [Finset.sum_comm]
      rw [show (∑ i ∈ Pf, π i * ∑ j ∈ Pf, (A i j : ℝ) * π j) =
          ∑ i ∈ Pf, ∑ j ∈ Pf, π i * ((A i j : ℝ) * π j) by simp only [Finset.mul_sum],
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hA i j
      have h' : (A j i : ℝ) = -(A i j : ℝ) := by exact_mod_cast this
      rw [h']
      ring
    linarith
  have hcr : ∑ i ∈ Pf, π i * ∑ j ∈ Qf, (A i j : ℝ) * π j =
      (c : ℝ) * ((∑ i ∈ Pf, π i) * ∑ j ∈ Qf, π j) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiP : P i := (Finset.mem_filter.1 hi).2
    have hin : ∑ j ∈ Qf, (A i j : ℝ) * π j = ∑ j ∈ Qf, (c : ℝ) * π j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjQ : ¬P j := (Finset.mem_filter.1 hj).2
      have := hcross i (mem_univ i) j (mem_univ j) hiP hjQ
      rw [this]
    rw [hin, ← Finset.mul_sum]
    ring
  have hsumP : 0 < ∑ i ∈ Pf, π i :=
    Finset.sum_pos (fun i _ => hπ i) ⟨p0, by simp [hPf, hPp0]⟩
  have hsumQ : 0 < ∑ j ∈ Qf, π j :=
    Finset.sum_pos (fun i _ => hπ i) ⟨q0, by simp [hQf, hPq0]⟩
  have htot : (c : ℝ) * ((∑ i ∈ Pf, π i) * ∑ j ∈ Qf, π j) = 0 := by
    rw [← hcr]
    have := h1
    simp only [hsplit, mul_add, Finset.sum_add_distrib] at this
    linarith
  have hprod : 0 < (∑ i ∈ Pf, π i) * ∑ j ∈ Qf, π j := mul_pos hsumP hsumQ
  have : (c : ℝ) = 0 := by
    rcases mul_eq_zero.1 htot with h | h
    · exact h
    · exact absurd h hprod.ne'
  exact_mod_cast this

/-- `rem:positive-equilibrium`: let `U, V` be disjoint-support skew-ternary matrices on a finite
set `X` with at least two vertices satisfying `eq:matrix-triangle`.  If `A = U + V` has a
strictly positive real null vector `π`, then the support graphs of `U` and `V` cannot both be
connected: at least one of them is disconnected. -/
theorem positive_equilibrium {U V : X → X → ℤ} (h : IsColorPair U V)
    (hcard : 2 ≤ Fintype.card X) (π : X → ℝ) (hπ : ∀ i, 0 < π i)
    (hnull : ∀ i, ∑ j, ((U i j + V i j : ℤ) : ℝ) * π j = 0) :
    SuppDisconnected U univ ∨ SuppDisconnected V univ := by
  classical
  have hAs : ∀ x y, (U y x + V y x) = -(U x y + V x y) := fun x y => by
    have := h.hU.skew x y
    have := h.hV.skew x y
    omega
  by_cases hcut : ∃ P : X → Prop, IsConstCut (fun x y => U x y + V x y) univ P
  · obtain ⟨P, c, hP⟩ := hcut
    have hc := const_cut_value_zero hAs π hπ hnull hP
    subst hc
    left
    refine ⟨P, hP.mono fun p q hpq => ?_⟩
    have hd := h.disj p q
    have hs := h.hU.ternary p q
    have ht := h.hV.ternary p q
    have h0 : U p q + V p q = 0 := hpq
    rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht <;> rw [hs, ht] at hd <;> omega
  · exact color_disconnected_univ h ⟨by simpa using hcard, hcut⟩

end Equilibrium

section Cyclic

variable {n : ℕ} [NeZero n]

/-- Disconnected support graph of the cyclic matrix `U_{ij} = u(j - i)` forces the support of
`u` to generate a proper subgroup: if `supportGcd u = 1`, the Cayley color graph is connected. -/
theorem cyclic_connected {u : ZMod n → ℤ} (hu : IsOdd u) (hg : supportGcd u = 1) :
    ¬SuppDisconnected (fun i j : ZMod n => u (j - i)) Finset.univ := by
  classical
  rintro hd
  obtain ⟨K, ⟨-, hcl⟩, ⟨i0, hi0⟩, hne⟩ := (suppDisconnected_iff _ _).1 hd
  -- `K` is a union of cosets of the subgroup `D` of translations preserving it
  let D : AddSubgroup ℤ :=
    { carrier := {m | ∀ i : ZMod n, i ∈ K ↔ i + (m : ZMod n) ∈ K}
      zero_mem' := fun i => by simp
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [ha i, hb (i + (a : ZMod n)), Int.cast_add, add_assoc]
      neg_mem' := fun {a} ha i => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have := ha (i + ((-a : ℤ) : ZMod n))
        rw [Int.cast_neg] at this ⊢
        rw [show i + -(a : ZMod n) + (a : ZMod n) = i by ring] at this
        exact this.symm }
  have hmem : ∀ k : ℕ, u (k : ZMod n) ≠ 0 → (k : ℤ) ∈ D := by
    intro k hk i
    simp only [Int.cast_natCast]
    constructor
    · intro hiK
      by_contra hno
      have := hcl i hiK (i + (k : ZMod n)) (mem_univ _) hno
      simp only [add_sub_cancel_left] at this
      exact hk this
    · intro hiK
      by_contra hno
      have := hcl (i + (k : ZMod n)) hiK i (mem_univ _) hno
      have e : i - (i + (k : ZMod n)) = -(k : ZMod n) := by ring
      change u (i - (i + (k : ZMod n))) = 0 at this
      rw [e] at this
      have hneg := hu (k : ZMod n)
      rw [hneg] at this
      exact hk (by omega)
  have hn : (n : ℤ) ∈ D := by
    intro i
    simp
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic D
  have haD : a ∈ D := by
    rw [ha]
    exact AddSubgroup.subset_closure rfl
  have hdvd : ∀ m ∈ D, a ∣ m := by
    intro m hm
    rw [ha, ← AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_zmultiples_iff] at hm
    obtain ⟨k, rfl⟩ := hm
    exact ⟨k, by simp [mul_comm]⟩
  have hna : a.natAbs ∣ n := by
    have := hdvd _ hn
    exact Int.natAbs_dvd_natAbs.2 this
  have hsupp : ∀ k ∈ (Finset.range n).filter (fun k : ℕ => u (k : ZMod n) ≠ 0),
      a.natAbs ∣ id k := by
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    have := hdvd _ (hmem k hk')
    exact Int.natAbs_dvd_natAbs.2 this
  have hdg : a.natAbs ∣ supportGcd u := by
    unfold supportGcd
    exact Nat.dvd_gcd hna (Finset.dvd_gcd hsupp)
  rw [hg] at hdg
  have ha1 : a.natAbs = 1 := Nat.dvd_one.1 hdg
  have h1D : (1 : ℤ) ∈ D := by
    have hcases : a = 1 ∨ a = -1 := by omega
    rcases hcases with h | h
    · rwa [h] at haD
    · have := D.neg_mem haD
      rw [h] at this
      simpa using this
  have hshift : ∀ i : ZMod n, i ∈ K ↔ i + 1 ∈ K := by
    intro i
    have := h1D i
    simpa using this
  have hall : ∀ m : ℕ, i0 + (m : ZMod n) ∈ K := by
    intro m
    induction m with
    | zero => simpa using hi0
    | succ m ih =>
      have := (hshift _).1 ih
      simpa [Nat.cast_succ, add_assoc] using this
  apply hne
  ext x
  simp only [Finset.mem_univ, iff_true]
  have := hall (x - i0).val
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this

end Cyclic

/-- The matrix triangle identity of `eq:matrix-triangle` for the cyclic matrices
`U_{ij} = u(j - i)`, `V_{ij} = v(j - i)` is exactly `eq:FE` (together with oddness). -/
theorem cyclic_matrixTriangle {n : ℕ} {u v : ZMod n → ℤ} (hu : IsOdd u) (hv : IsOdd v)
    (hfe : FEq u v) :
    MatrixTriangle (fun i j : ZMod n => u (j - i)) (fun i j : ZMod n => v (j - i)) := by
  intro i j k
  unfold triSum
  have h := hfe (j - i) (k - j)
  have e1 : (j - i) + (k - j) = -(i - k) := by ring
  rw [e1, hu, hv] at h
  have e2 : k - i = -(i - k) := by ring
  have hu' := hu (i - k)
  have hv' := hv (i - k)
  simp only [e2, hu, hv] at *
  linear_combination h

/-- `thm:support`: nonzero odd `u, v : ℤ/n → {-1, 0, 1}` with `u v = 0` satisfying `eq:FE`
have a support generating a proper subgroup of `ℤ/n` (`supportGcd ≠ 1`).  The proof is
the paper's: cyclic matrices, `eq:FE` as `eq:matrix-triangle`, zero row sums by oddness, and
`rem:positive-equilibrium` with `π ≡ 1` (which packages the zero-cut-value argument and
`lem:color`). -/
theorem supportSeparation : SupportSeparation := by
  intro n u v hn hu hv _ _ huo hvo huv hfe
  by_contra hcon
  push Not at hcon
  obtain ⟨hgu, hgv⟩ := hcon
  have : NeZero n := ⟨by omega⟩
  let U : ZMod n → ZMod n → ℤ := fun i j => u (j - i)
  let V : ZMod n → ZMod n → ℤ := fun i j => v (j - i)
  have hpair : IsColorPair U V :=
    { hU :=
        { skew := fun x y => by
            have := huo (y - x)
            have e : x - y = -(y - x) := by ring
            simp only [U, e, this]
          ternary := fun x y => hu (y - x) |> fun h => by simpa [U] using h }
      hV :=
        { skew := fun x y => by
            have := hvo (y - x)
            have e : x - y = -(y - x) := by ring
            simp only [V, e, this]
          ternary := fun x y => hv (y - x) |> fun h => by simpa [V] using h }
      disj := fun x y => huv (y - x)
      tri := cyclic_matrixTriangle huo hvo hfe }
  have hrow : ∀ f : ZMod n → ℤ, IsOdd f → ∀ i : ZMod n, ∑ j : ZMod n, f (j - i) = 0 := by
    intro f hf i
    have h1 : ∑ j : ZMod n, f (j - i) = ∑ j : ZMod n, f j :=
      Equiv.sum_comp (Equiv.subRight i) f
    have h2 : ∑ j : ZMod n, f j = ∑ j : ZMod n, f (-j) := (Equiv.sum_comp (Equiv.neg _) f).symm
    have h3 : ∑ j : ZMod n, f (-j) = -∑ j : ZMod n, f j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => hf j
    omega
  have hnull : ∀ i, ∑ j, (((U i j + V i j : ℤ)) : ℝ) * (fun _ : ZMod n => (1 : ℝ)) j = 0 := by
    intro i
    simp only [mul_one]
    have : ∑ j : ZMod n, (U i j + V i j) = 0 := by
      rw [Finset.sum_add_distrib]
      have h1 := hrow u huo i
      have h2 := hrow v hvo i
      simp only [U, V]
      omega
    exact_mod_cast this
  have hcard : 2 ≤ Fintype.card (ZMod n) := by
    rw [ZMod.card]
    exact hn
  rcases positive_equilibrium hpair hcard (fun _ => (1 : ℝ)) (fun _ => one_pos) hnull with h | h
  · exact cyclic_connected huo hgu h
  · exact cyclic_connected hvo hgv h

end SkewRibbonCoarsenings
